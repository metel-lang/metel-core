//! Declaration clauses become the marker impls they stand for (RFC-0207, metel-core#1928).
//!
//! `struct T: A derives B` is `struct T` with `extend T: A;` and `extend T: B;`, so the later stages see an
//! `extend` and a clause for the same aspect as the overlap they are (`T0015`). This runs after name
//! resolution because it has to read the aspect declarations:
//! - the `copy` class keyword names the aspect with the `implicit` property, and also stands for the entries of
//!   the super-aspects that aspect marks `derived` (`copy struct P` is `derives Clone, Copy`, RFC-0234);
//! - `derives A` requires an entry of its own for every positive super-aspect `A` marks `derived`
//!   (`Copy requires derived Clone`, RFC-0213 section 4, RFC-0234): nothing is generated, a missing entry is an error;
//! - an entry may carry arguments, the flow of a field-wise derivation (RFC-0227);
//! - the host `clone` body belongs to the std `Clone` aspect, whose derivation is native.
//!
//! A generic type's impl is generic over the same parameters, and a `derives` impl bounds each parameter a
//! field holds by value by the derived aspect, so `copy struct W<T>` is `Copy` exactly when `T` is.

use std::collections::HashMap;

mod flows;
use flows::{Aspects, Kind, Scope, Table};

use crate::data::ast::{
    AspectProperty, Block, Bound, BoundHead, ClauseEntry, Decl, FunDecl, GenericParam, ImplBlock,
    NameSpan, NativeBinding, Param, Polarity, ReceiverKind, Span, TypeExpr, Visibility,
};
use crate::data::error::{MetelError, TypeErrorCode};
use crate::identity::symbols::{Namespace, SymbolId};
use crate::pipeline::name_resolution::name_resolver::ResolvedNames;
use crate::pipeline::parsing::module_loader::ModuleGraph;

/// What an entry needs to know about the aspect it names.
struct Aspect {
    name: String,
    module: Vec<String>,
    implicit: bool,
    /// Positive `derived` supers, as written in the declaring module.
    derived: Vec<String>,
}

/// Resolve names, then write the impls of the declaration clauses: the one step every pipeline entry point
/// runs between loading and identity allocation.
///
/// # Errors
/// A name-resolution error, or `T0003` from [`expand`].
pub fn resolve_and_expand(
    graph: &mut ModuleGraph,
) -> Result<std::rc::Rc<ResolvedNames>, MetelError> {
    let names = crate::pipeline::name_resolution::name_resolver::resolve(graph)?;
    expand(graph, &names)?;
    Ok(names)
}

/// Write the impls of every struct, enum and record declaration's clauses, in place.
///
/// # Errors
/// `T0003` when the `copy` class keyword is used and no aspect has the `implicit` property.
pub fn expand(graph: &mut ModuleGraph, names: &ResolvedNames) -> Result<(), MetelError> {
    let mut aspects: HashMap<SymbolId, Aspect> = HashMap::new();
    for module in &graph.modules {
        for decl in &module.program.decls {
            if let Decl::Aspect(ad) = decl
                && let Some(id) = names.symbols.get(&(
                    module.module_path.clone(),
                    Namespace::Type,
                    ad.name.clone(),
                ))
            {
                aspects.insert(
                    *id,
                    Aspect {
                        name: ad.name.clone(),
                        module: module.module_path.clone(),
                        implicit: ad
                            .properties
                            .iter()
                            .any(|(p, _)| *p == AspectProperty::Implicit),
                        derived: ad
                            .supers
                            .iter()
                            .filter(|s| s.derived && !s.negative)
                            .map(|s| s.name.clone())
                            .collect(),
                    },
                );
            }
        }
    }
    let clone_id = names
        .symbols
        .get(&(
            vec!["std".to_string(), "core".to_string()],
            Namespace::Type,
            "Clone".to_string(),
        ))
        .copied();
    let flow_aspects = Aspects {
        // The language's own `implicit` aspect, declared in `std::core`. A user aspect that writes the property is
        // rejected later (T0045); until then it must not be mistaken for `Copy`, whatever order the table iterates in.
        implicit: aspects
            .iter()
            .find(|(_, a)| a.implicit && a.module == ["std".to_string(), "core".to_string()])
            .map(|(id, _)| *id),
        clone: clone_id,
    };
    let module_flows = flows::module_table(graph, names, &flow_aspects);
    let ctx = Ctx {
        names,
        aspects: &aspects,
        clone_id,
        flow_aspects,
    };
    for module in &mut graph.modules {
        let path = module.module_path.clone();
        expand_decls(
            &mut module.program.decls,
            &path,
            &ctx,
            &[&module_flows],
            true,
        )?;
    }
    Ok(())
}

struct Ctx<'a> {
    names: &'a ResolvedNames,
    aspects: &'a HashMap<SymbolId, Aspect>,
    clone_id: Option<SymbolId>,
    /// How the clause entries name the two aspects whose derivation has a flow (RFC-0224).
    flow_aspects: Aspects,
}

/// Expand a declaration list, and the declaration lists of the function bodies inside it.
///
/// `outer` holds the flow tables of the enclosing scopes, the module's first; a function body adds a table
/// of its own local type declarations (`top` is the module's own list, which the module table covers).
fn expand_decls(
    decls: &mut Vec<Decl>,
    module: &[String],
    ctx: &Ctx<'_>,
    outer: &[&Table],
    top: bool,
) -> Result<(), MetelError> {
    let local;
    let mut tables: Vec<&Table> = outer.to_vec();
    if !top {
        local = flows::local_table(decls, module, outer, ctx.names, &ctx.flow_aspects);
        tables.push(&local);
    }
    let scope = Scope::new(&tables);
    let mut out: Vec<Decl> = Vec::with_capacity(decls.len());
    for mut decl in std::mem::take(decls) {
        match &mut decl {
            Decl::Fun(fun) => expand_decls(&mut fun.body.stmts, module, ctx, &tables, false)?,
            Decl::Impl(block) => {
                for method in &mut block.methods {
                    expand_decls(&mut method.body.stmts, module, ctx, &tables, false)?;
                }
            }
            _ => {}
        }
        let impls = match &mut decl {
            Decl::Struct(sd) => {
                let fields: Vec<TypeExpr> = sd.fields.iter().map(|f| f.type_ann.clone()).collect();
                clause_impls(
                    &Declaration {
                        name: &sd.name,
                        generics: &sd.generics,
                        fields: &fields,
                        span: &sd.span,
                        public: sd.visibility == Visibility::Public,
                    },
                    &mut sd.clauses,
                    module,
                    ctx,
                    &scope,
                )?
            }
            Decl::Enum(ed) => {
                let fields: Vec<TypeExpr> = ed
                    .variants
                    .iter()
                    .flat_map(|v| v.fields.iter().map(|f| f.type_ann.clone()))
                    .collect();
                clause_impls(
                    &Declaration {
                        name: &ed.name,
                        generics: &ed.generics,
                        fields: &fields,
                        span: &ed.span,
                        public: ed.visibility == Visibility::Public,
                    },
                    &mut ed.clauses,
                    module,
                    ctx,
                    &scope,
                )?
            }
            _ => Vec::new(),
        };
        out.push(decl);
        out.extend(impls.into_iter().map(Decl::Impl));
    }
    check_no_negative_copy(&out, module, ctx)?;
    *decls = out;
    Ok(())
}

/// RFC-0224 rule 8: a type that derives `Copy` is `Copy` exactly by its flow, so a negative grant of `Copy`
/// for it (`extend<T: Marker> Token<T>: !Copy;`) is an error at the grant. (A `Drop` impl is rejected by
/// the `Copy: !Drop` exclusion, `T0015`.)
fn check_no_negative_copy(
    decls: &[Decl],
    module: &[String],
    ctx: &Ctx<'_>,
) -> Result<(), MetelError> {
    let Some(implicit) = ctx
        .aspects
        .iter()
        .find(|(_, a)| a.implicit)
        .map(|(id, _)| *id)
    else {
        return Ok(());
    };
    let is_copy = |block: &ImplBlock| {
        block.aspect_name.as_deref().is_some_and(|name| {
            super::coherence::resolve_id(ctx.names, module, name) == Some(implicit)
        })
    };
    let target_name = |block: &ImplBlock| match &block.target_type {
        TypeExpr::Named(name, ..) => Some(name.clone()),
        _ => None,
    };
    let derived: std::collections::HashSet<String> = decls
        .iter()
        .filter_map(|d| match d {
            Decl::Impl(b) if b.from_clause && b.polarity == Polarity::Positive && is_copy(b) => {
                target_name(b)
            }
            _ => None,
        })
        .collect();
    for decl in decls {
        if let Decl::Impl(block) = decl
            && !block.from_clause
            && block.polarity == Polarity::Negative
            && is_copy(block)
            && let Some(name) = target_name(block)
            && derived.contains(&name)
        {
            return Err(MetelError::type_error(
                TypeErrorCode::T0015,
                format!(
                    "`{name}` derives `Copy`, so it is `Copy` exactly by its flow: a negative grant `extend {name}: !Copy` is an error (RFC-0224 rule 8)"
                ),
                &block.span,
            ));
        }
    }
    Ok(())
}

/// The declaration whose clauses are expanded.
struct Declaration<'a> {
    name: &'a str,
    generics: &'a [GenericParam],
    fields: &'a [TypeExpr],
    span: &'a Span,
    public: bool,
}

/// The positive `derived` super-aspects of an aspect, transitively: the aspects a type that derives it must also
/// derive (RFC-0234). Each is named as written in the declaring module and resolved there.
fn derived_supers(id: SymbolId, ctx: &Ctx<'_>) -> Vec<(String, SymbolId)> {
    let mut out: Vec<(String, SymbolId)> = Vec::new();
    let mut stack = vec![id];
    while let Some(next) = stack.pop() {
        let Some(aspect) = ctx.aspects.get(&next) else {
            continue;
        };
        for sup in &aspect.derived {
            if let Some(sup_id) = super::coherence::resolve_id(ctx.names, &aspect.module, sup)
                && sup_id != id
                && !out.iter().any(|(_, seen)| *seen == sup_id)
            {
                out.push((sup.clone(), sup_id));
                stack.push(sup_id);
            }
        }
    }
    out
}

/// The `copy` class keyword names the aspect with the `implicit` property, and stands for the entries of the
/// super-aspects that aspect marks `derived` (`copy struct P` is `derives Clone, Copy`, RFC-0234), unless the
/// clause writes them itself.
fn name_class_keywords(
    clauses: &mut crate::data::ast::DeclClauses,
    module: &[String],
    ctx: &Ctx<'_>,
) -> Result<(), MetelError> {
    let mut added: Vec<ClauseEntry> = Vec::new();
    for entry in &mut clauses.derives {
        if entry.from_class_keyword && entry.name.is_empty() {
            let implicit = ctx
                .flow_aspects
                .implicit
                .and_then(|id| ctx.aspects.get(&id).map(|a| (id, a)))
                .or_else(|| ctx.aspects.iter().find(|(_, a)| a.implicit).map(|(id, a)| (*id, a)))
                .ok_or_else(|| {
                    MetelError::type_error(
                        TypeErrorCode::T0003,
                        "the `copy` class keyword needs an aspect with the `implicit` property, and the program has none".to_string(),
                        &entry.span,
                    )
                })?;
            entry.name = implicit.1.name.clone();
            for (sup, sup_id) in derived_supers(implicit.0, ctx) {
                // The super as the declaring module wrote it must name the same aspect here.
                if super::coherence::resolve_id(ctx.names, module, &sup) == Some(sup_id) {
                    added.push(ClauseEntry {
                        name: sup,
                        from_class_keyword: true,
                        flow: None,
                        span: entry.span.clone(),
                    });
                }
            }
        }
    }
    for entry in added {
        let present = clauses.derives.iter().any(|e| {
            super::coherence::resolve_id(ctx.names, module, &e.name)
                == super::coherence::resolve_id(ctx.names, module, &entry.name)
        });
        if !present {
            clauses.derives.push(entry);
        }
    }
    Ok(())
}

/// RFC-0234: `derives A` requires an entry of its own for every super-aspect `A` marks `derived`. Nothing is
/// generated; a missing entry is an error that names the entry to add.
fn check_derived_obligations(
    clauses: &crate::data::ast::DeclClauses,
    module: &[String],
    ctx: &Ctx<'_>,
) -> Result<(), MetelError> {
    for entry in &clauses.derives {
        let Some(id) = super::coherence::resolve_id(ctx.names, module, &entry.name) else {
            continue;
        };
        for (sup, sup_id) in derived_supers(id, ctx) {
            let present = clauses
                .derives
                .iter()
                .any(|e| super::coherence::resolve_id(ctx.names, module, &e.name) == Some(sup_id));
            if !present {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0046,
                    format!(
                        "`{}` requires a derived `{sup}`: add `{sup}` to the `derives` clause (RFC-0234); a written `extend T: {sup}` does not satisfy it",
                        entry.name
                    ),
                    &entry.span,
                ));
            }
        }
    }
    Ok(())
}

/// Each entry with the aspect that bounds a generic type's parameters: a `derives` entry is bounded by itself,
/// a colon-list marker by nothing.
fn clause_entries(clauses: &crate::data::ast::DeclClauses) -> Vec<(ClauseEntry, Option<String>)> {
    let mut entries: Vec<(ClauseEntry, Option<String>)> = Vec::new();
    for entry in &clauses.colon {
        entries.push((entry.clone(), None));
    }
    for entry in &clauses.derives {
        entries.push((entry.clone(), Some(entry.name.clone())));
    }
    entries
}

/// Which field-wise derivation an entry is, for the flow (RFC-0224, RFC-0227): `Copy` (the aspect with the
/// `implicit` property) or `Clone`; any other entry has no flow.
fn entry_kind(entry: &ClauseEntry, module: &[String], ctx: &Ctx<'_>) -> Option<Kind> {
    let resolves = |id: Option<SymbolId>| {
        id.is_some() && super::coherence::resolve_id(ctx.names, module, &entry.name) == id
    };
    if resolves(ctx.flow_aspects.implicit) {
        Some(Kind::Copy)
    } else if resolves(ctx.clone_id) {
        Some(Kind::Clone)
    } else {
        None
    }
}

fn clause_impls(
    decl: &Declaration<'_>,
    clauses: &mut crate::data::ast::DeclClauses,
    module: &[String],
    ctx: &Ctx<'_>,
    scope: &Scope<'_>,
) -> Result<Vec<ImplBlock>, MetelError> {
    if clauses.is_empty() {
        return Ok(Vec::new());
    }
    name_class_keywords(clauses, module, ctx)?;
    check_derived_obligations(clauses, module, ctx)?;
    let args: Vec<TypeExpr> = decl
        .generics
        .iter()
        .map(|g| TypeExpr::Named(g.name.clone(), Vec::new(), NameSpan(decl.span.clone())))
        .collect();
    let target = TypeExpr::Named(decl.name.to_string(), args, NameSpan(decl.span.clone()));
    let entries = clause_entries(clauses);
    let mut seen = std::collections::HashSet::new();
    let mut impls = Vec::new();
    let mut flows: Vec<(Kind, Vec<String>, Span)> = Vec::new();
    // Derivation is idempotent per type and aspect: `copy struct T derives Clone, Copy` derives it once.
    for (entry, bound) in entries
        .iter()
        .filter(|(entry, _)| seen.insert(entry.name.clone()))
    {
        let kind = entry_kind(entry, module, ctx);
        if bound.is_some() {
            check_flow(entry, kind, decl.generics, decl.fields, module, ctx, scope)?;
            // The `Clone` entry a class keyword stands for has no argument list to write, so the type's `Copy`
            // entry is the one that must state the flow.
            let implied = entry.from_class_keyword && kind == Some(Kind::Clone);
            if let Some(kind) = kind
                && decl.public
                && entry.flow.is_none()
                && !implied
            {
                check_public_flow_stated(decl, entry, kind, module, ctx, scope)?;
            }
        }
        let flow = if bound.is_some() {
            entry_flow(entry, kind, decl.name, module, ctx, scope)
        } else {
            None
        };
        if let (Some(kind), Some(flow)) = (kind, &flow) {
            flows.push((kind, flow.clone(), entry.span.clone()));
        }
        impls.push(ImplBlock {
            polarity: Polarity::Positive,
            generics: impl_generics(
                decl.generics,
                entry,
                bound.as_deref(),
                decl.fields,
                flow.as_deref(),
            ),
            aspect_name: Some(entry.name.clone()),
            aspect_type_args: Vec::new(),
            target_type: target.clone(),
            where_clause: None,
            assoc_type_defs: Vec::new(),
            methods: derived_methods(entry, &target, module, ctx),
            from_clause: true,
            span: entry.span.clone(),
        });
    }
    check_clone_flow_within_copy(&flows)?;
    Ok(impls)
}

/// RFC-0234 section 2: a type that derives `Copy` is `Clone` wherever it is `Copy`, so the `Clone` flow must be
/// contained in the `Copy` flow. A parameter only `Clone` depends on is an error at the `Copy` entry.
fn check_clone_flow_within_copy(flows: &[(Kind, Vec<String>, Span)]) -> Result<(), MetelError> {
    let copy = flows.iter().find(|(kind, ..)| *kind == Kind::Copy);
    let clone = flows.iter().find(|(kind, ..)| *kind == Kind::Clone);
    if let (Some((_, copy_flow, copy_span)), Some((_, clone_flow, _))) = (copy, clone)
        && let Some(extra) = clone_flow.iter().find(|p| !copy_flow.contains(p))
    {
        return Err(MetelError::type_error(
            TypeErrorCode::T0046,
            format!(
                "the `Clone` of this type depends on `{extra}`, which its `Copy` flow does not cover: a type is `Clone` wherever it is `Copy`, so state `Copy` with `{extra}` or narrow the `Clone` flow (RFC-0234)"
            ),
            copy_span,
        ));
    }
    Ok(())
}

/// The flow an entry's impl is generated with (RFC-0224, RFC-0227): the argument list the entry states, or the
/// flow the compiler computes from the fields for a `Copy` or `Clone` entry; any other entry has none (its
/// parameters are bounded by the per-parameter rule).
fn entry_flow(
    entry: &ClauseEntry,
    kind: Option<Kind>,
    type_name: &str,
    module: &[String],
    ctx: &Ctx<'_>,
    scope: &Scope<'_>,
) -> Option<Vec<String>> {
    let kind = kind?;
    if let Some(stated) = &entry.flow {
        return Some(stated.iter().map(|p| p.name.clone()).collect());
    }
    scope
        .own(type_name, module, ctx.names, kind)
        .map(|e| e.set().iter().cloned().collect())
}

/// The spelling of a flow argument list, for the fix-its.
fn flow_args(set: &[&str]) -> String {
    set.join(", ")
}

/// RFC-0224 section 2 rule 3, widened to every field-wise derivation by RFC-0227: a `pub` generic type that
/// derives `Copy` or `Clone` without an argument list has a computed flow, which is its published interface, so
/// it may omit the list only when that flow is empty. Otherwise the error shows the computed set as the fix-it.
/// Non-`pub` and non-generic types are unaffected.
fn check_public_flow_stated(
    decl: &Declaration<'_>,
    entry: &ClauseEntry,
    kind: Kind,
    module: &[String],
    ctx: &Ctx<'_>,
    scope: &Scope<'_>,
) -> Result<(), MetelError> {
    let Some(computed) = scope.own(decl.name, module, ctx.names, kind) else {
        return Ok(());
    };
    let set: Vec<&str> = computed.set().iter().map(String::as_str).collect();
    if set.is_empty() {
        return Ok(());
    }
    let aspect = entry.name.as_str();
    let message = if entry.from_class_keyword {
        format!(
            "a public generic type must state the flow of its `{aspect}` when it is not empty, and `copy` states none; write `derives Clone({0}), Copy({0})` (RFC-0227)",
            flow_args(&set)
        )
    } else {
        format!(
            "a public generic type must state the flow of its `{aspect}` when it is not empty; write `derives {aspect}({})` (RFC-0227)",
            flow_args(&set)
        )
    };
    Err(MetelError::type_error(
        TypeErrorCode::T0046,
        message,
        &entry.span,
    ))
}

/// RFC-0224 section 2 and RFC-0227: the checks on a `derives` entry's arguments, stated or computed. An argument
/// list is accepted on a field-wise derivation (`Copy`, `Clone`) only, names only type parameters of the
/// declaration, and must contain every parameter a field's derivation depends on (it may contain more). A
/// `Copy` declaration with a field that depends on a row- or record-kinded parameter is rejected (rule 7).
/// Rule 6, a field that depends on an associated type, needs no check yet: a struct or enum field `T::Item` is
/// rejected as an unknown type before this runs.
fn check_flow(
    entry: &ClauseEntry,
    kind: Option<Kind>,
    generics: &[GenericParam],
    field_types: &[TypeExpr],
    module: &[String],
    ctx: &Ctx<'_>,
    scope: &Scope<'_>,
) -> Result<(), MetelError> {
    let invalid =
        |message: String, span: &Span| MetelError::type_error(TypeErrorCode::T0046, message, span);
    if let Some(flow) = &entry.flow {
        let Some(_) = kind else {
            return Err(invalid(
                format!(
                    "`{}` takes no arguments: only the field-wise derivations `Copy` and `Clone` state a flow (RFC-0227)",
                    entry.name
                ),
                &entry.span,
            ));
        };
        for param in flow {
            let declared = generics.iter().find(|g| g.name == param.name);
            match declared {
                None => {
                    return Err(invalid(
                        format!(
                            "`{}` names no type parameter of this declaration",
                            param.name
                        ),
                        &param.span,
                    ));
                }
                Some(g) if g.is_record || g.is_row => {
                    return Err(invalid(
                        format!(
                            "`{}` is a row- or record-kinded parameter; a flow lists type parameters only (RFC-0224 rule 7)",
                            param.name
                        ),
                        &param.span,
                    ));
                }
                Some(_) => {}
            }
        }
    }
    let Some(kind) = kind else {
        return Ok(());
    };
    if kind == Kind::Copy {
        for g in generics.iter().filter(|g| g.is_record || g.is_row) {
            if field_types.iter().any(|ty| mentions_owned(ty, &g.name)) {
                return Err(invalid(
                    format!(
                        "a `Copy` declaration cannot have a field that depends on the row- or record-kinded parameter `{}` (RFC-0224 rule 7)",
                        g.name
                    ),
                    &entry.span,
                ));
            }
        }
    }
    if let Some(flow) = &entry.flow {
        let aspect = entry.name.as_str();
        let params: Vec<String> = generics
            .iter()
            .filter(|g| !g.is_record && !g.is_row)
            .map(|g| g.name.clone())
            .collect();
        let needs = flows::dependence(field_types, &params, module, ctx.names, scope, kind);
        for g in generics.iter().filter(|g| !g.is_record && !g.is_row) {
            let needed = needs.contains(&g.name);
            if needed && !flow.iter().any(|p| p.name == g.name) {
                let stated: Vec<&str> = flow.iter().map(|p| p.name.as_str()).collect();
                let mut fixed = stated.clone();
                fixed.push(&g.name);
                return Err(invalid(
                    format!(
                        "a field's `{aspect}` depends on `{}`, which `{aspect}({})` does not cover; write `{aspect}({})` (RFC-0224 rule 1)",
                        g.name,
                        flow_args(&stated),
                        flow_args(&fixed)
                    ),
                    &entry.span,
                ));
            }
        }
    }
    Ok(())
}

/// Whether `ty` holds a `name` by value: not only behind a shared reference, which is `Clone` and
/// `Copy` for every referent. `struct View<T> { r: &T }` is `Clone` for every `T`, so `T` is not
/// bounded; a position this does not look through counts as owned.
fn mentions_owned(ty: &TypeExpr, name: &str) -> bool {
    match ty {
        TypeExpr::Named(n, args, _) => n == name || args.iter().any(|a| mentions_owned(a, name)),
        TypeExpr::Reference(_) => false,
        TypeExpr::MutReference(inner) | TypeExpr::Array(inner) | TypeExpr::SizedArray(inner, _) => {
            mentions_owned(inner, name)
        }
        TypeExpr::Record(fields) => fields.iter().any(|(_, t)| mentions_owned(t, name)),
        _ => true,
    }
}

/// The methods a derivation writes (RFC-0207 section 2): `Clone` is the host clone every record
/// already uses, which clones each field through that field's own `clone` and keeps the active
/// variant of an enum. `Copy` has none.
fn derived_methods(
    entry: &ClauseEntry,
    target: &TypeExpr,
    module: &[String],
    ctx: &Ctx<'_>,
) -> Vec<FunDecl> {
    // The derivation of the std `Clone` is native; no other aspect has one.
    let is_clone = ctx.clone_id.is_some()
        && super::coherence::resolve_id(ctx.names, module, &entry.name) == ctx.clone_id;
    if !is_clone {
        return Vec::new();
    }
    let span = entry.span.clone();
    // `Self` resolves for a plain nominal target; an instantiated generic one is spelled out (`Self`
    // does not resolve to it at run time).
    let generic = matches!(target, TypeExpr::Named(_, args, _) if !args.is_empty());
    let return_type = if generic {
        target.clone()
    } else {
        TypeExpr::Named("Self".to_string(), Vec::new(), NameSpan(span.clone()))
    };
    vec![FunDecl {
        visibility: Visibility::Public,
        name: "clone".to_string(),
        generics: Vec::new(),
        where_clause: None,
        params: vec![Param {
            mutable: false,
            receiver: Some(ReceiverKind::Ref),
            name: "self".into(),
            type_ann: None,
            span: span.clone(),
        }],
        return_type: Some(return_type),
        native: Some(NativeBinding {
            key_path: ["std", "core", "record_clone"].map(String::from).to_vec(),
            span: span.clone(),
        }),
        body: Block {
            stmts: Vec::new(),
            tail: None,
            span: span.clone(),
        },
        span,
    }]
}

/// The impl's generics: the declaration's own. A `derives` entry holds when each type parameter has the
/// aspect (`copy struct W<T>` is `Copy` exactly when `T` is), so it is bounded by that aspect; this
/// over-approximates a parameter no field mentions, and an exact per-instantiation rule replaces it
/// with the row machinery (RFC-0207 section 2, rule 2). A colon-list marker is bounded by nothing.
fn impl_generics(
    generics: &[GenericParam],
    entry: &ClauseEntry,
    bound: Option<&str>,
    field_types: &[TypeExpr],
    flow: Option<&[String]>,
) -> Vec<GenericParam> {
    generics
        .iter()
        .map(|g| {
            let mut param = g.clone();
            param.bounds = Vec::new();
            // A stated flow (`via A + B`) bounds exactly the parameters it names; without one the compiler
            // computes the set from the fields.
            let in_flow = match flow {
                Some(flow) => flow.contains(&g.name),
                None => field_types.iter().any(|ty| mentions_owned(ty, &g.name)),
            };
            if let Some(bound) = bound
                && !g.is_record
                && !g.is_row
                && in_flow
            {
                param.bounds.push(Bound {
                    polarity: Polarity::Positive,
                    head: BoundHead::Aspect(TypeExpr::Named(
                        bound.to_string(),
                        Vec::new(),
                        NameSpan(entry.span.clone()),
                    )),
                    assoc_bindings: Vec::new(),
                    span: entry.span.clone(),
                });
            }
            param
        })
        .collect()
}

#[cfg(test)]
mod tests;
