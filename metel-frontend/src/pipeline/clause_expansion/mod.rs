//! Declaration clauses become the marker impls they stand for (RFC-0207, metel-core#1928).
//!
//! `struct T: A derives B` is `struct T` with `extend T: A;` and `extend T: B;`, so the later stages see an
//! `extend` and a clause for the same aspect as the overlap they are (`T0015`). This runs after name
//! resolution because it has to read the aspect declarations:
//! - the `copy` class keyword names the aspect with the `implicit` property;
//! - `derives A` also grants every positive super-aspect `A` marks `deriving` (`Copy: deriving Clone`,
//!   RFC-0213 section 4), under the same condition;
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
    /// Positive `deriving` supers, as written in the declaring module.
    deriving: Vec<String>,
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
                        deriving: ad
                            .supers
                            .iter()
                            .filter(|s| s.deriving && !s.negative)
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
        implicit: aspects.iter().find(|(_, a)| a.implicit).map(|(id, _)| *id),
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

/// The `copy` class keyword names the aspect with the `implicit` property.
fn name_class_keywords(
    clauses: &mut crate::data::ast::DeclClauses,
    ctx: &Ctx<'_>,
) -> Result<(), MetelError> {
    for entry in &mut clauses.derives {
        if entry.from_class_keyword && entry.name.is_empty() {
            let implicit = ctx.aspects.values().find(|a| a.implicit).ok_or_else(|| {
                MetelError::type_error(
                    TypeErrorCode::T0003,
                    "the `copy` class keyword needs an aspect with the `implicit` property, and the program has none".to_string(),
                    &entry.span,
                )
            })?;
            entry.name = implicit.name.clone();
        }
    }
    Ok(())
}

/// Each entry with the aspect that bounds a generic type's parameters: a `derives` entry is bounded by itself,
/// a colon-list marker by nothing; a brought super is bounded by the aspect that brought it.
fn clause_entries(
    clauses: &crate::data::ast::DeclClauses,
    module: &[String],
    ctx: &Ctx<'_>,
) -> Vec<(ClauseEntry, Option<String>)> {
    let mut entries: Vec<(ClauseEntry, Option<String>)> = Vec::new();
    for entry in &clauses.colon {
        entries.push((entry.clone(), None));
    }
    for entry in &clauses.derives {
        entries.push((entry.clone(), Some(entry.name.clone())));
        let Some(id) = super::coherence::resolve_id(ctx.names, module, &entry.name) else {
            continue;
        };
        let Some(aspect) = ctx.aspects.get(&id) else {
            continue;
        };
        for sup in &aspect.deriving {
            // The super as the declaring module wrote it must name the same aspect here.
            let same = super::coherence::resolve_id(ctx.names, &aspect.module, sup).is_some_and(
                |sup_id| super::coherence::resolve_id(ctx.names, module, sup) == Some(sup_id),
            );
            if same {
                entries.push((
                    ClauseEntry {
                        name: sup.clone(),
                        from_class_keyword: false,
                        // The `Clone` a `Copy` brings has the flow of the `Copy` entry (RFC-0224 section 3).
                        flow: entry.flow.clone(),
                        span: entry.span.clone(),
                    },
                    Some(entry.name.clone()),
                ));
            }
        }
    }
    entries
}

/// What a clause entry is for the flow (RFC-0224): the `Copy` entry and the supers it brings carry the flow of
/// the `Copy` declaration; an original `derives Clone` carries its own computed flow; any other entry has none.
/// Also whether the entry is a `derives` entry as written (not a brought super), and whether it is the `Copy` one.
fn entry_origin(
    entry: &ClauseEntry,
    bound: Option<&str>,
    module: &[String],
    ctx: &Ctx<'_>,
) -> (bool, bool, Option<Kind>) {
    let original = bound == Some(entry.name.as_str());
    let resolves = |name: &str, id: Option<SymbolId>| {
        id.is_some() && super::coherence::resolve_id(ctx.names, module, name) == id
    };
    let implicit = ctx.flow_aspects.implicit;
    let is_copy_entry = resolves(&entry.name, implicit);
    let from_copy = is_copy_entry || bound.is_some_and(|b| resolves(b, implicit));
    let origin = if from_copy {
        Some(Kind::Copy)
    } else if original && resolves(&entry.name, ctx.clone_id) {
        Some(Kind::Clone)
    } else {
        None
    };
    (original, is_copy_entry, origin)
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
    name_class_keywords(clauses, ctx)?;
    let args: Vec<TypeExpr> = decl
        .generics
        .iter()
        .map(|g| TypeExpr::Named(g.name.clone(), Vec::new(), NameSpan(decl.span.clone())))
        .collect();
    let target = TypeExpr::Named(decl.name.to_string(), args, NameSpan(decl.span.clone()));
    let entries = clause_entries(clauses, module, ctx);
    let mut seen = std::collections::HashSet::new();
    let mut impls = Vec::new();
    // Derivation is idempotent per type and aspect: `copy struct T derives Copy` derives it once.
    for (entry, bound) in entries
        .iter()
        .filter(|(entry, _)| seen.insert(entry.name.clone()))
    {
        let (original, is_copy_entry, origin) = entry_origin(entry, bound.as_deref(), module, ctx);
        if original {
            check_flow(
                entry,
                is_copy_entry,
                decl.generics,
                decl.fields,
                module,
                ctx,
                scope,
            )?;
            if is_copy_entry && decl.public && entry.flow.is_none() {
                check_public_flow_stated(decl, entry, module, ctx, scope)?;
            }
        }
        let flow = entry_flow(entry, origin, decl.name, module, ctx, scope);
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
    Ok(impls)
}

/// The flow an entry's impl is generated with (RFC-0224): the `Copy` entry and the supers it brings carry the
/// `Copy` declaration's flow, stated with `via` or computed from the fields; a `derives Clone` that no `Copy`
/// brings carries its computed `Clone` flow; any other entry has none (its parameters are bounded by the
/// per-parameter rule).
fn entry_flow(
    entry: &ClauseEntry,
    origin: Option<Kind>,
    type_name: &str,
    module: &[String],
    ctx: &Ctx<'_>,
    scope: &Scope<'_>,
) -> Option<Vec<String>> {
    let kind = origin?;
    if kind == Kind::Copy
        && let Some(stated) = &entry.flow
    {
        return Some(stated.iter().map(|p| p.name.clone()).collect());
    }
    scope
        .own(type_name, module, ctx.names, kind)
        .map(|e| e.set().iter().cloned().collect())
}

/// RFC-0224 section 2 rule 3: a `pub` generic type that derives `Copy` without `via` has a computed flow, which
/// is its published interface, so it may omit `via` only when that flow is empty. Otherwise the error shows
/// the computed set as the fix-it. Non-`pub` and non-generic types are unaffected.
fn check_public_flow_stated(
    decl: &Declaration<'_>,
    entry: &ClauseEntry,
    module: &[String],
    ctx: &Ctx<'_>,
    scope: &Scope<'_>,
) -> Result<(), MetelError> {
    let Some(computed) = scope.own(decl.name, module, ctx.names, Kind::Copy) else {
        return Ok(());
    };
    let set: Vec<&str> = computed.set().iter().map(String::as_str).collect();
    if set.is_empty() {
        return Ok(());
    }
    Err(MetelError::type_error(
        TypeErrorCode::T0046,
        format!(
            "a public generic type must state the flow of its `Copy` when it is not empty; write `derives Copy via {}` (RFC-0224 rule 3)",
            set.join(" + ")
        ),
        &entry.span,
    ))
}

/// RFC-0224 section 2: the checks on a `derives Copy` entry's flow, stated or computed. A `via` clause is
/// accepted on `Copy` only (rule: the other markers adopt it in their own RFCs), names only type
/// parameters of the declaration, and must contain every parameter a field's copy-ness depends on (it
/// may contain more). A `Copy` declaration with a field that depends on a row- or record-kinded parameter is
/// rejected (rule 7). Rule 6, a field that depends on an associated type, needs no check yet: a struct or enum
/// field `T::Item` is rejected as an unknown type before this runs.
fn check_flow(
    entry: &ClauseEntry,
    is_copy_entry: bool,
    generics: &[GenericParam],
    field_types: &[TypeExpr],
    module: &[String],
    ctx: &Ctx<'_>,
    scope: &Scope<'_>,
) -> Result<(), MetelError> {
    let invalid =
        |message: String, span: &Span| MetelError::type_error(TypeErrorCode::T0046, message, span);
    if let Some(flow) = &entry.flow {
        if !is_copy_entry {
            return Err(invalid(
                format!(
                    "a `via` clause is accepted only on `derives Copy` in this release (RFC-0224), not on `{}`",
                    entry.name
                ),
                &entry.span,
            ));
        }
        for param in flow {
            let declared = generics.iter().find(|g| g.name == param.name);
            match declared {
                None => {
                    return Err(invalid(
                        format!(
                            "`via {}` names no type parameter of this declaration",
                            param.name
                        ),
                        &param.span,
                    ));
                }
                Some(g) if g.is_record || g.is_row => {
                    return Err(invalid(
                        format!(
                            "`via {}` names a row- or record-kinded parameter; a flow lists type parameters only (RFC-0224 rule 7)",
                            param.name
                        ),
                        &param.span,
                    ));
                }
                Some(_) => {}
            }
        }
    }
    if !is_copy_entry {
        return Ok(());
    }
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
    if let Some(flow) = &entry.flow {
        let params: Vec<String> = generics
            .iter()
            .filter(|g| !g.is_record && !g.is_row)
            .map(|g| g.name.clone())
            .collect();
        let needs = flows::dependence(field_types, &params, module, ctx.names, scope, Kind::Copy);
        for g in generics.iter().filter(|g| !g.is_record && !g.is_row) {
            let needed = needs.contains(&g.name);
            if needed && !flow.iter().any(|p| p.name == g.name) {
                let stated: Vec<&str> = flow.iter().map(|p| p.name.as_str()).collect();
                let mut fixed = stated.clone();
                fixed.push(&g.name);
                return Err(invalid(
                    format!(
                        "a field's `Copy` depends on `{}`, which `via {}` does not cover; write `via {}` (RFC-0224 rule 1)",
                        g.name,
                        stated.join(" + "),
                        fixed.join(" + ")
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
        TypeExpr::Tuple(items) => items.iter().any(|t| mentions_owned(t, name)),
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
