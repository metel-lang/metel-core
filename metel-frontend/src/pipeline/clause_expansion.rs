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
    let ctx = Ctx {
        names,
        aspects: &aspects,
        clone_id,
    };
    for module in &mut graph.modules {
        let path = module.module_path.clone();
        expand_decls(&mut module.program.decls, &path, &ctx)?;
    }
    Ok(())
}

struct Ctx<'a> {
    names: &'a ResolvedNames,
    aspects: &'a HashMap<SymbolId, Aspect>,
    clone_id: Option<SymbolId>,
}

/// Expand a declaration list, and the declaration lists of the function bodies inside it.
fn expand_decls(decls: &mut Vec<Decl>, module: &[String], ctx: &Ctx<'_>) -> Result<(), MetelError> {
    let mut out: Vec<Decl> = Vec::with_capacity(decls.len());
    for mut decl in std::mem::take(decls) {
        match &mut decl {
            Decl::Fun(fun) => expand_decls(&mut fun.body.stmts, module, ctx)?,
            Decl::Impl(block) => {
                for method in &mut block.methods {
                    expand_decls(&mut method.body.stmts, module, ctx)?;
                }
            }
            _ => {}
        }
        let impls = match &mut decl {
            Decl::Struct(sd) => {
                let fields: Vec<TypeExpr> = sd.fields.iter().map(|f| f.type_ann.clone()).collect();
                clause_impls(
                    &sd.name,
                    &sd.generics,
                    &mut sd.clauses,
                    &fields,
                    &sd.span,
                    module,
                    ctx,
                )?
            }
            Decl::Enum(ed) => {
                let fields: Vec<TypeExpr> = ed
                    .variants
                    .iter()
                    .flat_map(|v| v.fields.iter().map(|f| f.type_ann.clone()))
                    .collect();
                clause_impls(
                    &ed.name,
                    &ed.generics,
                    &mut ed.clauses,
                    &fields,
                    &ed.span,
                    module,
                    ctx,
                )?
            }
            _ => Vec::new(),
        };
        out.push(decl);
        out.extend(impls.into_iter().map(Decl::Impl));
    }
    *decls = out;
    Ok(())
}

fn clause_impls(
    type_name: &str,
    generics: &[GenericParam],
    clauses: &mut crate::data::ast::DeclClauses,
    field_types: &[TypeExpr],
    span: &Span,
    module: &[String],
    ctx: &Ctx<'_>,
) -> Result<Vec<ImplBlock>, MetelError> {
    if clauses.is_empty() {
        return Ok(Vec::new());
    }
    // The `copy` class keyword names the aspect with the `implicit` property.
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
    let args: Vec<TypeExpr> = generics
        .iter()
        .map(|g| TypeExpr::Named(g.name.clone(), Vec::new(), NameSpan(span.clone())))
        .collect();
    let target = TypeExpr::Named(type_name.to_string(), args, NameSpan(span.clone()));
    // Each entry with the aspect that bounds a generic type's parameters: a `derives` entry is bounded by
    // itself, a colon-list marker by nothing; a brought super is bounded by the aspect that brought it.
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
                        span: entry.span.clone(),
                    },
                    Some(entry.name.clone()),
                ));
            }
        }
    }
    let mut seen = std::collections::HashSet::new();
    Ok(entries
        .iter()
        // Derivation is idempotent per type and aspect: `copy struct T derives Copy` derives it once.
        .filter(|(entry, _)| seen.insert(entry.name.clone()))
        .map(|(entry, bound)| ImplBlock {
            polarity: Polarity::Positive,
            generics: impl_generics(generics, entry, bound.as_deref(), field_types),
            aspect_name: Some(entry.name.clone()),
            aspect_type_args: Vec::new(),
            target_type: target.clone(),
            where_clause: None,
            assoc_type_defs: Vec::new(),
            methods: derived_methods(entry, &target, module, ctx),
            from_clause: true,
            span: entry.span.clone(),
        })
        .collect())
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
) -> Vec<GenericParam> {
    generics
        .iter()
        .map(|g| {
            let mut param = g.clone();
            param.bounds = Vec::new();
            if let Some(bound) = bound
                && !g.is_record
                && !g.is_row
                && field_types.iter().any(|ty| mentions_owned(ty, &g.name))
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
