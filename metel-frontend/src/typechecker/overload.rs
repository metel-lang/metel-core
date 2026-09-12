//! Free-function overloading by exact argument-type match (METEL-180).
//!
//! A function *name* is "overloaded" when a module declares more than one free
//! `fun` with that name. Overloaded functions must be non-generic and have fully
//! annotated parameters so each definition has a distinct, concrete signature.
//!
//! Resolution is **exact-match only**: at a call site the argument types must
//! equal a candidate's parameter types exactly. Implicit numeric `From`
//! coercions do **not** participate in overload selection (decided in sprint 22).
//!
//! Implementation strategy: each overloaded definition is assigned a unique
//! [`SymbolId`] from a dedicated range (see `symbols::OVERLOAD_SYM_START`).
//! Construction selects the matching candidate at each call site and stamps its
//! id into `TypedExpr::Call::callee_id`; the evaluator registers each
//! overloaded definition under its id and dispatches such calls through its
//! symbol registry. Names never disambiguate overloads anywhere in the pipeline.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering};

use crate::ast::{Decl, Expr, FunDecl, Span};
use crate::error::{MetelError, TypeErrorCode};
use crate::symbols::SymbolId;
use crate::typeinference::{OverloadEntry, OverloadTable, TypeDefinitionRegistry, TypeVar};
use crate::types::Type;

use super::conversions::{
    infer_type_to_type, type_expr_to_infer, type_expr_to_infer_with_assoc_ctx, AssocResolveCtx,
};

/// Process-global allocator for overload-definition `SymbolIds`. Overload tables
/// are built per module; the global counter keeps ids unique across the whole
/// graph so the evaluator's symbol registry never collides.
static NEXT_OVERLOAD_SYM: AtomicU32 = AtomicU32::new(crate::symbols::OVERLOAD_SYM_START);

fn next_overload_symbol() -> SymbolId {
    SymbolId(NEXT_OVERLOAD_SYM.fetch_add(1, Ordering::Relaxed))
}

/// The overload table for the embedded `std::core` declarations, built once per
/// process so every module (and the single-program path) sees the SAME
/// `SymbolId` for each `std::core` overload — call sites in any module and the
/// runtime registration must agree on the id.
pub(super) fn core_overload_table() -> &'static OverloadTable {
    use std::sync::OnceLock;
    static CORE: OnceLock<OverloadTable> = OnceLock::new();
    CORE.get_or_init(|| {
        build_table_from_decls(&crate::stdlib::core_program().decls, None)
            .expect("embedded std::core overloads must validate; they are compiled in")
    })
}

/// The `SymbolId` of an embedded `std::core` overloaded definition, or `None`
/// if the declaration's name is not overloaded in `std::core`. Used by the
/// evaluator's embedded-core seeding to register host impls under the same
/// ids the typechecker stamps into call sites.
#[must_use]
pub fn core_native_symbol(fun: &FunDecl) -> Option<SymbolId> {
    entry_for_decl(core_overload_table(), fun).map(|e| e.symbol_id)
}

/// Build the overload table for a module: the module's own overload groups,
/// plus the `std::core` groups (so `assert(cond)` / `assert(cond, msg)` resolve
/// everywhere) and any overload groups `imported` brings in from other user
/// modules (metel-core#1143) — except where the module declares its own `fun`
/// with the same name, which shadows either kind of imported group entirely.
///
/// A module group whose signatures exactly match a `std::core` group (i.e. the
/// `std::core` module checking its own decls) reuses the canonical core entries
/// so the `SymbolIds` agree across the whole graph.
///
/// `imported` is this module's own explicit/glob overload imports, already
/// resolved and filtered to visible names by `build_import_overloads` — its
/// entries carry the `SymbolId`s the *declaring* module's own overload table
/// assigned, so a call dispatched through an imported name agrees with the
/// evaluator's registration of the source module's definitions.
pub(super) fn build_overload_table(
    decls: &[Decl],
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
    imported: &OverloadTable,
) -> Result<OverloadTable, MetelError> {
    let mut table = build_table_from_decls(decls, Some((registry, current_module)))?;
    let core = core_overload_table();

    for (name, entries) in &mut table {
        if let Some(core_entries) = core.get(name) {
            let same_signatures = entries.len() == core_entries.len()
                && entries
                    .iter()
                    .all(|e| core_entries.iter().any(|c| c.params == e.params));
            if same_signatures {
                entries.clone_from(core_entries);
            }
        }
    }

    let local_fun_names: std::collections::HashSet<&str> = decls
        .iter()
        .filter_map(|d| match d {
            Decl::Fun(f) => Some(f.name.as_str()),
            _ => None,
        })
        .collect();
    for (name, entries) in core {
        if !local_fun_names.contains(name.as_str()) {
            table.entry(name.clone()).or_insert_with(|| entries.clone());
        }
    }
    for (name, entries) in imported {
        if !local_fun_names.contains(name.as_str()) {
            table.entry(name.clone()).or_insert_with(|| entries.clone());
        }
    }
    Ok(table)
}

/// Group a declaration list's same-name `fun`s into validated overload
/// entries, allocating a fresh `SymbolId` per definition.
///
/// Errors if an overloaded function is generic, has an unannotated parameter, or
/// collides with another overload on identical parameter types.
fn build_table_from_decls(
    decls: &[Decl],
    assoc_ctx: Option<(&TypeDefinitionRegistry, &[String])>,
) -> Result<OverloadTable, MetelError> {
    let mut groups: HashMap<&str, Vec<&FunDecl>> = HashMap::new();
    for decl in decls {
        if let Decl::Fun(f) = decl {
            groups.entry(f.name.as_str()).or_default().push(f);
        }
    }

    let mut table = OverloadTable::new();
    for (name, funs) in groups {
        if funs.len() < 2 {
            continue;
        }
        let mut entries: Vec<OverloadEntry> = Vec::new();
        for f in funs {
            if !f.generics.is_empty() {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0002,
                    format!("overloaded function `{name}` cannot be generic"),
                    &f.span,
                ));
            }
            let params = fun_param_types(f, assoc_ctx)?;
            let ret = match &f.return_type {
                Some(te) => {
                    infer_type_to_type(&type_expr_to_infer_for_overload(te, assoc_ctx), &f.span)?
                }
                None => Type::Unit,
            };
            if entries.iter().any(|e| e.params == params) {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0011,
                    format!(
                        "duplicate definition of `{name}` with identical parameter types; \
                         overloads must differ in their parameter types"
                    ),
                    &f.span,
                ));
            }
            entries.push(OverloadEntry {
                params,
                ret,
                symbol_id: next_overload_symbol(),
            });
        }
        table.insert(name.to_string(), entries);
    }
    Ok(table)
}

/// Concrete parameter types of a function declaration. Every parameter must be
/// annotated (overloaded functions require this).
fn type_expr_to_infer_for_overload(
    te: &crate::ast::TypeExpr,
    assoc_ctx: Option<(&TypeDefinitionRegistry, &[String])>,
) -> crate::typeinference::InferType {
    let Some((registry, current_module)) = assoc_ctx else {
        return type_expr_to_infer(te);
    };
    let assoc_ctx = AssocResolveCtx {
        registry,
        current_module,
        current_aspect: None,
    };
    type_expr_to_infer_with_assoc_ctx(te, &HashMap::<String, TypeVar>::new(), None, &assoc_ctx)
}

fn fun_param_types(
    fun: &FunDecl,
    assoc_ctx: Option<(&TypeDefinitionRegistry, &[String])>,
) -> Result<Vec<Type>, MetelError> {
    fun.params
        .iter()
        .map(|p| {
            let ann = p.type_ann.as_ref().ok_or_else(|| {
                MetelError::type_error(
                    TypeErrorCode::T0002,
                    format!(
                        "overloaded function `{}` requires a type annotation on every parameter",
                        fun.name
                    ),
                    &p.span,
                )
            })?;
            infer_type_to_type(&type_expr_to_infer_for_overload(ann, assoc_ctx), &p.span)
        })
        .collect()
}

/// The overload entry for a declaration, or `None` if `fun`'s name is not
/// overloaded. Matches the declaration against the table by its concrete
/// parameter signature.
pub(super) fn entry_for_decl<'a>(
    table: &'a OverloadTable,
    fun: &FunDecl,
) -> Option<&'a OverloadEntry> {
    let entries = table.get(fun.name.as_str())?;
    let params = fun_param_types(fun, None).ok()?;
    entries.iter().find(|e| e.params == params)
}

/// Select the overload candidate whose parameters exactly match `arg_types`.
/// Returns `None` when no candidate matches (no implicit coercion is applied).
pub(super) fn select<'a>(
    entries: &'a [OverloadEntry],
    arg_types: &[Type],
) -> Option<&'a OverloadEntry> {
    entries
        .iter()
        .find(|e| e.params.len() == arg_types.len() && e.params == arg_types)
}

/// If `callee` is a bare name reference (`Ident` or a normalized `ResolvedPath`),
/// return that name. Overloading applies only to such direct named calls.
pub(super) fn callee_name(callee: &Expr) -> Option<&str> {
    match callee {
        Expr::Ident(name, _) => Some(name.as_str()),
        Expr::ResolvedPath { resolved, .. } => Some(resolved.as_str()),
        _ => None,
    }
}

/// Error for a call to an overloaded name where no candidate matches the argument
/// types exactly. Lists the available signatures.
pub(super) fn no_match_error(
    name: &str,
    arg_types: &[Type],
    entries: &[OverloadEntry],
    span: &Span,
) -> MetelError {
    let got = arg_types
        .iter()
        .map(std::string::ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    let candidates = entries
        .iter()
        .map(|e| {
            format!(
                "({})",
                e.params
                    .iter()
                    .map(std::string::ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    MetelError::type_error(
        TypeErrorCode::T0003,
        format!(
            "no overload of `{name}` matches argument types ({got}); \
             available: {candidates} (overload resolution is exact, with no implicit coercion)"
        ),
        span,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typeinference::OverloadEntry;

    fn entry(params: Vec<Type>, ret: Type) -> OverloadEntry {
        OverloadEntry {
            params,
            ret,
            symbol_id: next_overload_symbol(),
        }
    }

    #[test]
    fn overload_symbol_ids_are_unique_and_in_range() {
        let a = next_overload_symbol();
        let b = next_overload_symbol();
        assert_ne!(a, b);
        assert!(a.0 >= crate::symbols::OVERLOAD_SYM_START);
        assert!(b.0 >= crate::symbols::OVERLOAD_SYM_START);
    }

    #[test]
    fn select_requires_exact_match() {
        let entries = vec![
            entry(vec![Type::I32], Type::Unit),
            entry(vec![Type::I64], Type::Unit),
        ];
        // Exact match picks the right candidate.
        assert_eq!(
            select(&entries, &[Type::I32]).unwrap().symbol_id,
            entries[0].symbol_id
        );
        assert_eq!(
            select(&entries, &[Type::I64]).unwrap().symbol_id,
            entries[1].symbol_id
        );
        // No coercion: a type with no exact candidate does not match.
        assert!(select(&entries, &[Type::I16]).is_none());
        // Arity mismatch does not match.
        assert!(select(&entries, &[Type::I32, Type::I32]).is_none());
        assert!(select(&entries, &[]).is_none());
    }

    #[test]
    fn select_distinguishes_by_arity() {
        let entries = vec![
            entry(vec![Type::I64], Type::I64),
            entry(vec![Type::I64, Type::I64], Type::I64),
        ];
        assert_eq!(select(&entries, &[Type::I64]).unwrap().params.len(), 1);
        assert_eq!(
            select(&entries, &[Type::I64, Type::I64])
                .unwrap()
                .params
                .len(),
            2
        );
    }
}
