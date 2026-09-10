//! Path normalization pass (#185).
//!
//! Rewrites `Expr::Path` nodes with module qualifiers to `Expr::ResolvedPath`.
//! Single-segment paths and type member accesses (e.g. `Color::Red`) are left as-is.
//!
//! A path `[s1, s2, ...]` is considered module-qualified when `s1` is:
//! - the reserved keyword `"root"`, `"self"`, or `"super"`, or
//! - the name of a loaded module in the `ModuleGraph`.
//!
//! Everything else (e.g. `Color::Red` where Color is a struct/enum) passes through
//! unchanged so the typechecker's existing type-member handling works unmodified.

use std::collections::HashSet;

use crate::ast::{
    Block, Decl, Expr, ForInit, FunDecl, ImplBlock, LetDecl, MatchArm, MutDecl, Stmt,
};
use crate::error::MetelError;
use crate::module_loader::{LoadedModule, ModuleGraph};
use crate::name_resolver::{ModuleScope, ResolvedNames};
use crate::symbols::SymbolId;

// ── Public API ────────────────────────────────────────────────────────────────

/// Opaque wrapper around `ModuleGraph` that proves the normalization pass has run.
/// `check_graph` requires this type; calling it with a raw `ModuleGraph` is a
/// compile-time error. See ADR-0021.
pub struct NormalizedModuleGraph(pub(crate) ModuleGraph);

impl NormalizedModuleGraph {
    #[must_use]
    pub fn modules(&self) -> &[LoadedModule] {
        &self.0.modules
    }
}

/// Run the path normalization pass on `graph`, rewriting qualified `Expr::Path`
/// nodes to `Expr::ResolvedPath` using the scope information in `names`.
///
/// Returns `NormalizedModuleGraph` — a newtype that downstream passes must accept
/// to enforce that normalization ran before typechecking.
///
/// # Errors
/// Returns an error if a qualified path cannot be resolved against `names`
/// (e.g. references an unknown module or name).
pub fn normalize(
    mut graph: ModuleGraph,
    names: &ResolvedNames,
) -> Result<NormalizedModuleGraph, MetelError> {
    let module_names: HashSet<String> = graph
        .modules
        .iter()
        .filter_map(|m| m.module_path.first().cloned())
        .collect();

    for loaded in &mut graph.modules {
        let scope = names.scopes.get(&loaded.module_path);
        normalize_program_decls(
            &mut loaded.program.decls,
            scope,
            &module_names,
            &names.symbols,
        )?;
    }
    Ok(NormalizedModuleGraph(graph))
}

// ── Internal helpers ──────────────────────────────────────────────────────────

fn normalize_program_decls(
    decls: &mut Vec<Decl>,
    scope: Option<&ModuleScope>,
    module_names: &HashSet<String>,
    symbols: &std::collections::HashMap<(Vec<String>, String), crate::symbols::SymbolId>,
) -> Result<(), MetelError> {
    for decl in decls {
        normalize_decl(decl, scope, module_names, symbols)?;
    }
    Ok(())
}

fn normalize_decl(
    decl: &mut Decl,
    scope: Option<&ModuleScope>,
    module_names: &HashSet<String>,
    symbols: &std::collections::HashMap<(Vec<String>, String), crate::symbols::SymbolId>,
) -> Result<(), MetelError> {
    match decl {
        Decl::Let(ld) => normalize_expr(&mut ld.value, scope, module_names, symbols),
        Decl::Mut(md) => normalize_expr(&mut md.value, scope, module_names, symbols),
        Decl::Fun(fd) => normalize_fun(fd, scope, module_names, symbols),
        Decl::Impl(ib) => normalize_impl(ib, scope, module_names, symbols),
        Decl::Stmt(s) => normalize_stmt(s, scope, module_names, symbols),
        Decl::Struct(_) | Decl::Enum(_) | Decl::Aspect(_) => Ok(()),
        Decl::TypeAlias(_) => {
            unreachable!("RFC-0160 type aliases are expanded before path normalization")
        }
    }
}

fn normalize_fun(
    fun: &mut FunDecl,
    scope: Option<&ModuleScope>,
    module_names: &HashSet<String>,
    symbols: &std::collections::HashMap<(Vec<String>, String), crate::symbols::SymbolId>,
) -> Result<(), MetelError> {
    normalize_block(&mut fun.body, scope, module_names, symbols)
}

fn normalize_impl(
    ib: &mut ImplBlock,
    scope: Option<&ModuleScope>,
    module_names: &HashSet<String>,
    symbols: &std::collections::HashMap<(Vec<String>, String), crate::symbols::SymbolId>,
) -> Result<(), MetelError> {
    for method in &mut ib.methods {
        normalize_fun(method, scope, module_names, symbols)?;
    }
    Ok(())
}

fn normalize_block(
    block: &mut Block,
    scope: Option<&ModuleScope>,
    module_names: &HashSet<String>,
    symbols: &std::collections::HashMap<(Vec<String>, String), crate::symbols::SymbolId>,
) -> Result<(), MetelError> {
    for decl in &mut block.stmts {
        normalize_decl(decl, scope, module_names, symbols)?;
    }
    if let Some(tail) = &mut block.tail {
        normalize_expr(tail, scope, module_names, symbols)?;
    }
    Ok(())
}

fn normalize_stmt(
    stmt: &mut Stmt,
    scope: Option<&ModuleScope>,
    module_names: &HashSet<String>,
    symbols: &std::collections::HashMap<(Vec<String>, String), crate::symbols::SymbolId>,
) -> Result<(), MetelError> {
    match stmt {
        Stmt::Expr(e) => normalize_expr(e, scope, module_names, symbols),
        Stmt::While(w) => {
            normalize_expr(&mut w.condition, scope, module_names, symbols)?;
            normalize_block(&mut w.body, scope, module_names, symbols)
        }
        Stmt::For(f) => {
            if let Some(init) = &mut f.init {
                match init {
                    ForInit::Expr(e) => normalize_expr(e, scope, module_names, symbols)?,
                    ForInit::Let(ld) => normalize_let_decl(ld, scope, module_names, symbols)?,
                    ForInit::Mut(md) => normalize_mut_decl(md, scope, module_names, symbols)?,
                }
            }
            if let Some(cond) = &mut f.condition {
                normalize_expr(cond, scope, module_names, symbols)?;
            }
            if let Some(step) = &mut f.step {
                normalize_expr(step, scope, module_names, symbols)?;
            }
            normalize_block(&mut f.body, scope, module_names, symbols)
        }
        Stmt::ForIn(fi) => {
            normalize_expr(&mut fi.iterable, scope, module_names, symbols)?;
            normalize_block(&mut fi.body, scope, module_names, symbols)
        }
    }
}

fn normalize_mut_decl(
    md: &mut MutDecl,
    scope: Option<&ModuleScope>,
    module_names: &HashSet<String>,
    symbols: &std::collections::HashMap<(Vec<String>, String), crate::symbols::SymbolId>,
) -> Result<(), MetelError> {
    normalize_expr(&mut md.value, scope, module_names, symbols)
}

fn normalize_let_decl(
    ld: &mut LetDecl,
    scope: Option<&ModuleScope>,
    module_names: &HashSet<String>,
    symbols: &std::collections::HashMap<(Vec<String>, String), crate::symbols::SymbolId>,
) -> Result<(), MetelError> {
    normalize_expr(&mut ld.value, scope, module_names, symbols)
}

// Exhaustive match over every AST/type-system variant; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
fn normalize_expr(
    expr: &mut Expr,
    scope: Option<&ModuleScope>,
    module_names: &HashSet<String>,
    symbols: &std::collections::HashMap<(Vec<String>, String), crate::symbols::SymbolId>,
) -> Result<(), MetelError> {
    match expr {
        Expr::Literal(_, _) | Expr::Ident(_, _) | Expr::ResolvedPath { .. } | Expr::Continue(_) => {
            Ok(())
        }

        Expr::Path(segments, _seg_spans, span) => {
            if let Some((resolved, symbol_id)) =
                try_resolve_path(segments, scope, module_names, symbols)
            {
                let original = std::mem::take(segments);
                *expr = Expr::ResolvedPath {
                    resolved,
                    symbol_id,
                    original,
                    span: span.clone(),
                };
            }
            Ok(())
        }

        Expr::Tuple(elems, _) | Expr::Array(elems, _) => {
            for e in elems {
                normalize_expr(e, scope, module_names, symbols)?;
            }
            Ok(())
        }
        Expr::RecordLiteral { fields, .. } => {
            for (_, expr) in fields {
                normalize_expr(expr, scope, module_names, symbols)?;
            }
            Ok(())
        }
        Expr::RepeatArray(elem, _, _) => normalize_expr(elem, scope, module_names, symbols),
        Expr::BinOp(lhs, _, rhs, _) => {
            normalize_expr(lhs, scope, module_names, symbols)?;
            normalize_expr(rhs, scope, module_names, symbols)
        }
        Expr::UnaryOp(_, operand, _) => normalize_expr(operand, scope, module_names, symbols),
        Expr::Cast { expr: inner, .. } | Expr::Ascribe { expr: inner, .. } => {
            normalize_expr(inner, scope, module_names, symbols)
        }
        Expr::Assign { value, .. } => normalize_expr(value, scope, module_names, symbols),
        Expr::Call { callee, args, .. } => {
            normalize_expr(callee, scope, module_names, symbols)?;
            for a in args {
                normalize_expr(a, scope, module_names, symbols)?;
            }
            Ok(())
        }
        Expr::MethodCall { receiver, args, .. } => {
            normalize_expr(receiver, scope, module_names, symbols)?;
            for a in args {
                normalize_expr(a, scope, module_names, symbols)?;
            }
            Ok(())
        }
        Expr::FieldAccess { object, .. } | Expr::TupleAccess { object, .. } => {
            normalize_expr(object, scope, module_names, symbols)
        }
        Expr::Index { object, index, .. } => {
            normalize_expr(object, scope, module_names, symbols)?;
            normalize_expr(index, scope, module_names, symbols)
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            normalize_expr(condition, scope, module_names, symbols)?;
            normalize_block(then_branch, scope, module_names, symbols)?;
            if let Some(eb) = else_branch {
                normalize_block(eb, scope, module_names, symbols)?;
            }
            Ok(())
        }
        Expr::Loop { body, .. } | Expr::Closure { body, .. } => {
            normalize_block(body, scope, module_names, symbols)
        }
        Expr::Match(m) => {
            normalize_expr(&mut m.scrutinee, scope, module_names, symbols)?;
            for arm in &mut m.arms {
                normalize_arm(arm, scope, module_names, symbols)?;
            }
            Ok(())
        }
        Expr::StructLiteral {
            path,
            fields,
            symbol_id,
            ..
        } => {
            if let Some((local_path, type_id)) =
                try_normalize_struct_path(path, scope, module_names, symbols)
            {
                *path = local_path;
                *symbol_id = type_id;
            } else if let [only] = path.as_mut_slice() {
                // A single-segment path can still be an alias (#667): `import
                // lexer::Token as Tok;` then `Tok { .. }` needs to construct the
                // same `Token` a bare `Token { .. }` would, not go looking for a
                // never-declared type literally named `Tok`. Only item bindings
                // apply -- a `Module` binding here would mean `path` should have had
                // a second segment (`handle::Type`), a different, already-handled
                // shape.
                if let Some(binding) = scope.and_then(|s| s.explicit.get(only.as_str())) {
                    if binding.kind == crate::name_resolver::BindingKind::Item {
                        *only = binding.source_name.clone();
                        *symbol_id = Some(binding.symbol_id);
                    }
                }
            }
            for (_, v) in fields {
                normalize_expr(v, scope, module_names, symbols)?;
            }
            Ok(())
        }
        Expr::RecordProjection { path, .. } => {
            if let Some((resolved, _symbol_id)) =
                try_resolve_path(path, scope, module_names, symbols)
            {
                *path = vec![resolved];
            }
            Ok(())
        }
        Expr::PropagateError { expr, .. } => normalize_expr(expr, scope, module_names, symbols),
        Expr::Return(r) => match &mut r.value {
            Some(v) => normalize_expr(v, scope, module_names, symbols),
            None => Ok(()),
        },
        Expr::Break(b) => match &mut b.value {
            Some(v) => normalize_expr(v, scope, module_names, symbols),
            None => Ok(()),
        },
    }
}

fn normalize_arm(
    arm: &mut MatchArm,
    scope: Option<&ModuleScope>,
    module_names: &HashSet<String>,
    symbols: &std::collections::HashMap<(Vec<String>, String), crate::symbols::SymbolId>,
) -> Result<(), MetelError> {
    if let Some(guard) = &mut arm.guard {
        normalize_expr(guard, scope, module_names, symbols)?;
    }
    normalize_block(&mut arm.body, scope, module_names, symbols)
}

// ── Path resolution logic ─────────────────────────────────────────────────────

/// Try to resolve a multi-segment path to a bare local name and its stable symbol identity.
///
/// Returns `Some((resolved_name, symbol_id))` if the path is module-qualified and can be
/// rewritten. Returns `None` to leave the path unchanged (type member access,
/// single-segment, or unresolvable).
fn try_resolve_path(
    segments: &[String],
    scope: Option<&ModuleScope>,
    module_names: &HashSet<String>,
    // `Expr::Path` resolution gets its `symbol_id` from the module scope's explicit
    // bindings; it does not need the global symbol table (unlike struct literals).
    _symbols: &std::collections::HashMap<(Vec<String>, String), crate::symbols::SymbolId>,
) -> Option<(String, Option<SymbolId>)> {
    if segments.len() < 2 {
        return None; // single-segment paths are already Ident
    }

    let first = &segments[0];
    let declared_name = segments.last().unwrap();

    // Keywords: root/self/super — the declared name is the last segment
    if first == "root" || first == "self" || first == "super" {
        // Check the scope for an alias, otherwise use the declared name
        if let Some(s) = scope {
            if let Some((local, binding)) = s
                .explicit
                .iter()
                .find(|(_, b)| &b.source_name == declared_name)
            {
                return Some((local.clone(), Some(binding.symbol_id)));
            }
        }
        return Some((declared_name.clone(), None));
    }

    // Accept if `first` is either a loaded module name OR the first segment of a glob path
    // (handles virtual modules like `std` that have no physical file).
    let is_known_prefix = module_names.contains(first.as_str())
        || scope.is_some_and(|s| {
            s.globs
                .iter()
                .any(|(_, g)| g.first().map(std::string::String::as_str) == Some(first.as_str()))
        });

    if !is_known_prefix {
        return None; // e.g. Color::Red — Color is a type, not a module
    }

    // first is a known module prefix — find the local alias for this import
    if let Some(s) = scope {
        // 1. Explicit import with matching source
        for (local_name, binding) in &s.explicit {
            if binding
                .source_module
                .first()
                .map(std::string::String::as_str)
                == Some(first.as_str())
                && &binding.source_name == declared_name
            {
                return Some((local_name.clone(), Some(binding.symbol_id)));
            }
        }
        // 2. Glob import from this module — local name == source name
        let source_module: Vec<String> = segments[..segments.len() - 1].to_vec();
        if s.globs.iter().any(|(_, g)| {
            g == &source_module
                || g.first().map(std::string::String::as_str) == Some(first.as_str())
        }) {
            return Some((declared_name.clone(), None));
        }
    }

    // Module is known but no import binding found for this name — treat as bare name
    // (the typechecker will error if it's actually undefined)
    Some((declared_name.clone(), None))
}

/// Resolve a struct-literal path by stripping a module prefix, returning the local
/// `type[+variant]` path and the constructed type's stable `SymbolId` (METEL-185).
/// For `["std", "core", "Perhaps", "Some"]` returns `(["Perhaps", "Some"], id_of(Perhaps))`.
/// Returns `None` if the path starts with a type name, not a module.
fn try_normalize_struct_path(
    path: &[String],
    scope: Option<&ModuleScope>,
    module_names: &HashSet<String>,
    symbols: &std::collections::HashMap<(Vec<String>, String), crate::symbols::SymbolId>,
) -> Option<(Vec<String>, Option<crate::symbols::SymbolId>)> {
    if path.len() < 2 {
        return None;
    }
    let first = &path[0];
    // Only process if the first segment looks like a module, not a type.
    let is_known_prefix = module_names.contains(first.as_str())
        || scope.is_some_and(|s| {
            s.globs
                .iter()
                .any(|(_, g)| g.first().map(std::string::String::as_str) == Some(first.as_str()))
        });
    if !is_known_prefix {
        return None;
    }
    let s = scope?;
    // Find the longest glob prefix that matches the beginning of the path,
    // then return the remainder as the local type+variant path.
    let mut best: Option<usize> = None;
    for (_, glob_module) in &s.globs {
        if path.starts_with(glob_module.as_slice()) && path.len() > glob_module.len() {
            let len = glob_module.len();
            if best.is_none_or(|b| len > b) {
                best = Some(len);
            }
        }
    }
    let prefix_len = best?;
    // The stripped remainder is `[TypeName]` (struct) or `[EnumName, Variant]` (enum).
    // Either way the *type* is its first segment, declared in the matched module.
    let module = path[..prefix_len].to_vec();
    let type_name = &path[prefix_len];
    let type_id = symbols.get(&(module, type_name.clone())).copied();
    Some((path[prefix_len..].to_vec(), type_id))
}

// ── Desugar ? operator ────────────────────────────────────────────────────────
//
