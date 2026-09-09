//! Position-based queries over frontend analysis artifacts.
//!
//! These helpers are deliberately small and borrow their results from the
//! typed graph and name-resolution tables. Editor clients own byte/UTF-16
//! conversion; the frontend owns the meaning of a source position.

use crate::ast::Span;
use crate::name_resolver::ResolvedNames;
use crate::symbols::SymbolId;
use crate::typed_ast::{
    FunBody, TypedBlock, TypedDecl, TypedExpr, TypedForInit, TypedModuleGraph, TypedPlace,
    TypedStmt,
};

/// A resolved declaration location for a reference at a source position.
#[derive(Debug, Clone, Copy)]
pub struct Definition<'a> {
    pub symbol_id: SymbolId,
    pub span: &'a Span,
}

/// Return the innermost typed expression containing `byte_offset` in `filename`.
///
/// Offsets use the same UTF-8 byte coordinates stored by [`Span`]. Returns
/// `None` for whitespace, comments, declarations without typed bodies, and
/// generic function/closure bodies which deliberately remain untyped until
/// instantiation.
#[must_use]
pub fn expr_at<'a>(
    graph: &'a TypedModuleGraph,
    filename: &str,
    byte_offset: usize,
) -> Option<&'a TypedExpr> {
    graph.modules.iter().find_map(|module| {
        module
            .decls
            .iter()
            .find_map(|decl| decl_expr_at(decl, filename, byte_offset))
    })
}

/// Resolve a bare identifier reference at `byte_offset` to its declaration.
///
/// The current resolver records stable identities for bare top-level and
/// imported identifiers. Module-qualified paths are intentionally not reported
/// yet: their identity is available during normalization but is not retained in
/// `TypedExpr::Path`; that preservation is the follow-up required for path
/// definition queries. Local bindings likewise need stable local identities.
#[must_use]
pub fn definition_at<'a>(
    names: &'a ResolvedNames,
    filename: &str,
    byte_offset: usize,
) -> Option<Definition<'a>> {
    let (_, symbol_id) = names
        .references
        .iter()
        .filter(|(span, _)| contains(span, filename, byte_offset))
        .min_by_key(|(span, _)| span.end - span.start)?;
    let span = names.definitions.get(symbol_id)?;
    Some(Definition {
        symbol_id: *symbol_id,
        span,
    })
}

fn decl_expr_at<'a>(
    decl: &'a TypedDecl,
    filename: &str,
    byte_offset: usize,
) -> Option<&'a TypedExpr> {
    match decl {
        TypedDecl::Let(decl) => expr_at_expr(&decl.value, filename, byte_offset),
        TypedDecl::Mut(decl) => expr_at_expr(&decl.value, filename, byte_offset),
        TypedDecl::Fun(decl) => match &decl.body {
            FunBody::Typed(body) => block_expr_at(body, filename, byte_offset),
            FunBody::Generic(_) | FunBody::Native(_) => None,
        },
        TypedDecl::Impl(block) => block.methods.iter().find_map(|method| match &method.body {
            FunBody::Typed(body) => block_expr_at(body, filename, byte_offset),
            FunBody::Generic(_) | FunBody::Native(_) => None,
        }),
        TypedDecl::Stmt(stmt) => stmt_expr_at(stmt, filename, byte_offset),
        TypedDecl::Struct(_) | TypedDecl::Enum(_) | TypedDecl::Aspect(_) => None,
    }
}

fn block_expr_at<'a>(
    block: &'a TypedBlock,
    filename: &str,
    byte_offset: usize,
) -> Option<&'a TypedExpr> {
    block
        .stmts
        .iter()
        .find_map(|decl| decl_expr_at(decl, filename, byte_offset))
        .or_else(|| {
            block
                .tail
                .as_deref()
                .and_then(|expr| expr_at_expr(expr, filename, byte_offset))
        })
}

fn stmt_expr_at<'a>(
    stmt: &'a TypedStmt,
    filename: &str,
    byte_offset: usize,
) -> Option<&'a TypedExpr> {
    match stmt {
        TypedStmt::Expr(expr) => expr_at_expr(expr, filename, byte_offset),
        TypedStmt::While(stmt) => expr_at_expr(&stmt.condition, filename, byte_offset)
            .or_else(|| block_expr_at(&stmt.body, filename, byte_offset)),
        TypedStmt::For(stmt) => stmt
            .init
            .as_ref()
            .and_then(|init| match init {
                TypedForInit::Let(decl) => expr_at_expr(&decl.value, filename, byte_offset),
                TypedForInit::Mut(decl) => expr_at_expr(&decl.value, filename, byte_offset),
                TypedForInit::Expr(expr) => expr_at_expr(expr, filename, byte_offset),
            })
            .or_else(|| {
                stmt.condition
                    .as_ref()
                    .and_then(|expr| expr_at_expr(expr, filename, byte_offset))
            })
            .or_else(|| {
                stmt.step
                    .as_ref()
                    .and_then(|expr| expr_at_expr(expr, filename, byte_offset))
            })
            .or_else(|| block_expr_at(&stmt.body, filename, byte_offset)),
        TypedStmt::ForIn(stmt) => expr_at_expr(&stmt.iterable, filename, byte_offset)
            .or_else(|| block_expr_at(&stmt.body, filename, byte_offset)),
    }
}

fn expr_at_expr<'a>(
    expr: &'a TypedExpr,
    filename: &str,
    byte_offset: usize,
) -> Option<&'a TypedExpr> {
    let child = match expr {
        TypedExpr::Tuple(items, ..) | TypedExpr::Array(items, ..) => items
            .iter()
            .find_map(|item| expr_at_expr(item, filename, byte_offset)),
        TypedExpr::RecordLiteral { fields, .. } | TypedExpr::StructLiteral { fields, .. } => fields
            .iter()
            .find_map(|(_, value)| expr_at_expr(value, filename, byte_offset)),
        TypedExpr::RepeatArray(value, ..)
        | TypedExpr::UnaryOp(_, value, ..)
        | TypedExpr::RefTemp { init: value, .. }
        | TypedExpr::FieldAccess { object: value, .. }
        | TypedExpr::TupleAccess { object: value, .. }
        | TypedExpr::Cast { expr: value, .. }
        | TypedExpr::SingletonCoerce { inner: value, .. }
        | TypedExpr::DynCoerce { inner: value, .. } => expr_at_expr(value, filename, byte_offset),
        TypedExpr::BinOp(left, _, right, ..) => expr_at_expr(left, filename, byte_offset)
            .or_else(|| expr_at_expr(right, filename, byte_offset)),
        TypedExpr::Assign { target, value, .. } => place_expr_at(target, filename, byte_offset)
            .or_else(|| expr_at_expr(value, filename, byte_offset)),
        TypedExpr::Call { callee, args, .. } => expr_at_expr(callee, filename, byte_offset)
            .or_else(|| {
                args.iter()
                    .find_map(|arg| expr_at_expr(arg, filename, byte_offset))
            }),
        TypedExpr::MethodCall { receiver, args, .. } => {
            expr_at_expr(receiver, filename, byte_offset).or_else(|| {
                args.iter()
                    .find_map(|arg| expr_at_expr(arg, filename, byte_offset))
            })
        }
        TypedExpr::Index { object, index, .. } => expr_at_expr(object, filename, byte_offset)
            .or_else(|| expr_at_expr(index, filename, byte_offset)),
        TypedExpr::Match(match_expr) => expr_at_expr(&match_expr.scrutinee, filename, byte_offset)
            .or_else(|| {
                match_expr.arms.iter().find_map(|arm| {
                    arm.guard
                        .as_ref()
                        .and_then(|guard| expr_at_expr(guard, filename, byte_offset))
                        .or_else(|| block_expr_at(&arm.body, filename, byte_offset))
                })
            }),
        TypedExpr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => expr_at_expr(condition, filename, byte_offset)
            .or_else(|| block_expr_at(then_branch, filename, byte_offset))
            .or_else(|| {
                else_branch
                    .as_ref()
                    .and_then(|branch| block_expr_at(branch, filename, byte_offset))
            }),
        TypedExpr::Loop { body, .. } | TypedExpr::Closure { body, .. } => {
            block_expr_at(body, filename, byte_offset)
        }
        TypedExpr::Return(return_expr) => return_expr
            .value
            .as_deref()
            .and_then(|value| expr_at_expr(value, filename, byte_offset)),
        TypedExpr::Break(break_expr) => break_expr
            .value
            .as_deref()
            .and_then(|value| expr_at_expr(value, filename, byte_offset)),
        TypedExpr::Literal(..)
        | TypedExpr::Ident(..)
        | TypedExpr::Path(..)
        | TypedExpr::GenericClosure { .. }
        | TypedExpr::Continue(_) => None,
    };

    child.or_else(|| contains(expr.span(), filename, byte_offset).then_some(expr))
}

fn place_expr_at<'a>(
    place: &'a TypedPlace,
    filename: &str,
    byte_offset: usize,
) -> Option<&'a TypedExpr> {
    match place {
        TypedPlace::Deref { object, .. } => expr_at_expr(object, filename, byte_offset),
        TypedPlace::Field { object, .. } | TypedPlace::Tuple { object, .. } => {
            place_expr_at(object, filename, byte_offset)
        }
        TypedPlace::Index { object, index, .. } => place_expr_at(object, filename, byte_offset)
            .or_else(|| expr_at_expr(index, filename, byte_offset)),
        TypedPlace::Ident(_, _) => None,
    }
}

fn contains(span: &Span, filename: &str, byte_offset: usize) -> bool {
    span.filename == filename && span.start <= byte_offset && byte_offset < span.end
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::{analyze_virtual_root_with, AnalysisOptions};
    use crate::module_loader::InMemorySourceProvider;

    fn analysis(source: &str) -> crate::analysis::Analysis {
        let provider = InMemorySourceProvider::new("editor.mtl", source);
        analyze_virtual_root_with("editor.mtl", &provider, AnalysisOptions::default())
            .expect("test source should analyze")
    }

    #[test]
    fn expr_at_returns_the_innermost_typed_expression() {
        let source = "let value := 1 + 2;";
        let analysis = analysis(source);
        let offset = source.rfind('2').expect("literal is present");

        let expr = expr_at(&analysis.graph, "editor.mtl", offset).expect("typed expression");
        assert!(matches!(expr, TypedExpr::Literal(..)));
    }

    #[test]
    fn definition_at_resolves_a_top_level_identifier_reference() {
        let source = "fun answer() -> i64 { 42 } fun main() -> i64 { answer() }";
        let analysis = analysis(source);
        let offset = source.rfind("answer").expect("call is present");

        let definition = definition_at(&analysis.names, "editor.mtl", offset)
            .expect("top-level reference should resolve");
        assert_eq!(definition.span.filename, "editor.mtl");
        assert!(definition.span.start < offset);
    }
}
