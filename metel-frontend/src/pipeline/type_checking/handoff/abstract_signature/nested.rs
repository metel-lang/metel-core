//! The functions declared inside a definition's body (ADR-0068).
//!
//! A nested function sees none of the enclosing function's locals or type parameters (RFC-0195), so
//! it is analysed as a definition of its own, ahead of any instantiation of the enclosing generic.
//! This finds them: at any depth, through blocks, closures and other nested functions.

use crate::data::ast::{AssignTarget, Block, Decl, Expr, ForInit, FunDecl, Stmt};

/// Every function declared in `block`, outermost first, with the functions declared inside those
/// following them.
pub(in crate::pipeline::type_checking) fn nested_functions(block: &Block) -> Vec<&FunDecl> {
    let mut found = Vec::new();
    in_block(block, &mut found);
    found
}

fn in_block<'a>(block: &'a Block, found: &mut Vec<&'a FunDecl>) {
    for declaration in &block.stmts {
        in_declaration(declaration, found);
    }
    if let Some(tail) = &block.tail {
        in_expr(tail, found);
    }
}

fn in_declaration<'a>(declaration: &'a Decl, found: &mut Vec<&'a FunDecl>) {
    match declaration {
        Decl::Fun(function) => {
            found.push(function);
            in_block(&function.body, found);
        }
        Decl::Let(binding) => in_expr(&binding.value, found),
        Decl::Mut(binding) => in_expr(&binding.value, found),
        Decl::LetPattern(binding) => in_expr(&binding.value, found),
        Decl::Stmt(statement) => in_statement(statement, found),
        // A type, an `extend` block or an aspect inside a body holds no function that the
        // enclosing body declares for itself.
        Decl::Struct(_) | Decl::Enum(_) | Decl::Impl(_) | Decl::Aspect(_) | Decl::TypeAlias(_) => {}
    }
}

fn in_statement<'a>(statement: &'a Stmt, found: &mut Vec<&'a FunDecl>) {
    match statement {
        Stmt::Expr(expression) => in_expr(expression, found),
        Stmt::While(loop_stmt) => {
            in_expr(&loop_stmt.condition, found);
            in_block(&loop_stmt.body, found);
        }
        Stmt::For(loop_stmt) => {
            match &loop_stmt.init {
                Some(ForInit::Let(binding)) => in_expr(&binding.value, found),
                Some(ForInit::Mut(binding)) => in_expr(&binding.value, found),
                Some(ForInit::Expr(expression)) => in_expr(expression, found),
                None => {}
            }
            if let Some(condition) = &loop_stmt.condition {
                in_expr(condition, found);
            }
            if let Some(step) = &loop_stmt.step {
                in_expr(step, found);
            }
            in_block(&loop_stmt.body, found);
        }
        Stmt::ForIn(loop_stmt) => {
            in_expr(&loop_stmt.iterable, found);
            in_block(&loop_stmt.body, found);
        }
    }
}

// Exhaustive on purpose: an expression form added later that holds a block must be handled here, or
// a nested function inside it would silently go unanalysed.
fn in_expr<'a>(expression: &'a Expr, found: &mut Vec<&'a FunDecl>) {
    match expression {
        Expr::Literal(..)
        | Expr::Ident(..)
        | Expr::Path(..)
        | Expr::ResolvedPath { .. }
        | Expr::Continue(..)
        | Expr::RecordProjection { .. } => {}
        Expr::Tuple(items, _) | Expr::Array(items, _) => {
            for item in items {
                in_expr(item, found);
            }
        }
        Expr::RecordLiteral { fields, spread, .. } => {
            for (_, value) in fields {
                in_expr(value, found);
            }
            if let Some((value, _, _)) = spread {
                in_expr(value, found);
            }
        }
        Expr::StructLiteral { fields, .. } => {
            for (_, value) in fields {
                in_expr(value, found);
            }
        }
        Expr::RepeatArray(value, _, _)
        | Expr::UnaryOp(_, value, _)
        | Expr::Cast { expr: value, .. }
        | Expr::Ascribe { expr: value, .. }
        | Expr::PropagateError { expr: value, .. }
        | Expr::FieldAccess { object: value, .. }
        | Expr::TupleAccess { object: value, .. } => in_expr(value, found),
        Expr::BinOp(left, _, right, _)
        | Expr::Index {
            object: left,
            index: right,
            ..
        } => {
            in_expr(left, found);
            in_expr(right, found);
        }
        Expr::Assign { target, value, .. } => {
            in_target(target, found);
            in_expr(value, found);
        }
        Expr::Call { callee, args, .. } => {
            in_expr(callee, found);
            for argument in args {
                in_expr(argument, found);
            }
        }
        Expr::MethodCall { receiver, args, .. } => {
            in_expr(receiver, found);
            for argument in args {
                in_expr(argument, found);
            }
        }
        Expr::Match(matched) => {
            in_expr(&matched.scrutinee, found);
            for arm in &matched.arms {
                if let Some(guard) = &arm.guard {
                    in_expr(guard, found);
                }
                in_block(&arm.body, found);
            }
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            in_expr(condition, found);
            in_block(then_branch, found);
            if let Some(else_branch) = else_branch {
                in_block(else_branch, found);
            }
        }
        Expr::Loop { body, .. } | Expr::Closure { body, .. } => in_block(body, found),
        Expr::Return(returned) => {
            if let Some(value) = &returned.value {
                in_expr(value, found);
            }
        }
        Expr::Break(broken) => {
            if let Some(value) = &broken.value {
                in_expr(value, found);
            }
        }
    }
}

fn in_target<'a>(target: &'a AssignTarget, found: &mut Vec<&'a FunDecl>) {
    match target {
        AssignTarget::Ident(..) => {}
        AssignTarget::FieldAccess { object, .. }
        | AssignTarget::TupleAccess { object, .. }
        | AssignTarget::Deref { object, .. } => in_expr(object, found),
        AssignTarget::Index { object, index, .. } => {
            in_expr(object, found);
            in_expr(index, found);
        }
    }
}
