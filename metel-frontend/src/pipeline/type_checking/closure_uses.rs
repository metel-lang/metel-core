use crate::data::ast::{Expr, Span};

pub(super) fn capture_name(capture: &crate::data::ast::CaptureSpec) -> &str {
    match capture {
        crate::data::ast::CaptureSpec::Owned { name, .. }
        | crate::data::ast::CaptureSpec::SharedRef { name, .. }
        | crate::data::ast::CaptureSpec::MutRef { name, .. }
        | crate::data::ast::CaptureSpec::Clone { name, .. } => name,
    }
}

pub(super) fn collect_closure_body_uses(
    block: &crate::data::ast::Block,
    bound: &mut std::collections::BTreeSet<String>,
    reads: &mut std::collections::BTreeSet<String>,
    writes: &mut std::collections::BTreeSet<String>,
    spans: &mut std::collections::HashMap<String, Span>,
) {
    for decl in &block.stmts {
        match decl {
            crate::data::ast::Decl::Let(ld) => {
                collect_closure_expr_uses(&ld.value, bound, reads, writes, spans);
                bound.insert(ld.name.clone());
            }
            crate::data::ast::Decl::LetPattern(ld) => {
                collect_closure_expr_uses(&ld.value, bound, reads, writes, spans);
                if let crate::data::ast::Pattern::Record {
                    fields,
                    rest_binding,
                    ..
                } = &ld.pattern
                {
                    bound.extend(fields.iter().cloned());
                    if let Some((name, _)) = rest_binding {
                        bound.insert(name.clone());
                    }
                }
            }
            crate::data::ast::Decl::Mut(md) => {
                collect_closure_expr_uses(&md.value, bound, reads, writes, spans);
                bound.insert(md.name.clone());
            }
            crate::data::ast::Decl::Stmt(stmt) => {
                collect_closure_stmt_uses(stmt, bound, reads, writes, spans);
            }
            crate::data::ast::Decl::Fun(fun) => {
                bound.insert(fun.name.clone());
            }
            crate::data::ast::Decl::Struct(_)
            | crate::data::ast::Decl::Enum(_)
            | crate::data::ast::Decl::Impl(_)
            | crate::data::ast::Decl::Aspect(_)
            | crate::data::ast::Decl::TypeAlias(_) => {}
        }
    }
    if let Some(tail) = &block.tail {
        collect_closure_expr_uses(tail, bound, reads, writes, spans);
    }
}

fn collect_closure_stmt_uses(
    stmt: &crate::data::ast::Stmt,
    bound: &mut std::collections::BTreeSet<String>,
    reads: &mut std::collections::BTreeSet<String>,
    writes: &mut std::collections::BTreeSet<String>,
    spans: &mut std::collections::HashMap<String, Span>,
) {
    match stmt {
        crate::data::ast::Stmt::Expr(expr) => {
            collect_closure_expr_uses(expr, bound, reads, writes, spans);
        }
        crate::data::ast::Stmt::While(ws) => {
            collect_closure_expr_uses(&ws.condition, bound, reads, writes, spans);
            collect_closure_body_uses(&ws.body, &mut bound.clone(), reads, writes, spans);
        }
        crate::data::ast::Stmt::For(fs) => {
            let mut loop_bound = bound.clone();
            if let Some(init) = &fs.init {
                match init {
                    crate::data::ast::ForInit::Let(ld) => {
                        collect_closure_expr_uses(&ld.value, &mut loop_bound, reads, writes, spans);
                        loop_bound.insert(ld.name.clone());
                    }
                    crate::data::ast::ForInit::Mut(md) => {
                        collect_closure_expr_uses(&md.value, &mut loop_bound, reads, writes, spans);
                        loop_bound.insert(md.name.clone());
                    }
                    crate::data::ast::ForInit::Expr(expr) => {
                        collect_closure_expr_uses(expr, &mut loop_bound, reads, writes, spans);
                    }
                }
            }
            if let Some(condition) = &fs.condition {
                collect_closure_expr_uses(condition, &mut loop_bound, reads, writes, spans);
            }
            if let Some(step) = &fs.step {
                collect_closure_expr_uses(step, &mut loop_bound, reads, writes, spans);
            }
            collect_closure_body_uses(&fs.body, &mut loop_bound, reads, writes, spans);
        }
        crate::data::ast::Stmt::ForIn(fs) => {
            collect_closure_expr_uses(&fs.iterable, bound, reads, writes, spans);
            let mut loop_bound = bound.clone();
            loop_bound.insert(fs.binding.clone());
            collect_closure_body_uses(&fs.body, &mut loop_bound, reads, writes, spans);
        }
    }
}

fn collect_assign_target_uses(
    target: &crate::data::ast::AssignTarget,
    bound: &std::collections::BTreeSet<String>,
    reads: &mut std::collections::BTreeSet<String>,
    writes: &mut std::collections::BTreeSet<String>,
    spans: &mut std::collections::HashMap<String, Span>,
) {
    match target {
        crate::data::ast::AssignTarget::Ident(name, span) => {
            if !bound.contains(name) {
                writes.insert(name.clone());
                spans.entry(name.clone()).or_insert_with(|| span.clone());
            }
        }
        crate::data::ast::AssignTarget::FieldAccess { object, .. }
        | crate::data::ast::AssignTarget::TupleAccess { object, .. }
        | crate::data::ast::AssignTarget::Deref { object, .. } => {
            collect_closure_expr_uses(object, &mut bound.clone(), reads, writes, spans);
            if let crate::data::ast::Expr::Ident(name, ident_span) = object.as_ref()
                && !bound.contains(name)
            {
                writes.insert(name.clone());
                spans
                    .entry(name.clone())
                    .or_insert_with(|| ident_span.clone());
            }
        }
        crate::data::ast::AssignTarget::Index { object, index, .. } => {
            collect_closure_expr_uses(object, &mut bound.clone(), reads, writes, spans);
            collect_closure_expr_uses(index, &mut bound.clone(), reads, writes, spans);
            if let crate::data::ast::Expr::Ident(name, ident_span) = object.as_ref()
                && !bound.contains(name)
            {
                writes.insert(name.clone());
                spans
                    .entry(name.clone())
                    .or_insert_with(|| ident_span.clone());
            }
        }
    }
}

/// The identifier at the root of a field, tuple or index selector chain (`x`, `x.f`, `x.0`,
/// `x[i]`), with its span. A dereference ends the chain: the place behind a reference is
/// not the binding itself.
fn lvalue_root_ident(expr: &Expr) -> Option<(&String, &Span)> {
    match expr {
        Expr::Ident(name, span) => Some((name, span)),
        Expr::FieldAccess { object, .. }
        | Expr::TupleAccess { object, .. }
        | Expr::Index { object, .. } => lvalue_root_ident(object),
        _ => None,
    }
}

/// Walks an unlisted closure body's free-variable uses, alongside
/// `verify_closure_capture_list`'s existing `bound`/`reads`/`writes` sets:
/// `spans` records each free name's first reference span, so an implicit
/// (no `[...]` list) `Copy` capture can be resolved to its enclosing
/// binding's `LocalId` the same way an explicit capture-list entry already
/// is (metel-core#1096) — `ctx.local_binding_at` looks up exactly this kind
/// of ordinary reference span, no new identity-walk machinery needed.
// clippy-allow: closure body use walker keeps one exhaustive AST traversal table.
#[allow(clippy::too_many_lines)]
fn collect_closure_expr_uses(
    expr: &Expr,
    bound: &mut std::collections::BTreeSet<String>,
    reads: &mut std::collections::BTreeSet<String>,
    writes: &mut std::collections::BTreeSet<String>,
    spans: &mut std::collections::HashMap<String, Span>,
) {
    match expr {
        Expr::Ident(name, span) => {
            if !bound.contains(name) {
                reads.insert(name.clone());
                spans.entry(name.clone()).or_insert_with(|| span.clone());
            }
        }
        Expr::ResolvedPath { resolved, .. } => {
            if !bound.contains(resolved) {
                reads.insert(resolved.clone());
            }
        }
        Expr::Tuple(items, _) | Expr::Array(items, _) => {
            for item in items {
                collect_closure_expr_uses(item, bound, reads, writes, spans);
            }
        }
        Expr::StructLiteral { fields, .. } => {
            for (_, value) in fields {
                collect_closure_expr_uses(value, bound, reads, writes, spans);
            }
        }
        Expr::RecordProjection {
            path, path_span, ..
        } => {
            if let [name] = path.as_slice()
                && !bound.contains(name)
            {
                reads.insert(name.clone());
                spans
                    .entry(name.clone())
                    .or_insert_with(|| path_span.clone());
            }
        }
        Expr::RecordLiteral { fields, spread, .. } => {
            for (_, value) in fields {
                collect_closure_expr_uses(value, bound, reads, writes, spans);
            }
            if let Some((value, _, _)) = spread {
                collect_closure_expr_uses(value, bound, reads, writes, spans);
            }
        }
        // `&var x` (or `&var x.f`, `&var x[i]`) takes exclusive access to the binding, which
        // for a by-value capture is a write to the capture (legality-25).
        Expr::UnaryOp(crate::data::ast::UnaryOp::RefMut, value, _) => {
            collect_closure_expr_uses(value, bound, reads, writes, spans);
            if let Some((name, span)) = lvalue_root_ident(value)
                && !bound.contains(name)
            {
                writes.insert(name.clone());
                spans.entry(name.clone()).or_insert_with(|| span.clone());
            }
        }
        Expr::RepeatArray(value, _, _)
        | Expr::UnaryOp(_, value, _)
        | Expr::Cast { expr: value, .. }
        | Expr::Ascribe { expr: value, .. }
        | Expr::PropagateError { expr: value, .. } => {
            collect_closure_expr_uses(value, bound, reads, writes, spans);
        }
        Expr::BinOp(left, _, right, _)
        | Expr::Index {
            object: left,
            index: right,
            ..
        } => {
            collect_closure_expr_uses(left, bound, reads, writes, spans);
            collect_closure_expr_uses(right, bound, reads, writes, spans);
        }
        Expr::Assign { target, value, .. } => {
            collect_assign_target_uses(target, bound, reads, writes, spans);
            collect_closure_expr_uses(value, bound, reads, writes, spans);
        }
        Expr::Call { callee, args, .. } => {
            collect_closure_expr_uses(callee, bound, reads, writes, spans);
            for arg in args {
                collect_closure_expr_uses(arg, bound, reads, writes, spans);
            }
        }
        Expr::MethodCall { receiver, args, .. } => {
            collect_closure_expr_uses(receiver, bound, reads, writes, spans);
            for arg in args {
                collect_closure_expr_uses(arg, bound, reads, writes, spans);
            }
        }
        Expr::FieldAccess { object, .. } | Expr::TupleAccess { object, .. } => {
            collect_closure_expr_uses(object, bound, reads, writes, spans);
        }
        Expr::Match(m) => {
            collect_closure_expr_uses(&m.scrutinee, bound, reads, writes, spans);
            for arm in &m.arms {
                let mut arm_bound = bound.clone();
                collect_pattern_bindings(&arm.pattern, &mut arm_bound);
                if let Some(guard) = &arm.guard {
                    collect_closure_expr_uses(guard, &mut arm_bound, reads, writes, spans);
                }
                collect_closure_body_uses(&arm.body, &mut arm_bound, reads, writes, spans);
            }
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            collect_closure_expr_uses(condition, bound, reads, writes, spans);
            collect_closure_body_uses(then_branch, &mut bound.clone(), reads, writes, spans);
            if let Some(else_branch) = else_branch {
                collect_closure_body_uses(else_branch, &mut bound.clone(), reads, writes, spans);
            }
        }
        Expr::Loop { body, .. } => {
            collect_closure_body_uses(body, &mut bound.clone(), reads, writes, spans);
        }
        Expr::Return(ret) => {
            if let Some(value) = &ret.value {
                collect_closure_expr_uses(value, bound, reads, writes, spans);
            }
        }
        Expr::Break(brk) => {
            if let Some(value) = &brk.value {
                collect_closure_expr_uses(value, bound, reads, writes, spans);
            }
        }
        // A nested closure's own free variables cross *this* closure's
        // boundary too, transitively (metel-core#1096) — `n + x` inside an
        // inner closure, itself inside an outer implicit closure, still
        // needs `n` relayed through the outer one. An explicit inner list is
        // the contract of what crosses; without one, recurse into the inner
        // body as if inlined (minus its own params).
        Expr::Closure {
            captures: inner_captures,
            params: inner_params,
            body: inner_body,
            ..
        } => {
            if inner_captures.is_empty() {
                let mut inner_bound = bound.clone();
                inner_bound.extend(inner_params.iter().map(|p| p.name.clone()));
                collect_closure_body_uses(inner_body, &mut inner_bound, reads, writes, spans);
            } else {
                for capture in inner_captures {
                    let name = capture_name(capture);
                    if !bound.contains(name) {
                        reads.insert(name.to_string());
                        spans
                            .entry(name.to_string())
                            .or_insert_with(|| capture_span(capture).clone());
                    }
                }
            }
        }
        Expr::Literal(_, _) | Expr::Path(..) | Expr::Continue(_) => {}
    }
}

/// The free names a closure body consumes by value: a bare identifier in a position that takes
/// ownership of it, namely a block tail, a `let` initialiser, a call or method-call argument, a
/// `return` or `break` value, an assigned value, or an element of a tuple, array, record or struct
/// literal. Whether a name is a non-`Copy` capture is for the caller to say; legality-8 asks for
/// `once` only when it is.
pub(super) fn collect_consumed_names(
    block: &crate::data::ast::Block,
    bound: &mut std::collections::BTreeSet<String>,
    out: &mut Vec<(String, Span)>,
) {
    for decl in &block.stmts {
        match decl {
            crate::data::ast::Decl::Let(ld) => {
                consume(&ld.value, bound, out);
                bound.insert(ld.name.clone());
            }
            crate::data::ast::Decl::Mut(md) => {
                consume(&md.value, bound, out);
                bound.insert(md.name.clone());
            }
            crate::data::ast::Decl::LetPattern(ld) => {
                consume(&ld.value, bound, out);
                collect_pattern_bindings(&ld.pattern, bound);
            }
            crate::data::ast::Decl::Stmt(stmt) => stmt_consumed_names(stmt, bound, out),
            crate::data::ast::Decl::Fun(fun) => {
                bound.insert(fun.name.clone());
            }
            _ => {}
        }
    }
    if let Some(tail) = &block.tail {
        consume(tail, bound, out);
    }
}

fn stmt_consumed_names(
    stmt: &crate::data::ast::Stmt,
    bound: &mut std::collections::BTreeSet<String>,
    out: &mut Vec<(String, Span)>,
) {
    match stmt {
        crate::data::ast::Stmt::Expr(expr) => inner_consumed_names(expr, bound, out),
        crate::data::ast::Stmt::While(ws) => {
            inner_consumed_names(&ws.condition, bound, out);
            collect_consumed_names(&ws.body, &mut bound.clone(), out);
        }
        crate::data::ast::Stmt::For(fs) => {
            let mut loop_bound = bound.clone();
            match &fs.init {
                Some(crate::data::ast::ForInit::Let(ld)) => {
                    consume(&ld.value, &loop_bound, out);
                    loop_bound.insert(ld.name.clone());
                }
                Some(crate::data::ast::ForInit::Mut(md)) => {
                    consume(&md.value, &loop_bound, out);
                    loop_bound.insert(md.name.clone());
                }
                Some(crate::data::ast::ForInit::Expr(expr)) => {
                    inner_consumed_names(expr, &loop_bound, out);
                }
                None => {}
            }
            if let Some(condition) = &fs.condition {
                inner_consumed_names(condition, &loop_bound, out);
            }
            if let Some(step) = &fs.step {
                inner_consumed_names(step, &loop_bound, out);
            }
            collect_consumed_names(&fs.body, &mut loop_bound, out);
        }
        crate::data::ast::Stmt::ForIn(fs) => {
            inner_consumed_names(&fs.iterable, bound, out);
            let mut loop_bound = bound.clone();
            loop_bound.insert(fs.binding.clone());
            collect_consumed_names(&fs.body, &mut loop_bound, out);
        }
    }
}

/// `expr` sits where its value is taken: a bare free identifier is consumed.
fn consume(expr: &Expr, bound: &std::collections::BTreeSet<String>, out: &mut Vec<(String, Span)>) {
    match expr {
        Expr::Ident(name, span) if !bound.contains(name) => out.push((name.clone(), span.clone())),
        _ => inner_consumed_names(expr, bound, out),
    }
}

fn inner_consumed_names(
    expr: &Expr,
    bound: &std::collections::BTreeSet<String>,
    out: &mut Vec<(String, Span)>,
) {
    match expr {
        Expr::Tuple(items, _) | Expr::Array(items, _) => {
            for item in items {
                consume(item, bound, out);
            }
        }
        Expr::StructLiteral { fields, .. } => {
            for (_, value) in fields {
                consume(value, bound, out);
            }
        }
        Expr::RecordLiteral { fields, spread, .. } => {
            for (_, value) in fields {
                consume(value, bound, out);
            }
            if let Some((value, _, _)) = spread {
                consume(value, bound, out);
            }
        }
        Expr::Call { callee, args, .. } => {
            inner_consumed_names(callee, bound, out);
            for arg in args {
                consume(arg, bound, out);
            }
        }
        Expr::MethodCall { receiver, args, .. } => {
            inner_consumed_names(receiver, bound, out);
            for arg in args {
                consume(arg, bound, out);
            }
        }
        Expr::Assign { value, .. } => consume(value, bound, out),
        Expr::Return(ret) => {
            if let Some(value) = &ret.value {
                consume(value, bound, out);
            }
        }
        Expr::Break(brk) => {
            if let Some(value) = &brk.value {
                consume(value, bound, out);
            }
        }
        Expr::RepeatArray(value, _, _)
        | Expr::UnaryOp(_, value, _)
        | Expr::Cast { expr: value, .. }
        | Expr::Ascribe { expr: value, .. }
        | Expr::PropagateError { expr: value, .. }
        | Expr::FieldAccess { object: value, .. }
        | Expr::TupleAccess { object: value, .. } => inner_consumed_names(value, bound, out),
        Expr::BinOp(left, _, right, _) => {
            inner_consumed_names(left, bound, out);
            inner_consumed_names(right, bound, out);
        }
        Expr::Index { object, index, .. } => {
            inner_consumed_names(object, bound, out);
            inner_consumed_names(index, bound, out);
        }
        Expr::Match(m) => {
            inner_consumed_names(&m.scrutinee, bound, out);
            for arm in &m.arms {
                let mut arm_bound = bound.clone();
                collect_pattern_bindings(&arm.pattern, &mut arm_bound);
                if let Some(guard) = &arm.guard {
                    inner_consumed_names(guard, &arm_bound, out);
                }
                collect_consumed_names(&arm.body, &mut arm_bound, out);
            }
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            inner_consumed_names(condition, bound, out);
            collect_consumed_names(then_branch, &mut bound.clone(), out);
            if let Some(else_branch) = else_branch {
                collect_consumed_names(else_branch, &mut bound.clone(), out);
            }
        }
        Expr::Loop { body, .. } => collect_consumed_names(body, &mut bound.clone(), out),
        _ => {}
    }
}

fn collect_pattern_bindings(
    pattern: &crate::data::ast::Pattern,
    bound: &mut std::collections::BTreeSet<String>,
) {
    match pattern {
        crate::data::ast::Pattern::Binding(name, _) => {
            bound.insert(name.clone());
        }
        crate::data::ast::Pattern::Tuple(items, _) => {
            for item in items {
                collect_pattern_bindings(item, bound);
            }
        }
        crate::data::ast::Pattern::Array { elems, rest, .. } => {
            for item in elems {
                collect_pattern_bindings(item, bound);
            }
            if let Some((rest, _)) = rest {
                bound.insert(rest.clone());
            }
        }
        crate::data::ast::Pattern::EnumVariant { fields, .. }
        | crate::data::ast::Pattern::Struct { fields, .. } => {
            bound.extend(fields.iter().cloned());
        }
        crate::data::ast::Pattern::Record {
            fields,
            rest_binding,
            ..
        } => {
            bound.extend(fields.iter().cloned());
            if let Some((name, _)) = rest_binding {
                bound.insert(name.clone());
            }
        }
        crate::data::ast::Pattern::Wildcard(_) | crate::data::ast::Pattern::Literal(_, _) => {}
    }
}

pub(super) fn capture_span(capture: &crate::data::ast::CaptureSpec) -> &Span {
    match capture {
        crate::data::ast::CaptureSpec::Owned { span, .. }
        | crate::data::ast::CaptureSpec::SharedRef { span, .. }
        | crate::data::ast::CaptureSpec::MutRef { span, .. }
        | crate::data::ast::CaptureSpec::Clone { span, .. } => span,
    }
}

/// Legality-25: a write to a `[&x]` capture asks for `&var`.
pub(super) fn shared_ref_write_message(name: &str) -> String {
    format!("`{name}` is captured by shared reference; use `&var {name}`")
}

/// Legality-25: a write to a by-value capture asks for `var` on the closure.
pub(super) fn var_required_message(name: &str) -> String {
    format!(
        "closure writes captured `{name}`; write `var` (the closure then mutates \
         its own copy), stop mutating it, or share it with `[&var {name}]`"
    )
}

/// A write to a capture that legality-25 rejects, found while inferring the closure.
#[derive(Debug, Clone)]
pub struct CaptureWriteViolation {
    pub name: String,
    /// A write to a `[&x]` capture (`&var` is needed) rather than to a by-value one (`var` is).
    pub shared_ref: bool,
}

impl CaptureWriteViolation {
    pub(super) fn message(&self) -> String {
        if self.shared_ref {
            shared_ref_write_message(&self.name)
        } else {
            var_required_message(&self.name)
        }
    }
}

/// Legality-8: a closure that returns a by-value capture by value consumes its environment, which
/// the closure must say with `once`.
pub(super) fn once_required_message(name: &str) -> String {
    format!("closure consumes captured `{name}`; write `once`")
}

/// Legality-10: a `var` closure is called through an exclusive place, never through a shared `&`.
pub(super) const VAR_CALL_THROUGH_SHARED_REFERENCE: &str =
    "cannot call a `var` closure through a shared reference";
