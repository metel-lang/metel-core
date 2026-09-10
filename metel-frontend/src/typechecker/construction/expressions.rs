use super::{
    assign_target_to_typed_place, block_result_type, builtin_pattern_method_expr,
    check_fun_call_assoc_eq, check_fun_call_bounds, check_fun_call_neg_bounds,
    check_scheme_assoc_eq, check_scheme_bounds, check_scheme_neg_bounds,
    check_type_does_not_satisfy_bound, check_type_satisfies_bounds, construct_binop,
    construct_block, construct_call, construct_enum_literal_ty, construct_literal_type,
    construct_match, construct_method_args, construct_propagate_error, construct_unaryop,
    dispatch_for_resolved_method, find_loop_break_type, infer_type_to_type,
    instantiate_scheme_for_call, maybe_dyn_coerce, maybe_fn_move_coerce, maybe_read_copy,
    maybe_singleton_coerce, merge_branch_types, peel_type_references, resolve_expected_enum,
    resolve_generic_method_call, resolve_unqualified_variant_expr, resolved_to_type,
    type_chain_provides_mut_access, type_expr_to_infer_with_generics, type_to_infer,
    typed_place_ty, unqualified_variant_needs_annotation_error, AssignTarget, ConstructCtx, Expr,
    ForInit, HashMap, InferType, Literal, MetelError, MethodDispatch, Param, Span, Stmt,
    Substitution, Type, TypeErrorCode, TypeVar, TypedBreakExpr, TypedExpr, TypedForInStmt,
    TypedForInit, TypedForStmt, TypedLetDecl, TypedMutDecl, TypedReturnExpr, TypedStmt,
    TypedWhileStmt, UnaryOp,
};

fn capture_name(capture: &crate::ast::CaptureSpec) -> &str {
    match capture {
        crate::ast::CaptureSpec::Owned { name, .. }
        | crate::ast::CaptureSpec::SharedRef { name, .. }
        | crate::ast::CaptureSpec::MutRef { name, .. }
        | crate::ast::CaptureSpec::Clone { name, .. } => name,
    }
}

fn collect_closure_body_uses(
    block: &crate::ast::Block,
    bound: &mut std::collections::BTreeSet<String>,
    reads: &mut std::collections::BTreeSet<String>,
    writes: &mut std::collections::BTreeSet<String>,
) {
    for decl in &block.stmts {
        match decl {
            crate::ast::Decl::Let(ld) => {
                collect_closure_expr_uses(&ld.value, bound, reads, writes);
                bound.insert(ld.name.clone());
            }
            crate::ast::Decl::Mut(md) => {
                collect_closure_expr_uses(&md.value, bound, reads, writes);
                bound.insert(md.name.clone());
            }
            crate::ast::Decl::Stmt(stmt) => collect_closure_stmt_uses(stmt, bound, reads, writes),
            crate::ast::Decl::Fun(fun) => {
                bound.insert(fun.name.clone());
            }
            crate::ast::Decl::Struct(_)
            | crate::ast::Decl::Enum(_)
            | crate::ast::Decl::Impl(_)
            | crate::ast::Decl::Aspect(_)
            | crate::ast::Decl::TypeAlias(_) => {}
        }
    }
    if let Some(tail) = &block.tail {
        collect_closure_expr_uses(tail, bound, reads, writes);
    }
}

fn collect_closure_stmt_uses(
    stmt: &crate::ast::Stmt,
    bound: &mut std::collections::BTreeSet<String>,
    reads: &mut std::collections::BTreeSet<String>,
    writes: &mut std::collections::BTreeSet<String>,
) {
    match stmt {
        crate::ast::Stmt::Expr(expr) => collect_closure_expr_uses(expr, bound, reads, writes),
        crate::ast::Stmt::While(ws) => {
            collect_closure_expr_uses(&ws.condition, bound, reads, writes);
            collect_closure_body_uses(&ws.body, &mut bound.clone(), reads, writes);
        }
        crate::ast::Stmt::For(fs) => {
            let mut loop_bound = bound.clone();
            if let Some(init) = &fs.init {
                match init {
                    crate::ast::ForInit::Let(ld) => {
                        collect_closure_expr_uses(&ld.value, &mut loop_bound, reads, writes);
                        loop_bound.insert(ld.name.clone());
                    }
                    crate::ast::ForInit::Mut(md) => {
                        collect_closure_expr_uses(&md.value, &mut loop_bound, reads, writes);
                        loop_bound.insert(md.name.clone());
                    }
                    crate::ast::ForInit::Expr(expr) => {
                        collect_closure_expr_uses(expr, &mut loop_bound, reads, writes);
                    }
                }
            }
            if let Some(condition) = &fs.condition {
                collect_closure_expr_uses(condition, &mut loop_bound, reads, writes);
            }
            if let Some(step) = &fs.step {
                collect_closure_expr_uses(step, &mut loop_bound, reads, writes);
            }
            collect_closure_body_uses(&fs.body, &mut loop_bound, reads, writes);
        }
        crate::ast::Stmt::ForIn(fs) => {
            collect_closure_expr_uses(&fs.iterable, bound, reads, writes);
            let mut loop_bound = bound.clone();
            loop_bound.insert(fs.binding.clone());
            collect_closure_body_uses(&fs.body, &mut loop_bound, reads, writes);
        }
    }
}

fn collect_assign_target_uses(
    target: &crate::ast::AssignTarget,
    bound: &std::collections::BTreeSet<String>,
    reads: &mut std::collections::BTreeSet<String>,
    writes: &mut std::collections::BTreeSet<String>,
) {
    match target {
        crate::ast::AssignTarget::Ident(name, _) => {
            if !bound.contains(name) {
                writes.insert(name.clone());
            }
        }
        crate::ast::AssignTarget::FieldAccess { object, .. }
        | crate::ast::AssignTarget::TupleAccess { object, .. }
        | crate::ast::AssignTarget::Deref { object, .. } => {
            collect_closure_expr_uses(object, &mut bound.clone(), reads, writes);
            if let crate::ast::Expr::Ident(name, _) = object.as_ref() {
                if !bound.contains(name) {
                    writes.insert(name.clone());
                }
            }
        }
        crate::ast::AssignTarget::Index { object, index, .. } => {
            collect_closure_expr_uses(object, &mut bound.clone(), reads, writes);
            collect_closure_expr_uses(index, &mut bound.clone(), reads, writes);
            if let crate::ast::Expr::Ident(name, _) = object.as_ref() {
                if !bound.contains(name) {
                    writes.insert(name.clone());
                }
            }
        }
    }
}

// clippy-allow: closure body use walker keeps one exhaustive AST traversal table.
#[allow(clippy::too_many_lines)]
fn collect_closure_expr_uses(
    expr: &Expr,
    bound: &mut std::collections::BTreeSet<String>,
    reads: &mut std::collections::BTreeSet<String>,
    writes: &mut std::collections::BTreeSet<String>,
) {
    match expr {
        Expr::Ident(name, _) => {
            if !bound.contains(name) {
                reads.insert(name.clone());
            }
        }
        Expr::ResolvedPath { resolved, .. } => {
            if !bound.contains(resolved) {
                reads.insert(resolved.clone());
            }
        }
        Expr::Tuple(items, _) | Expr::Array(items, _) => {
            for item in items {
                collect_closure_expr_uses(item, bound, reads, writes);
            }
        }
        Expr::RecordLiteral { fields, .. } => {
            for (_, value) in fields {
                collect_closure_expr_uses(value, bound, reads, writes);
            }
        }
        Expr::RepeatArray(value, _, _)
        | Expr::UnaryOp(_, value, _)
        | Expr::Cast { expr: value, .. }
        | Expr::Ascribe { expr: value, .. }
        | Expr::PropagateError { expr: value, .. } => {
            collect_closure_expr_uses(value, bound, reads, writes);
        }
        Expr::BinOp(left, _, right, _)
        | Expr::Index {
            object: left,
            index: right,
            ..
        } => {
            collect_closure_expr_uses(left, bound, reads, writes);
            collect_closure_expr_uses(right, bound, reads, writes);
        }
        Expr::Assign { target, value, .. } => {
            collect_assign_target_uses(target, bound, reads, writes);
            collect_closure_expr_uses(value, bound, reads, writes);
        }
        Expr::Call { callee, args, .. } => {
            collect_closure_expr_uses(callee, bound, reads, writes);
            for arg in args {
                collect_closure_expr_uses(arg, bound, reads, writes);
            }
        }
        Expr::MethodCall { receiver, args, .. } => {
            collect_closure_expr_uses(receiver, bound, reads, writes);
            for arg in args {
                collect_closure_expr_uses(arg, bound, reads, writes);
            }
        }
        Expr::FieldAccess { object, .. } | Expr::TupleAccess { object, .. } => {
            collect_closure_expr_uses(object, bound, reads, writes);
        }
        Expr::Match(m) => {
            collect_closure_expr_uses(&m.scrutinee, bound, reads, writes);
            for arm in &m.arms {
                let mut arm_bound = bound.clone();
                collect_pattern_bindings(&arm.pattern, &mut arm_bound);
                if let Some(guard) = &arm.guard {
                    collect_closure_expr_uses(guard, &mut arm_bound, reads, writes);
                }
                collect_closure_body_uses(&arm.body, &mut arm_bound, reads, writes);
            }
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            collect_closure_expr_uses(condition, bound, reads, writes);
            collect_closure_body_uses(then_branch, &mut bound.clone(), reads, writes);
            if let Some(else_branch) = else_branch {
                collect_closure_body_uses(else_branch, &mut bound.clone(), reads, writes);
            }
        }
        Expr::Loop { body, .. } => {
            collect_closure_body_uses(body, &mut bound.clone(), reads, writes);
        }
        Expr::Return(ret) => {
            if let Some(value) = &ret.value {
                collect_closure_expr_uses(value, bound, reads, writes);
            }
        }
        Expr::Break(brk) => {
            if let Some(value) = &brk.value {
                collect_closure_expr_uses(value, bound, reads, writes);
            }
        }
        Expr::Closure { .. }
        | Expr::Literal(_, _)
        | Expr::Path(_, _)
        | Expr::StructLiteral { .. }
        | Expr::RecordProjection { .. }
        | Expr::Continue(_) => {}
    }
}

fn collect_pattern_bindings(
    pattern: &crate::ast::Pattern,
    bound: &mut std::collections::BTreeSet<String>,
) {
    match pattern {
        crate::ast::Pattern::Binding(name, _) => {
            bound.insert(name.clone());
        }
        crate::ast::Pattern::Tuple(items, _) => {
            for item in items {
                collect_pattern_bindings(item, bound);
            }
        }
        crate::ast::Pattern::Array { elems, rest, .. } => {
            for item in elems {
                collect_pattern_bindings(item, bound);
            }
            if let Some(rest) = rest {
                bound.insert(rest.clone());
            }
        }
        crate::ast::Pattern::EnumVariant { fields, .. }
        | crate::ast::Pattern::Struct { fields, .. }
        | crate::ast::Pattern::Record { fields, .. } => {
            bound.extend(fields.iter().cloned());
        }
        crate::ast::Pattern::Wildcard(_) | crate::ast::Pattern::Literal(_, _) => {}
    }
}

fn verify_closure_capture_list(
    capture_specs: &[crate::ast::CaptureSpec],
    call_multiplicity: crate::types::CallMultiplicity,
    call_mutation: crate::types::CallMutation,
    params: &[Param],
    body: &crate::ast::Block,
    span: &Span,
    ctx: &mut ConstructCtx,
) -> Result<(), MetelError> {
    verify_capture_specs(capture_specs, call_mutation, ctx)?;
    let mut bound: std::collections::BTreeSet<String> =
        params.iter().map(|param| param.name.clone()).collect();
    let mut reads = std::collections::BTreeSet::new();
    let mut writes = std::collections::BTreeSet::new();
    collect_closure_body_uses(body, &mut bound, &mut reads, &mut writes);
    let used: std::collections::BTreeSet<_> = reads.union(&writes).cloned().collect();
    let listed: std::collections::BTreeSet<_> = capture_specs
        .iter()
        .map(capture_name)
        .map(str::to_string)
        .collect();

    if capture_specs.is_empty() {
        for name in &used {
            let Some(ty) = ctx.lookup(name) else {
                continue;
            };
            if !ctx
                .registry
                .type_satisfies_aspect(ctx.current_module, ty, "Copy")
            {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0026,
                    format!("closure captures non-`Copy` `{name}`; add a capture list"),
                    span,
                ));
            }
        }
    } else {
        for name in &used {
            if ctx.lookup(name).is_some() && !listed.contains(name) {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0026,
                    format!("`{name}` is captured but not listed"),
                    span,
                ));
            }
        }
    }

    for capture in capture_specs {
        if let crate::ast::CaptureSpec::SharedRef { name, span } = capture {
            if writes.contains(name) {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0028,
                    format!("`{name}` is captured by shared reference; use `&var {name}`"),
                    span,
                ));
            }
        }
    }

    // A tail read of an owned non-Copy capture is returned by value, so it
    // consumes the environment field. RFC-0134 requires that capability to be
    // written as `once`; ordinary reads in non-consuming positions stay many.
    if call_multiplicity != crate::types::CallMultiplicity::Once {
        if let Some(crate::ast::Expr::Ident(name, _)) = body.tail.as_deref() {
            if capture_specs.iter().any(|capture| {
                matches!(capture, crate::ast::CaptureSpec::Owned { name: captured, .. } if captured == name)
            }) && ctx.lookup(name).is_some_and(|ty| {
                !ctx.registry.type_satisfies_aspect(ctx.current_module, ty, "Copy")
            }) {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0027,
                    format!("closure consumes captured `{name}`; write `once`"),
                    span,
                ));
            }
        }
    }

    if call_mutation != crate::types::CallMutation::Mutating {
        for name in &writes {
            if listed.contains(name) {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0028,
                    format!("closure writes captured `{name}`; write `var`"),
                    span,
                ));
            }
        }
    }

    Ok(())
}

fn verify_capture_specs(
    capture_specs: &[crate::ast::CaptureSpec],
    call_mutation: crate::types::CallMutation,
    ctx: &ConstructCtx,
) -> Result<(), MetelError> {
    for capture in capture_specs {
        if let crate::ast::CaptureSpec::MutRef { name, span } = capture {
            if ctx.lookup(name).is_none() {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0003,
                    format!("undefined variable `{name}`"),
                    span,
                ));
            }
            if !ctx.is_mutable(name) {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0028,
                    format!("`{name}` must be a `var` binding for a `&var` capture"),
                    span,
                ));
            }
            if call_mutation != crate::types::CallMutation::Mutating {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0028,
                    "a `&var` capture makes this closure `var`; write the `var` qualifier: `[...] var |...| { ... }`",
                    span,
                ));
            }
        }
        if matches!(
            capture,
            crate::ast::CaptureSpec::SharedRef { .. } | crate::ast::CaptureSpec::MutRef { .. }
        ) && ctx.is_enclosing_owned_capture(capture_name(capture))
        {
            return Err(MetelError::type_error(
                TypeErrorCode::T0030,
                format!(
                    "cannot borrow `{}` into an enclosing closure's environment",
                    capture_name(capture)
                ),
                capture_span(capture),
            ));
        }
    }
    Ok(())
}

fn capture_span(capture: &crate::ast::CaptureSpec) -> &Span {
    match capture {
        crate::ast::CaptureSpec::Owned { span, .. }
        | crate::ast::CaptureSpec::SharedRef { span, .. }
        | crate::ast::CaptureSpec::MutRef { span, .. }
        | crate::ast::CaptureSpec::Clone { span, .. } => span,
    }
}

// Exhaustive match over every AST/type-system variant; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
pub(super) fn construct_stmt(stmt: &Stmt, ctx: &mut ConstructCtx) -> Result<TypedStmt, MetelError> {
    match stmt {
        Stmt::Expr(e) => Ok(TypedStmt::Expr(construct_expr(e, None, ctx)?)),
        Stmt::While(ws) => {
            let condition = construct_expr(&ws.condition, None, ctx)?;
            ctx.enter_loop();
            let body = construct_block(&ws.body, None, ctx)?;
            ctx.exit_loop();
            Ok(TypedStmt::While(TypedWhileStmt {
                condition,
                body,
                span: ws.span.clone(),
            }))
        }
        Stmt::For(fs) => {
            ctx.push_scope();
            let init = match &fs.init {
                Some(ForInit::Let(ld)) => {
                    let expected_ty = ld
                        .type_ann
                        .as_ref()
                        .map(|ann| {
                            resolved_to_type(&ctx.type_expr_to_infer_ctx(ann), ctx.subst, &ld.span)
                        })
                        .transpose()?;
                    let value = construct_expr(&ld.value, expected_ty.as_ref(), ctx)?;
                    let value = match &expected_ty {
                        Some(t) => {
                            let value = maybe_read_copy(
                                t,
                                value,
                                &ld.span,
                                ctx.registry,
                                ctx.current_module,
                            )?;
                            let value = maybe_singleton_coerce(t, value, &ld.span, ctx.registry)?;
                            let value = maybe_dyn_coerce(t, value, &ld.span, ctx)?;
                            maybe_fn_move_coerce(t, value)
                        }
                        None => value,
                    };
                    let ty = expected_ty.unwrap_or_else(|| value.ty().clone());
                    ctx.bind(&ld.name, ty);
                    let typed_ld = TypedLetDecl {
                        name: ld.name.clone(),
                        type_ann: ld.type_ann.clone(),
                        value,
                        def_id: None,
                        span: ld.span.clone(),
                    };
                    Some(TypedForInit::Let(typed_ld))
                }
                Some(ForInit::Mut(md)) => {
                    let expected_ty = md
                        .type_ann
                        .as_ref()
                        .map(|ann| {
                            resolved_to_type(&ctx.type_expr_to_infer_ctx(ann), ctx.subst, &md.span)
                        })
                        .transpose()?;
                    let value = construct_expr(&md.value, expected_ty.as_ref(), ctx)?;
                    let value = match &expected_ty {
                        Some(t) => {
                            let value = maybe_read_copy(
                                t,
                                value,
                                &md.span,
                                ctx.registry,
                                ctx.current_module,
                            )?;
                            let value = maybe_singleton_coerce(t, value, &md.span, ctx.registry)?;
                            let value = maybe_dyn_coerce(t, value, &md.span, ctx)?;
                            maybe_fn_move_coerce(t, value)
                        }
                        None => value,
                    };
                    let ty = expected_ty.unwrap_or_else(|| value.ty().clone());
                    ctx.bind_mut(&md.name, ty);
                    let typed_md = TypedMutDecl {
                        name: md.name.clone(),
                        type_ann: md.type_ann.clone(),
                        value,
                        def_id: None,
                        span: md.span.clone(),
                    };
                    Some(TypedForInit::Mut(typed_md))
                }
                Some(ForInit::Expr(e)) => Some(TypedForInit::Expr(construct_expr(e, None, ctx)?)),
                None => None,
            };
            let condition = match &fs.condition {
                Some(c) => Some(construct_expr(c, None, ctx)?),
                None => None,
            };
            let step = match &fs.step {
                Some(s) => Some(construct_expr(s, None, ctx)?),
                None => None,
            };
            ctx.enter_loop();
            let body = construct_block(&fs.body, None, ctx)?;
            ctx.exit_loop();
            ctx.pop_scope();
            Ok(TypedStmt::For(Box::new(TypedForStmt {
                init,
                condition,
                step,
                body,
                span: fs.span.clone(),
            })))
        }
        Stmt::ForIn(fi) => {
            let iterable = construct_expr(&fi.iterable, None, ctx)?;
            let elem_ty = match peel_type_references(iterable.ty()) {
                Type::Array(elem) | Type::SizedArray(elem, _) => *elem.clone(),
                Type::Named(name, _) if name == "Range" => Type::I64,
                Type::Named(type_name, type_args) => {
                    // User-defined Iterable: derive elem type from next() -> Perhaps<T>.
                    // Concrete-impl method_env first; fall back to the polymorphic
                    // method_scheme_env (mirrors the method-call construction path
                    // above) for a generic struct implementing Iterable<T> generically
                    // -- e.g. `extend<T> Wrapper<T>: Iterable<T> { ... }` -- whose
                    // `next` is only registered there, not in method_env.
                    let next_ret = ctx
                        .method_env
                        .get(type_name.as_str())
                        .and_then(|m| m.get("next"))
                        .and_then(|ty| {
                            if let Type::Fun(_, ret, ..) = ty {
                                Some(ret.as_ref().clone())
                            } else {
                                None
                            }
                        })
                        .or_else(|| {
                            let (scheme, struct_tvars) =
                                ctx.registry.method_scheme_for(type_name.as_str(), "next")?;
                            let mut subst = Substitution::new();
                            for (&tv, concrete) in struct_tvars.iter().zip(type_args.iter()) {
                                subst.bind(tv, type_to_infer(concrete));
                            }
                            match subst.apply(&scheme.ty) {
                                InferType::Fun(_, ret, ..) => {
                                    let dummy = Span::new(0, 0, "");
                                    infer_type_to_type(&ret, &dummy).ok()
                                }
                                _ => None,
                            }
                        });
                    match next_ret {
                        Some(Type::Named(n, mut args)) if n == "Perhaps" && args.len() == 1 => {
                            args.remove(0)
                        }
                        _ => {
                            return Err(MetelError::internal(format!(
                                "for-in: `{type_name}` has no `next() -> Perhaps<T>` method"
                            )))
                        }
                    }
                }
                _ => return Err(MetelError::internal("for-in over non-iterable type")),
            };
            ctx.push_scope();
            ctx.bind(&fi.binding, elem_ty);
            ctx.enter_loop();
            let body = construct_block(&fi.body, None, ctx)?;
            ctx.exit_loop();
            ctx.pop_scope();
            Ok(TypedStmt::ForIn(Box::new(TypedForInStmt {
                binding: fi.binding.clone(),
                mutable: fi.mutable,
                iterable,
                body,
                span: fi.span.clone(),
            })))
        }
    }
}

// Exhaustive match over every AST/type-system variant; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
pub(super) fn construct_expr(
    expr: &Expr,
    expected_ty: Option<&Type>,
    ctx: &mut ConstructCtx,
) -> Result<TypedExpr, MetelError> {
    match expr {
        Expr::Literal(lit, span) => {
            let ty = construct_literal_type(lit, expected_ty, span)?;
            Ok(TypedExpr::Literal(lit.clone(), ty, span.clone()))
        }
        Expr::Ident(name, span) => {
            if let Some(ty) = ctx.lookup(name).cloned() {
                // RFC-0137 slice 2 (metel-core#858): a binding with a field moved
                // out reads at its narrowed residual type from that point on.
                let ty = ctx.narrowed_type(name).unwrap_or(ty);
                return Ok(TypedExpr::Ident(name.clone(), ty, span.clone()));
            }
            if let Some(fields) = ctx.get_struct_fields(name) {
                if fields.is_empty() {
                    let ty = if let Some(Type::Named(expected_name, _)) = expected_ty {
                        if expected_name == name {
                            expected_ty
                                .cloned()
                                .unwrap_or_else(|| Type::Named(name.clone(), vec![]))
                        } else {
                            Type::Named(name.clone(), vec![])
                        }
                    } else {
                        Type::Named(name.clone(), vec![])
                    };
                    return Ok(TypedExpr::StructLiteral {
                        path: vec![name.clone()],
                        fields: vec![],
                        ty,
                        type_id: ctx.type_symbol_id(name),
                        span: span.clone(),
                    });
                }
            }
            if ctx.can_be_unqualified_variant(name) {
                return resolve_unqualified_variant_expr(name, expected_ty, span, ctx);
            }
            // #736: `name` may be a real, checked declaration -- a generic
            // function's own scheme is deliberately kept out of `ctx.env`
            // (see the `GenericClosure` construction above for why: call
            // sites resolve it through `scheme_env` instead), so a bare,
            // non-call reference to it reaches here. It genuinely exists;
            // `undefined name` would be a lie. Generic functions are
            // call-only today (`functions.md`'s first-class-functions
            // carve-out; RFC-0138 proposes lifting this) -- say so instead.
            if let Some(scheme) = ctx.scheme_env.get(name.as_str()) {
                if !scheme.quantified_vars.is_empty() {
                    // metel-core#736 / RFC-0138 §4: a concrete expected type here
                    // (a higher-order call argument whose own parameter position is
                    // monomorphic, or an explicitly-annotated `let`) instantiates
                    // this one reference once, at this one use site -- rank-1, not
                    // let-polymorphism, so no `GenericClosure`/`fn_table` lookup is
                    // needed: `instantiate_scheme_for_call` (the same helper a
                    // direct call already uses) unifies `expected_ty`'s own param
                    // types against the scheme exactly as if they were argument
                    // types.
                    if let Some(Type::Fun(expected_params, ..)) = expected_ty {
                        let arity_matches = matches!(
                            &scheme.ty,
                            InferType::Fun(p, ..) if p.len() == expected_params.len()
                        );
                        if arity_matches {
                            let arg_types: Vec<&Type> = expected_params.iter().collect();
                            if let Ok((concrete, var_map)) = instantiate_scheme_for_call(
                                scheme,
                                &arg_types,
                                span,
                                &mut ctx.gen,
                                ctx.registry,
                                ctx.current_module,
                            ) {
                                check_fun_call_bounds(
                                    name,
                                    &var_map,
                                    span,
                                    ctx.registry,
                                    ctx.current_module,
                                )?;
                                check_scheme_bounds(
                                    name,
                                    scheme,
                                    &var_map,
                                    span,
                                    ctx.registry,
                                    ctx.current_module,
                                )?;
                                check_fun_call_assoc_eq(
                                    name,
                                    &var_map,
                                    span,
                                    ctx.registry,
                                    ctx.current_module,
                                )?;
                                check_scheme_assoc_eq(
                                    name,
                                    scheme,
                                    &var_map,
                                    span,
                                    ctx.registry,
                                    ctx.current_module,
                                )?;
                                check_fun_call_neg_bounds(
                                    name,
                                    &var_map,
                                    span,
                                    ctx.registry,
                                    ctx.current_module,
                                )?;
                                check_scheme_neg_bounds(
                                    name,
                                    scheme,
                                    &var_map,
                                    span,
                                    ctx.registry,
                                    ctx.current_module,
                                )?;
                                return Ok(TypedExpr::Ident(name.clone(), concrete, span.clone()));
                            }
                        }
                    }
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!(
                            "generic function `{name}` cannot be referenced except by \
                             direct call; a generic function is not yet a first-class \
                             value (RFC-0138)"
                        ),
                        span,
                    ));
                }
            }
            Err(MetelError::type_error(
                TypeErrorCode::T0003,
                format!("undefined name `{name}`"),
                span,
            ))
        }
        Expr::ResolvedPath {
            resolved,
            original,
            symbol_id: _,
            span,
        } => {
            let ty = ctx.lookup(resolved).cloned().ok_or_else(|| {
                MetelError::type_error(
                    TypeErrorCode::T0003,
                    format!("undefined name `{}`", original.join("::")),
                    span,
                )
            })?;
            Ok(TypedExpr::Ident(resolved.clone(), ty, span.clone()))
        }
        Expr::BinOp(lhs, op, rhs, span) => construct_binop(lhs, op, rhs, span, ctx),
        Expr::UnaryOp(op, operand, span) => {
            // For negation, propagate expected_ty to the operand so `-100` in
            // `let x: i8 = -100` resolves to i8. Unsigned targets are excluded:
            // negation of an unsigned value is a type error that must stay detectable.
            let inner_hint = if matches!(op, UnaryOp::Neg) {
                match expected_ty {
                    Some(Type::U8 | Type::U16 | Type::U32 | Type::U64) => None,
                    other => other,
                }
            } else {
                None
            };
            construct_unaryop(op, operand, span, inner_hint, ctx)
        }
        Expr::Tuple(elems, span) => {
            let typed: Vec<TypedExpr> = elems
                .iter()
                .map(|e| construct_expr(e, None, ctx))
                .collect::<Result<_, _>>()?;
            let ty = Type::Tuple(typed.iter().map(|e| e.ty().clone()).collect());
            Ok(TypedExpr::Tuple(typed, ty, span.clone()))
        }
        Expr::RecordLiteral { fields, span } => {
            let expected_record = match expected_ty {
                Some(Type::Record(fields)) => Some(fields),
                _ => None,
            };
            let mut typed_fields = Vec::with_capacity(fields.len());
            for (name, expr) in fields {
                let hint = expected_record.and_then(|expected_fields| {
                    expected_fields
                        .iter()
                        .find(|(expected_name, _)| expected_name == name)
                        .map(|(_, ty)| ty)
                });
                typed_fields.push((name.clone(), construct_expr(expr, hint, ctx)?));
            }
            let ty = expected_record.map_or_else(
                || {
                    Type::Record(
                        typed_fields
                            .iter()
                            .map(|(name, expr)| (name.clone(), expr.ty().clone()))
                            .collect(),
                    )
                },
                |expected_fields| Type::Record(expected_fields.clone()),
            );
            Ok(TypedExpr::RecordLiteral {
                fields: typed_fields,
                ty,
                span: span.clone(),
            })
        }
        Expr::Array(elems, span) => {
            if elems.is_empty() {
                let ty = expected_ty.cloned().ok_or_else(|| {
                    MetelError::type_error(
                        TypeErrorCode::T0002,
                        "cannot infer element type of empty array; add a type annotation",
                        span,
                    )
                })?;
                return Ok(TypedExpr::Array(vec![], ty, span.clone()));
            }
            // When the expected type is SizedArray, validate element count and use that type.
            if let Some(Type::SizedArray(expected_elem, n)) = expected_ty {
                if elems.len() as u64 != *n {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0001,
                        format!("expected array of {} element(s), got {}", n, elems.len()),
                        span,
                    ));
                }
                let typed: Vec<TypedExpr> = elems
                    .iter()
                    .map(|e| {
                        let typed = construct_expr(e, Some(expected_elem.as_ref()), ctx)?;
                        // RFC-0008 §6: an array element declared `dyn Aspect`
                        // needs the same coercion any other hinted site gets.
                        maybe_dyn_coerce(expected_elem.as_ref(), typed, e.span(), ctx)
                    })
                    .collect::<Result<_, _>>()?;
                let ty = Type::SizedArray(expected_elem.clone(), *n);
                return Ok(TypedExpr::Array(typed, ty, span.clone()));
            }
            // When expected type is Array(T), propagate element type hint.
            if let Some(Type::Array(expected_elem)) = expected_ty {
                let typed: Vec<TypedExpr> = elems
                    .iter()
                    .map(|e| {
                        let typed = construct_expr(e, Some(expected_elem.as_ref()), ctx)?;
                        maybe_dyn_coerce(expected_elem.as_ref(), typed, e.span(), ctx)
                    })
                    .collect::<Result<_, _>>()?;
                let ty = Type::Array(expected_elem.clone());
                return Ok(TypedExpr::Array(typed, ty, span.clone()));
            }
            let typed: Vec<TypedExpr> = elems
                .iter()
                .map(|e| construct_expr(e, None, ctx))
                .collect::<Result<_, _>>()?;
            let elem_ty = typed[0].ty().clone();
            let ty = Type::Array(Box::new(elem_ty));
            Ok(TypedExpr::Array(typed, ty, span.clone()))
        }
        Expr::RepeatArray(elem, n, span) => {
            let elem_hint: Option<&Type> = match expected_ty {
                Some(Type::SizedArray(elem_ty, _) | Type::Array(elem_ty)) => Some(elem_ty.as_ref()),
                _ => None,
            };
            let typed_elem = construct_expr(elem, elem_hint, ctx)?;
            let elem_ty = typed_elem.ty().clone();
            let ty = Type::SizedArray(Box::new(elem_ty), *n);
            Ok(TypedExpr::RepeatArray(
                Box::new(typed_elem),
                *n,
                ty,
                span.clone(),
            ))
        }
        Expr::Call {
            callee,
            type_args,
            args,
            span,
        } => {
            let call = construct_call(callee, type_args, args, span, expected_ty, ctx)?;
            // RFC-0137 slice 2: a by-value argument that is a partial move of a
            // struct field narrows the base binding from here on.
            if let TypedExpr::Call { args, .. } = &call {
                for arg in args {
                    ctx.note_consumed(arg);
                }
            }
            Ok(call)
        }
        Expr::Index {
            object,
            index,
            span,
        } => {
            let typed_obj = construct_expr(object, None, ctx)?;
            let typed_idx = construct_expr(index, Some(&Type::U64), ctx)?;
            if typed_idx.ty() != &Type::U64 {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0001,
                    format!(
                        "array index must be u64, got {}; use `expr as u64`",
                        typed_idx.ty()
                    ),
                    span,
                ));
            }
            if matches!(peel_type_references(typed_obj.ty()), Type::SizedArray(_, 0))
                && matches!(
                    index.as_ref(),
                    Expr::Literal(Literal::Int(_) | Literal::SizedInt { .. }, _)
                )
            {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0001,
                    "cannot index an empty fixed-size array with a literal index",
                    span,
                ));
            }
            let elem_ty = match peel_type_references(typed_obj.ty()) {
                Type::Array(elem) | Type::SizedArray(elem, _) => *elem.clone(),
                _ => {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0001,
                        "indexed value is not an array",
                        span,
                    ))
                }
            };
            Ok(TypedExpr::Index {
                object: Box::new(typed_obj),
                index: Box::new(typed_idx),
                ty: elem_ty,
                span: span.clone(),
            })
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            span,
        } => {
            let condition = construct_expr(condition, None, ctx)?;

            // metel-core#958: fork each arm's row-narrowing move state from the
            // pre-`if` state and join (union) afterward — Pass 2's counterpart of
            // the `Expr::If` fork/join in `inference/expressions.rs`.
            let entry_flow = ctx.flow.clone();
            let then_branch = construct_block(then_branch, expected_ty, ctx)?;
            let then_flow = std::mem::replace(&mut ctx.flow, entry_flow.clone());
            let mut joined_flow = entry_flow.clone();
            joined_flow.union_from(&then_flow);

            let (else_branch, ty) = match else_branch {
                Some(eb) => {
                    let typed_else = construct_block(eb, expected_ty, ctx)?;
                    joined_flow.union_from(&ctx.flow);
                    // RFC-0078: prefer whichever branch's type isn't `!` — a
                    // diverging branch (e.g. a `return`-only `then`) must not mask
                    // the other branch's real type; only `!` if both diverge.
                    let ty = merge_branch_types(&[
                        block_result_type(&then_branch),
                        block_result_type(&typed_else),
                    ]);
                    (Some(typed_else), ty)
                }
                None => (None, Type::Unit),
            };
            ctx.flow = joined_flow;
            Ok(TypedExpr::If {
                condition: Box::new(condition),
                then_branch,
                else_branch,
                ty,
                span: span.clone(),
            })
        }
        Expr::Assign {
            target,
            op,
            value,
            span,
        } => {
            // RFC-0110 §4.2: bare assignment to an identifier rebinds. The value's
            // expected type is simply the binding's own type — no peeling. Writing
            // through is spelled `*p = v` (AssignTarget::Deref), one `*` per layer.
            let value_hint: Option<Type> = match target {
                AssignTarget::Ident(name, _) => ctx.lookup(name).cloned(),
                AssignTarget::Deref { object, .. } => match construct_expr(object, None, ctx) {
                    Ok(o) => match o.ty() {
                        Type::MutReference(inner) => Some((**inner).clone()),
                        _ => None,
                    },
                    Err(_) => None,
                },
                _ => None,
            };
            let typed_value = construct_expr(value, value_hint.as_ref(), ctx)?;
            // RFC-0008 §6: reassigning an existing `dyn Aspect` binding needs
            // the same coercion its original `let`/`var` got.
            let typed_value = match &value_hint {
                Some(h) => maybe_dyn_coerce(h, typed_value, span, ctx)?,
                None => typed_value,
            };
            let typed_place = assign_target_to_typed_place(target, ctx)?;
            let _ = typed_place_ty(&typed_place, ctx, span)?;
            // RFC-0137 slice 2: the RHS may itself partially move a struct field
            // (`a.f := b.f`); then assigning `a.f` widens `a`'s type back by
            // reinitializing that place.
            ctx.note_consumed(&typed_value);
            ctx.note_reassigned(&typed_place);
            Ok(TypedExpr::Assign {
                target: typed_place,
                op: op.clone(),
                value: Box::new(typed_value),
                ty: Type::Unit,
                span: span.clone(),
            })
        }
        Expr::FieldAccess {
            object,
            field,
            span,
        } => {
            let typed_obj = construct_expr(object, None, ctx)?;
            let peeled = peel_type_references(typed_obj.ty());
            // RFC-0137 (metel-core#857): a Residual resolves field access exactly like
            // Record does -- directly from its own field list.
            if let Type::Record(fields) | Type::Residual { fields, .. } = peeled {
                let field_ty = fields
                    .iter()
                    .find(|(name, _)| name == field)
                    .map(|(_, ty)| ty.clone())
                    .ok_or_else(|| {
                        MetelError::internal(format!("no field `{field}` on {peeled}"))
                    })?;
                return Ok(TypedExpr::FieldAccess {
                    object: Box::new(typed_obj),
                    field: field.clone(),
                    ty: field_ty,
                    span: span.clone(),
                });
            }
            let (struct_name, type_args) = match peeled {
                Type::Named(name, args) => (name.clone(), args.clone()),
                t => {
                    return Err(MetelError::internal(format!(
                        "field access on non-struct type {t}"
                    )))
                }
            };
            let struct_id = ctx
                .registry
                .resolve_type_id(ctx.current_module, &struct_name);
            let field_ty = if let Some(type_params) =
                struct_id.and_then(|id| ctx.registry.raw_struct_type_params().get(&id))
            {
                // Generic struct: look up raw InferType field, build remap, apply, convert.
                let raw_fields = struct_id
                    .and_then(|id| ctx.registry.raw_struct_env().get(&id))
                    .ok_or_else(|| {
                        MetelError::internal(format!("missing raw fields for `{struct_name}`"))
                    })?;
                let raw_ty = raw_fields
                    .iter()
                    .find(|entry| entry.name == *field)
                    .map(|entry| entry.ty.clone())
                    .ok_or_else(|| {
                        MetelError::internal(format!("no field `{field}` on `{struct_name}`"))
                    })?;
                let mut remap = Substitution::new();
                for (&tp, arg) in type_params.iter().zip(type_args.iter()) {
                    remap.bind(tp, type_to_infer(arg));
                }
                infer_type_to_type(&remap.apply(&raw_ty), span)?
            } else {
                ctx.get_struct_fields(&struct_name)
                    .and_then(|fs| fs.iter().find(|(name, _, _)| name == field))
                    .map(|(_, ty, _)| ty.clone())
                    .ok_or_else(|| {
                        MetelError::internal(format!("no field `{field}` on `{struct_name}`"))
                    })?
            };
            Ok(TypedExpr::FieldAccess {
                object: Box::new(typed_obj),
                field: field.clone(),
                ty: field_ty,
                span: span.clone(),
            })
        }
        Expr::MethodCall {
            receiver,
            method,
            type_args,
            args,
            span,
        } => {
            let typed_receiver = construct_expr(receiver, None, ctx)?;
            // Peel references before the builtin-pattern gate, matching what the
            // scheme-based path below already does and what
            // `builtin_pattern_method_expr` itself checks. Without this, `.len()`
            // on a `&T[]` fell past the builtin and into the scheme lookup, which
            // has no entry for it, so the diagnostic claimed the method did not
            // exist on arrays at all (#314).
            //
            // `args.is_empty()` guards the *construction* below, not the builtin
            // match: every builtin pattern is nullary, so a call with arguments can
            // never match one, and constructing its arguments here only to discard
            // them advances `ctx.gen` — the shared TypeVar generator — a second
            // time before the real path constructs them again. That shifts `?tN`
            // numbering for everything downstream (#307).
            if args.is_empty()
                && matches!(
                    peel_type_references(typed_receiver.ty()),
                    Type::Array(_) | Type::SizedArray(_, _)
                )
            {
                let typed_args: Vec<TypedExpr> = args
                    .iter()
                    .map(|arg| construct_expr(arg, None, ctx))
                    .collect::<Result<_, _>>()?;
                if let Some(result) =
                    builtin_pattern_method_expr(typed_receiver.clone(), method, typed_args, span)
                {
                    return result;
                }
            }
            // Resolve explicit method type args once.
            let explicit_method_tys: Option<Vec<Type>> = if type_args.is_empty() {
                None
            } else {
                Some(
                    type_args
                        .iter()
                        .map(|te| infer_type_to_type(&ctx.type_expr_to_infer_ctx(te), span))
                        .collect::<Result<_, _>>()?,
                )
            };

            // Resolve the method's function type and construct the arguments.
            if let Type::Array(elem) | Type::SizedArray(elem, _) =
                peel_type_references(typed_receiver.ty())
            {
                let candidates = ctx
                    .registry
                    .array_method_scheme_variants_for(method)
                    .to_vec();
                if candidates.is_empty() {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!("no method `{method}` on array type"),
                        span,
                    ));
                }
                let receiver_type_args = [elem.as_ref().clone()];
                let (method_fun_ty, typed_args, winning_aspect) = resolve_generic_method_call(
                    &candidates,
                    &receiver_type_args,
                    explicit_method_tys.as_deref(),
                    args,
                    method,
                    span,
                    ctx,
                )?;
                if matches!(
                    ctx.registry.array_method_receiver_kind(method),
                    Some(crate::ast::ReceiverKind::RefMut)
                ) && !type_chain_provides_mut_access(typed_receiver.ty())
                {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0008,
                        format!(
                            "cannot call `&var self` method `{method}` through shared receiver"
                        ),
                        span,
                    ));
                }
                let ret_ty = match method_fun_ty {
                    Type::Fun(_, ret, ..) => *ret,
                    _ => return Err(MetelError::internal("array method type is not a function")),
                };
                let dispatch = dispatch_for_resolved_method(ctx, winning_aspect.as_deref());
                return Ok(TypedExpr::MethodCall {
                    receiver: Box::new(typed_receiver),
                    method: method.clone(),
                    args: typed_args,
                    ty: ret_ty,
                    dispatch,
                    span: span.clone(),
                });
            }

            if matches!(peel_type_references(typed_receiver.ty()), Type::Never) {
                // Receiver's type is unknowable -- e.g. `construct_generic_body`'s
                // call-time reconstruction sampling an empty collection's element
                // type (issue #271), or a genuinely diverging receiver expression.
                // Either way nothing here actually runs, but construction must
                // still produce a valid typed node: skip static method resolution
                // and defer to runtime dynamic dispatch, which resolves by the
                // receiver's real value/kind (see `eval_method_call_expr`), not by
                // this placeholder type.
                let typed_args = args
                    .iter()
                    .map(|a| construct_expr(a, None, ctx))
                    .collect::<Result<_, _>>()?;
                return Ok(TypedExpr::MethodCall {
                    receiver: Box::new(typed_receiver),
                    method: method.clone(),
                    args: typed_args,
                    ty: Type::Never,
                    dispatch: crate::typed_ast::MethodDispatch::Dynamic,
                    span: span.clone(),
                });
            }
            // `dyn Aspect` receiver (RFC-0008 slice 2): mirrors the bounded-TypeVar
            // slow path Pass 1 already has (`inference.rs`'s own `InferType::Dyn`
            // arm) but working in concrete `Type`s, the way Pass 2 construction
            // does everywhere else. Object safety already guarantees no `Self`/
            // associated type outside receiver position, so the only substitution
            // needed is the aspect's own generic params against this `dyn
            // Aspect`'s type args. `dispatch: MethodDispatch::Dynamic` here is
            // deliberate, not a placeholder to fix later — elaboration (a later,
            // separate pass) resolves it to `Aspect { aspect_id }` by inspecting
            // the receiver's own `Type::Dyn`, the same way the concrete-struct
            // fast path below defers to elaboration too.
            if let Type::Dyn { aspect, type_args } = peel_type_references(typed_receiver.ty()) {
                let aspect = aspect.clone();
                let type_args = type_args.clone();
                let method_def = ctx
                    .registry
                    .aspect_method_defs_in(ctx.current_module, &aspect)
                    .and_then(|methods| methods.iter().find(|m| m.name == *method).cloned())
                    .ok_or_else(|| {
                        MetelError::type_error(
                            TypeErrorCode::T0003,
                            format!("no method `{method}` on `dyn {aspect}`"),
                            span,
                        )
                    })?;

                let aspect_generics = ctx
                    .registry
                    .aspect_generics_in(ctx.current_module, &aspect)
                    .cloned()
                    .unwrap_or_default();
                let mut local_subst = Substitution::new();
                let mut generics_map: HashMap<String, TypeVar> = HashMap::new();
                for (name, arg_ty) in aspect_generics.iter().zip(type_args.iter()) {
                    let tv = ctx.gen.fresh();
                    generics_map.insert(name.clone(), tv);
                    local_subst.bind(tv, type_to_infer(arg_ty));
                }

                let declared_params: Vec<&Param> = method_def
                    .params
                    .iter()
                    .filter(|p| p.name != "self")
                    .collect();
                if args.len() != declared_params.len() {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0004,
                        format!(
                            "`{aspect}::{method}` expects {} argument(s), got {}",
                            declared_params.len(),
                            args.len()
                        ),
                        span,
                    ));
                }
                let mut typed_args = Vec::with_capacity(args.len());
                for (arg_expr, param) in args.iter().zip(declared_params.iter()) {
                    let expected = param
                        .type_ann
                        .as_ref()
                        .map(|ann| {
                            let infer_ty = type_expr_to_infer_with_generics(ann, &generics_map);
                            resolved_to_type(&infer_ty, &local_subst, span)
                        })
                        .transpose()?;
                    typed_args.push(construct_expr(arg_expr, expected.as_ref(), ctx)?);
                }

                // No mutable-access guard here, unlike the array fast path
                // below: Pass 1 (`inference.rs`'s own `InferType::Dyn` arm)
                // already checked this, with the binding-mutability fallback
                // (`lookup_for_write`) for a bare owned receiver that the
                // array path's simpler `type_chain_provides_mut_access`-only
                // check doesn't have -- mirroring the concrete-struct fast
                // path just below, which likewise trusts Pass 1 and re-checks
                // nothing here.
                let ret_ty = match &method_def.return_type {
                    Some(rt) => {
                        let infer_ty = type_expr_to_infer_with_generics(rt, &generics_map);
                        resolved_to_type(&infer_ty, &local_subst, span)?
                    }
                    None => Type::Unit,
                };

                return Ok(TypedExpr::MethodCall {
                    receiver: Box::new(typed_receiver),
                    method: method.clone(),
                    args: typed_args,
                    ty: ret_ty,
                    dispatch: MethodDispatch::Dynamic,
                    span: span.clone(),
                });
            }

            let (struct_name, receiver_type_args) = match peel_type_references(typed_receiver.ty())
            {
                Type::Named(name, targs) => (name.clone(), targs.clone()),
                t => match super::super::inference::primitive_type_name(t) {
                    Some(name) => (name, vec![]),
                    None => {
                        return Err(MetelError::internal(format!(
                            "method call on non-struct type {t}"
                        )))
                    }
                },
            };

            // Resolve the method's function type and construct the arguments.
            // Two cases: a concrete method already in method_env (fast path), or a
            // polymorphic scheme on a generic struct/enum (slow path).
            let (method_fun_ty, typed_args, dispatch): (Type, Vec<TypedExpr>, MethodDispatch) =
                if let Some(ty) = ctx
                    .method_env
                    .get(&struct_name)
                    .and_then(|m| m.get(method.as_str()))
                    .cloned()
                {
                    if explicit_method_tys.is_some() {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0004,
                            format!("method `{method}` on `{struct_name}` has no type parameters"),
                            span,
                        ));
                    }
                    let typed_args = construct_method_args(&ty, args, ctx)?;
                    (ty, typed_args, MethodDispatch::Dynamic)
                } else {
                    // Slow path: method on a generic struct/enum — look up the polymorphic
                    // scheme(s) and instantiate against the receiver's concrete type
                    // arguments. More than one candidate can be registered here (issue
                    // #272: different aspects providing the same method name for the
                    // same generic target) -- try each and use the one whose bounds the
                    // receiver's concrete type args actually satisfy.
                    let candidates = ctx
                        .registry
                        .method_scheme_variants_for(&struct_name, method)
                        .to_vec();
                    if candidates.is_empty() {
                        return Err(MetelError::internal(format!(
                            "no method `{method}` on `{struct_name}`"
                        )));
                    }
                    let (ty, typed_args, winning_aspect) = resolve_generic_method_call(
                        &candidates,
                        &receiver_type_args,
                        explicit_method_tys.as_deref(),
                        args,
                        method,
                        span,
                        ctx,
                    )?;
                    let dispatch = dispatch_for_resolved_method(ctx, winning_aspect.as_deref());
                    (ty, typed_args, dispatch)
                };
            let ret_ty = match method_fun_ty {
                Type::Fun(_, ret, ..) => *ret,
                _ => return Err(MetelError::internal("method type is not a function")),
            };
            Ok(TypedExpr::MethodCall {
                receiver: Box::new(typed_receiver),
                method: method.clone(),
                args: typed_args,
                ty: ret_ty,
                dispatch,
                span: span.clone(),
            })
        }
        Expr::StructLiteral {
            path,
            fields,
            symbol_id,
            span,
        } => {
            let resolved_path = if path.len() == 1
                && ctx.can_be_unqualified_variant(&path[0])
                && !ctx.has_struct_named(&path[0])
            {
                let expected_ty = expected_ty
                    .ok_or_else(|| unqualified_variant_needs_annotation_error(&path[0], span))?;
                let (enum_name, enum_info) = resolve_expected_enum(Some(expected_ty), span, ctx)?;
                if enum_info
                    .variants
                    .iter()
                    .any(|variant| variant.name == path[0])
                {
                    vec![enum_name.clone(), path[0].clone()]
                } else {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0001,
                        format!("cannot unify `{}` with `{expected_ty}`", path[0]),
                        span,
                    ));
                }
            } else {
                path.clone()
            };
            // Look up field type hints from the struct definition for non-generic structs.
            // Clone to release the borrow on ctx before calling construct_expr below.
            let type_name = resolved_path.last().map_or("", std::string::String::as_str);
            let field_hints: HashMap<String, Type> = ctx
                .get_struct_fields(type_name)
                .map(|fs| fs.iter().map(|(n, t, _)| (n.clone(), t.clone())).collect())
                .unwrap_or_default();
            let typed_fields: Vec<(String, TypedExpr)> = fields
                .iter()
                .map(|(name, expr)| {
                    let hint = field_hints.get(name.as_str());
                    let typed = construct_expr(expr, hint, ctx)?;
                    // RFC-0008 §6: a struct field declared `dyn Aspect` needs
                    // the same coercion any other hinted site gets.
                    let typed = match hint {
                        Some(h) => maybe_dyn_coerce(h, typed, expr.span(), ctx)?,
                        None => typed,
                    };
                    Ok((name.clone(), typed))
                })
                .collect::<Result<_, _>>()?;

            let ty = if resolved_path.len() == 2 {
                construct_enum_literal_ty(
                    &resolved_path[0],
                    &resolved_path[1],
                    &typed_fields,
                    expected_ty,
                    span,
                    ctx,
                )?
            } else {
                let type_name = resolved_path.last().unwrap();
                let type_id = ctx.registry.resolve_type_id(ctx.current_module, type_name);
                if let Some(type_params) =
                    type_id.and_then(|id| ctx.registry.raw_struct_type_params().get(&id))
                {
                    // Generic struct: infer type args from the typed field values.
                    let raw_fields = type_id
                        .and_then(|id| ctx.registry.raw_struct_env().get(&id))
                        .ok_or_else(|| {
                            MetelError::internal(format!("missing raw fields for `{type_name}`"))
                        })?;
                    let mut remap: HashMap<TypeVar, InferType> = HashMap::new();
                    for &tp in type_params {
                        remap.entry(tp).or_insert_with(|| InferType::Var(tp));
                    }
                    // Match each field value type to its raw InferType param; resolve via subst.
                    for (fname, fexpr) in &typed_fields {
                        if let Some(field) = raw_fields.iter().find(|entry| entry.name == *fname) {
                            if let InferType::Var(v) = &field.ty {
                                if type_params.contains(v) {
                                    remap.insert(*v, type_to_infer(fexpr.ty()));
                                }
                            }
                        }
                    }
                    let type_args: Vec<Type> = type_params
                        .iter()
                        .map(|tp| {
                            let it = remap.get(tp).cloned().unwrap_or(InferType::Var(*tp));
                            infer_type_to_type(&ctx.subst.apply(&it), span)
                        })
                        .collect::<Result<_, _>>()?;
                    // T0012: check each resolved type arg satisfies the declared bounds.
                    let generic_types_by_name: HashMap<String, Type> = ctx
                        .registry
                        .struct_generic_names_for(ctx.current_module, type_name)
                        .into_iter()
                        .flatten()
                        .cloned()
                        .zip(type_args.iter().cloned())
                        .collect();
                    let record_kinds = ctx
                        .get_type_param_record_kinds(type_name)
                        .cloned()
                        .unwrap_or_else(|| vec![false; type_args.len()]);
                    if let Some(param_bounds) = ctx
                        .registry
                        .type_param_bounds_for(ctx.current_module, type_name)
                    {
                        for (i, bounds) in param_bounds.iter().enumerate() {
                            let record_kind = record_kinds.get(i).copied().unwrap_or(false);
                            if bounds.is_empty() && !record_kind {
                                continue;
                            }
                            let Some(arg) = type_args.get(i) else {
                                continue;
                            };
                            check_type_satisfies_bounds(
                                arg,
                                bounds,
                                record_kind,
                                type_name,
                                span,
                                ctx.registry,
                                ctx.current_module,
                                &generic_types_by_name,
                            )?;
                        }
                    }
                    // T0012 negative bounds: check each resolved type arg does NOT
                    // implement the declared negative bounds (RFC-0072, issue #243).
                    if let Some(neg_param_bounds) = ctx
                        .registry
                        .neg_type_param_bounds_for(ctx.current_module, type_name)
                    {
                        for (i, neg_bounds) in neg_param_bounds.iter().enumerate() {
                            let record_kind = record_kinds.get(i).copied().unwrap_or(false);
                            if neg_bounds.is_empty() && !record_kind {
                                continue;
                            }
                            let Some(arg) = type_args.get(i) else {
                                continue;
                            };
                            check_type_does_not_satisfy_bound(
                                arg,
                                neg_bounds,
                                record_kind,
                                type_name,
                                span,
                                ctx.registry,
                                ctx.current_module,
                                &generic_types_by_name,
                            )?;
                        }
                    }
                    Type::Named(type_name.clone(), type_args)
                } else {
                    Type::Named(type_name.clone(), vec![])
                }
            };

            // Resolve the constructed type's stable identity. A module-qualified
            // literal carries its resolver-stamped id (correct across modules with
            // same-named types); otherwise derive it from the declaring-module index
            // (struct name, or the enum name for a 2-segment `Enum::Variant` literal).
            let type_id = symbol_id.or_else(|| {
                if resolved_path.len() == 2 {
                    ctx.type_symbol_id(&resolved_path[0])
                } else {
                    ctx.type_symbol_id(resolved_path.last().unwrap())
                }
            });

            Ok(TypedExpr::StructLiteral {
                path: resolved_path,
                fields: typed_fields,
                ty,
                type_id,
                span: span.clone(),
            })
        }
        Expr::RecordProjection { path, fields, span } => {
            let base_expr = if path.len() == 1 {
                Expr::Ident(path[0].clone(), span.clone())
            } else {
                Expr::Path(path.clone(), span.clone())
            };
            let typed_base = construct_expr(&base_expr, None, ctx)?;
            let (struct_name, type_args) = match peel_type_references(typed_base.ty()) {
                Type::Named(name, args) => (name.clone(), args.clone()),
                // RFC-0137 slice 2: re-projecting a narrowed residual, as long as
                // every named field is still in its current row.
                Type::Residual {
                    brand,
                    fields: res_fields,
                } => {
                    for field in fields {
                        if !res_fields.iter().any(|(n, _)| n == field) {
                            return Err(MetelError::type_error(
                                TypeErrorCode::T0003,
                                format!(
                                    "field `{field}` was moved out of this `{brand}` and cannot be projected"
                                ),
                                span,
                            ));
                        }
                    }
                    (brand.clone(), Vec::new())
                }
                other => {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0002,
                        format!("record projection requires a nominal struct value, got {other}"),
                        span,
                    ))
                }
            };
            let mut projected_fields = Vec::with_capacity(fields.len());
            let mut record_ty = Vec::with_capacity(fields.len());
            // RFC-0137 (metel-core#857): the struct's own total declared field count,
            // captured once, decides whether this projection is full-width -- a
            // full-width projection normalizes to the plain struct type instead of a
            // branded Residual (§3's own worked example: naming every field is still
            // just the struct, not a distinct form).
            let mut total_field_count: Option<usize> = None;
            let struct_id = ctx
                .registry
                .resolve_type_id(ctx.current_module, &struct_name);
            for field in fields {
                let field_ty = if let Some(type_params) =
                    struct_id.and_then(|id| ctx.registry.raw_struct_type_params().get(&id))
                {
                    let raw_fields = struct_id
                        .and_then(|id| ctx.registry.raw_struct_env().get(&id))
                        .ok_or_else(|| {
                            MetelError::internal(format!("missing raw fields for `{struct_name}`"))
                        })?;
                    total_field_count.get_or_insert(raw_fields.len());
                    let raw_ty = raw_fields
                        .iter()
                        .find(|entry| entry.name == *field)
                        .map(|entry| entry.ty.clone())
                        .ok_or_else(|| {
                            MetelError::type_error(
                                TypeErrorCode::T0003,
                                format!("no field `{field}` on `{struct_name}`"),
                                span,
                            )
                        })?;
                    let mut remap = Substitution::new();
                    for (&tp, arg) in type_params.iter().zip(type_args.iter()) {
                        remap.bind(tp, type_to_infer(arg));
                    }
                    infer_type_to_type(&remap.apply(&raw_ty), span)?
                } else {
                    let entries = ctx.get_struct_fields(&struct_name);
                    total_field_count.get_or_insert(entries.map_or(0, Vec::len));
                    entries
                        .and_then(|entries| entries.iter().find(|(name, _, _)| name == field))
                        .map(|(_, ty, _)| ty.clone())
                        .ok_or_else(|| {
                            MetelError::type_error(
                                TypeErrorCode::T0003,
                                format!("no field `{field}` on `{struct_name}`"),
                                span,
                            )
                        })?
                };
                record_ty.push((field.clone(), field_ty.clone()));
                projected_fields.push((
                    field.clone(),
                    TypedExpr::FieldAccess {
                        object: Box::new(typed_base.clone()),
                        field: field.clone(),
                        ty: field_ty,
                        span: span.clone(),
                    },
                ));
            }
            let ty = if total_field_count == Some(record_ty.len()) {
                Type::Named(struct_name.clone(), type_args.clone())
            } else {
                // `Residual::fields` is always lexicographically sorted (mirrors
                // `Record`'s own invariant), regardless of the projection's written order.
                record_ty.sort_by(|(a, _), (b, _)| a.cmp(b));
                Type::Residual {
                    brand: struct_name.clone(),
                    fields: record_ty,
                }
            };
            Ok(TypedExpr::RecordLiteral {
                fields: projected_fields,
                ty,
                span: span.clone(),
            })
        }
        Expr::Path(segments, span) => {
            // For 2-segment paths, try method_env first (static methods, enum variant constructors).
            if let [type_name, member_name] = segments.as_slice() {
                if let Some(ty) = ctx
                    .method_env
                    .get(type_name.as_str())
                    .and_then(|m| m.get(member_name.as_str()))
                    .cloned()
                {
                    return Ok(TypedExpr::Path(segments.clone(), ty, span.clone()));
                }
                // Also check enum variants via enum_env.
                if let Some(info) = ctx
                    .registry
                    .enum_info(ctx.current_module, type_name.as_str())
                {
                    if let Some(variant) = info.variants.iter().find(|v| &v.name == member_name) {
                        if variant.fields.is_empty() {
                            // A unit enum variant is a value, not a constructor: emit it as
                            // a (field-less) struct literal so it carries the enum's type
                            // SymbolId onto the runtime value, like any other constructor
                            // (METEL-185). The evaluator builds `Value::Enum` from a
                            // 2-segment struct-literal path.
                            return Ok(TypedExpr::StructLiteral {
                                path: segments.clone(),
                                fields: vec![],
                                ty: Type::Named(type_name.clone(), vec![]),
                                type_id: ctx.type_symbol_id(type_name),
                                span: span.clone(),
                            });
                        }
                        let field_types: Vec<Type> = variant
                            .fields
                            .iter()
                            .map(|field| infer_type_to_type(&field.ty, span))
                            .collect::<Result<_, _>>()?;
                        let ty = crate::types::default_fun_type(
                            field_types,
                            Type::Named(type_name.clone(), vec![]),
                        );
                        return Ok(TypedExpr::Path(segments.clone(), ty, span.clone()));
                    }
                }
            }
            Err(MetelError::internal(format!(
                "unresolved path `{}`",
                segments.join("::")
            )))
        }
        Expr::Closure {
            captures,
            call_multiplicity,
            call_mutation,
            params,
            return_type,
            body,
            span,
        } => {
            let (effective_multiplicity, effective_mutation) = match expected_ty {
                Some(Type::Fun(_, _, expected_multiplicity, _, expected_mutation)) => {
                    (*expected_multiplicity, *expected_mutation)
                }
                _ => (*call_multiplicity, *call_mutation),
            };
            verify_closure_capture_list(
                captures,
                effective_multiplicity,
                effective_mutation,
                params,
                body,
                span,
                ctx,
            )?;
            let param_types: Vec<Type> = params
                .iter()
                .map(|p| {
                    p.type_ann.as_ref().map_or_else(
                        || {
                            Err(MetelError::type_error(
                                TypeErrorCode::T0002,
                                format!("closure parameter `{}` needs a type annotation", p.name),
                                &p.span,
                            ))
                        },
                        |ann| {
                            resolved_to_type(&ctx.type_expr_to_infer_ctx(ann), ctx.subst, &p.span)
                        },
                    )
                })
                .collect::<Result<_, _>>()?;
            let ret_ty = if let Some(inferred) = ctx.resolved_facts.closure_return_type(span) {
                inferred.clone()
            } else {
                return_type
                    .as_ref()
                    .map(|ann| resolved_to_type(&ctx.type_expr_to_infer_ctx(ann), ctx.subst, span))
                    .transpose()?
                    .unwrap_or(Type::Unit)
            };
            let use_multiplicity = if captures.iter().all(|capture| match capture {
                crate::ast::CaptureSpec::SharedRef { .. }
                | crate::ast::CaptureSpec::MutRef { .. } => true,
                crate::ast::CaptureSpec::Owned { name, .. }
                | crate::ast::CaptureSpec::Clone { name, .. } => {
                    ctx.lookup(name).is_some_and(|ty| {
                        ctx.registry
                            .type_satisfies_aspect(ctx.current_module, ty, "Copy")
                    })
                }
            }) {
                crate::types::UseMultiplicity::Copy
            } else {
                crate::types::UseMultiplicity::Move
            };
            ctx.push_scope();
            ctx.enter_closure(
                captures
                    .iter()
                    .filter_map(|capture| match capture {
                        crate::ast::CaptureSpec::Owned { name, .. }
                        | crate::ast::CaptureSpec::Clone { name, .. } => Some(name.clone()),
                        crate::ast::CaptureSpec::SharedRef { .. }
                        | crate::ast::CaptureSpec::MutRef { .. } => None,
                    })
                    .collect(),
            );
            for (p, ty) in params.iter().zip(param_types.iter()) {
                ctx.bind(&p.name, ty.clone());
            }
            // Without this, unmentioned type params in variant literals (e.g. the
            // E in Result::Ok inside a ()->Result<T,E>) have no hint and fail T0002.
            let body_expected = Some(&ret_ty);
            // Push the closure's own return type so an explicit `return` inside its
            // body (constructed via `construct_stmt`'s `Stmt::Return` arm) compares
            // against the closure's declared type, not whatever enclosing function's
            // return type happened to be in scope (RFC-0067a's read-copy relies on
            // this being correct — without it, `return`ing a reference out of a
            // closure declared to return the referent type silently skipped the copy).
            let saved_return = ctx.push_return_type(Some(ret_ty.clone()));
            let saved_loop_depth = ctx.push_loop_depth_reset();
            let typed_body = construct_block(body, body_expected, ctx)?;
            ctx.pop_loop_depth(saved_loop_depth);
            ctx.pop_return_type(saved_return);
            ctx.exit_closure();
            ctx.pop_scope();
            let ty = Type::Fun(
                param_types,
                Box::new(ret_ty),
                effective_multiplicity,
                use_multiplicity,
                effective_mutation,
            );
            Ok(TypedExpr::Closure {
                captures: captures.clone(),
                call_multiplicity: effective_multiplicity,
                call_mutation: effective_mutation,
                params: params.clone(),
                return_type: return_type.clone(),
                body: typed_body,
                ty,
                span: span.clone(),
            })
        }
        Expr::Match(m) => construct_match(m, expected_ty, ctx),
        Expr::PropagateError { expr, span } => construct_propagate_error(expr, span, ctx),
        Expr::Ascribe { expr, ann, span } => {
            let ty = resolved_to_type(&ctx.type_expr_to_infer_ctx(ann), ctx.subst, span)?;
            let constructed = construct_expr(expr, Some(&ty), ctx)?;
            let constructed =
                maybe_read_copy(&ty, constructed, span, ctx.registry, ctx.current_module)?;
            let constructed = maybe_singleton_coerce(&ty, constructed, span, ctx.registry)?;
            maybe_dyn_coerce(&ty, constructed, span, ctx)
        }

        Expr::Cast {
            expr,
            target_type,
            span,
        } => {
            let typed_expr = construct_expr(expr, None, ctx)?;
            let ty = resolved_to_type(&ctx.type_expr_to_infer_ctx(target_type), ctx.subst, span)?;
            Ok(TypedExpr::Cast {
                expr: Box::new(typed_expr),
                target_type: target_type.clone(),
                ty,
                span: span.clone(),
            })
        }

        Expr::TupleAccess {
            object,
            index,
            span,
        } => {
            let typed_obj = construct_expr(object, None, ctx)?;
            let ty = match peel_type_references(typed_obj.ty()) {
                Type::Tuple(elems) => elems.get(*index).cloned().ok_or_else(|| {
                    MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!(
                            "tuple index {index} out of bounds (tuple has {} elements)",
                            elems.len()
                        ),
                        span,
                    )
                })?,
                _ => {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0002,
                        "cannot infer tuple type for index access; add a type annotation",
                        span,
                    ))
                }
            };
            Ok(TypedExpr::TupleAccess {
                object: Box::new(typed_obj),
                index: *index,
                ty,
                span: span.clone(),
            })
        }
        Expr::Loop { body, span } => {
            let saved_break = ctx.push_break_type(expected_ty.cloned());
            ctx.enter_loop();
            let typed_body = construct_block(body, None, ctx)?;
            ctx.exit_loop();
            ctx.pop_break_type(saved_break);
            let ty = find_loop_break_type(&typed_body).unwrap_or(Type::Never);
            Ok(TypedExpr::Loop {
                body: typed_body,
                ty,
                span: span.clone(),
            })
        }
        // Issue #229: `return`/`break`/`continue` as expressions of type `!`,
        // reachable anywhere (not just as a braced statement). Direct port of
        // the former `Stmt::Return`/`Break`/`Continue` construction.
        Expr::Return(r) => {
            let return_ty = ctx.current_return_ty.clone();
            let value = match &r.value {
                Some(e) => {
                    let constructed = construct_expr(e, return_ty.as_ref(), ctx)?;
                    Some(Box::new(match &return_ty {
                        Some(t) => {
                            let constructed = maybe_read_copy(
                                t,
                                constructed,
                                e.span(),
                                ctx.registry,
                                ctx.current_module,
                            )?;
                            let constructed =
                                maybe_singleton_coerce(t, constructed, e.span(), ctx.registry)?;
                            maybe_dyn_coerce(t, constructed, e.span(), ctx)?
                        }
                        None => constructed,
                    }))
                }
                None => None,
            };
            Ok(TypedExpr::Return(TypedReturnExpr {
                value,
                span: r.span.clone(),
            }))
        }
        Expr::Break(b) => {
            if !ctx.is_in_loop() {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0021,
                    "`break` used with no enclosing loop",
                    &b.span,
                ));
            }
            let break_ty = ctx.current_break_ty.clone();
            let value = match &b.value {
                Some(e) => {
                    let constructed = construct_expr(e, break_ty.as_ref(), ctx)?;
                    Some(Box::new(match &break_ty {
                        Some(t) => {
                            let constructed = maybe_read_copy(
                                t,
                                constructed,
                                e.span(),
                                ctx.registry,
                                ctx.current_module,
                            )?;
                            let constructed =
                                maybe_singleton_coerce(t, constructed, e.span(), ctx.registry)?;
                            maybe_dyn_coerce(t, constructed, e.span(), ctx)?
                        }
                        None => constructed,
                    }))
                }
                None => None,
            };
            Ok(TypedExpr::Break(TypedBreakExpr {
                value,
                span: b.span.clone(),
            }))
        }
        Expr::Continue(span) => {
            if !ctx.is_in_loop() {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0021,
                    "`continue` used with no enclosing loop",
                    span,
                ));
            }
            Ok(TypedExpr::Continue(span.clone()))
        }
    }
}
