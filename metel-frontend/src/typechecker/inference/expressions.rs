use super::{
    ann_to_infer, builtin_pattern_method_type, chain_provides_mut_access, check_field_visibility,
    constrain_with_read_copy, infer_binop, infer_block, infer_enum_variant_literal,
    infer_field_assign_type, infer_literal, infer_match, infer_propagate_error,
    infer_struct_literal, infer_to_type_for_from, infer_tuple_assign_type, infer_type_name,
    infer_type_to_type, infer_unaryop, is_shared_reference_chain, named_type_name,
    peel_all_references, record_projection_base_expr, resolve_row_bound_field,
    signature_type_expr_to_infer, type_expr_to_infer_with_generics, type_to_infer, AssignOp,
    AssignTarget, Expr, ForInit, FunGeneralization, GenericBound, HashMap, InferContext, InferType,
    MetelError, Param, SignatureEnv, Stmt, Substitution, Type, TypeErrorCode, TypeExpr, TypeVar,
};

// Exhaustive match over every AST/type-system variant; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
pub(super) fn infer_stmt(
    stmt: &Stmt,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<InferType, MetelError> {
    match stmt {
        // Issue #229: `return`/`break`/`continue` are now `Expr` variants, so a
        // bare `return 5;` used as a mid-block statement reaches here as an
        // ordinary `Stmt::Expr`. Propagate `Never` when the inner expression
        // is genuinely `Never`-typed (return/break/continue, or any other
        // diverging expression like `panic(msg)`) rather than always
        // discarding to `unit()` — needed so `infer_block`'s tail-less "last
        // statement" type correctly reflects divergence.
        Stmt::Expr(e) => {
            let ty = infer_expr(e, ctx, fun_generalizations)?;
            Ok(if ty == InferType::Never {
                InferType::never()
            } else {
                InferType::unit()
            })
        }
        Stmt::While(ws) => {
            let cond_ty = infer_expr(&ws.condition, ctx, fun_generalizations)?;
            ctx.add_constraint(cond_ty, InferType::bool(), ws.span.clone());
            ctx.enter_loop();
            infer_block(&ws.body, ctx, fun_generalizations)?;
            ctx.exit_loop();
            Ok(InferType::unit())
        }
        Stmt::For(fs) => {
            ctx.push_scope();
            if let Some(init) = &fs.init {
                match init {
                    ForInit::Let(ld) => {
                        let val_ty = infer_expr(&ld.value, ctx, fun_generalizations)?;
                        let bound_ty = if let Some(ann) = &ld.type_ann {
                            let declared = ann_to_infer(ann, ctx);
                            constrain_with_read_copy(ctx, val_ty, declared, ld.span.clone())
                        } else {
                            val_ty
                        };
                        ctx.bind_mono(&ld.name, bound_ty, false);
                    }
                    ForInit::Mut(md) => {
                        let val_ty = infer_expr(&md.value, ctx, fun_generalizations)?;
                        let bound_ty = if let Some(ann) = &md.type_ann {
                            let declared = ann_to_infer(ann, ctx);
                            constrain_with_read_copy(ctx, val_ty, declared, md.span.clone())
                        } else {
                            val_ty
                        };
                        ctx.bind_mono(&md.name, bound_ty, true);
                    }
                    ForInit::Expr(e) => {
                        infer_expr(e, ctx, fun_generalizations)?;
                    }
                }
            }
            if let Some(cond) = &fs.condition {
                let cond_ty = infer_expr(cond, ctx, fun_generalizations)?;
                ctx.add_constraint(cond_ty, InferType::bool(), fs.span.clone());
            }
            if let Some(step) = &fs.step {
                infer_expr(step, ctx, fun_generalizations)?;
            }
            ctx.enter_loop();
            infer_block(&fs.body, ctx, fun_generalizations)?;
            ctx.exit_loop();
            ctx.pop_scope();
            Ok(InferType::unit())
        }
        Stmt::ForIn(fi) => {
            let iter_ty = infer_expr(&fi.iterable, ctx, fun_generalizations)?;
            let elem_ty = ctx.fresh_var();
            let partial = ctx.solve()?;
            let resolved_iter = peel_all_references(&partial.apply(&iter_ty));
            match &resolved_iter {
                InferType::Array(elem) | InferType::SizedArray(elem, _) => {
                    ctx.add_constraint(elem_ty.clone(), *elem.clone(), fi.span.clone());
                }
                InferType::Var(_) => {
                    // Unknown type — constrain to Array as default.
                    ctx.add_constraint(
                        iter_ty,
                        InferType::Array(Box::new(elem_ty.clone())),
                        fi.span.clone(),
                    );
                }
                _ => {
                    // Prefer a per-instantiation resolution via the polymorphic
                    // method scheme over the static Iterable registry entry: for a
                    // generic struct implementing Iterable<T> generically (e.g.
                    // `extend<T> Wrapper<T>: Iterable<T> { ... }`), the registry's
                    // own recorded "type args" are the impl's still-generic
                    // parameter names, not concrete types (registered before any
                    // instantiation is known) -- reading them directly would bind
                    // elem_ty to that bogus placeholder instead of the receiver's
                    // actual instantiation.
                    let elem_from_scheme = if let InferType::Named(name, type_args) = &resolved_iter
                    {
                        ctx.method_scheme_for(name, "next")
                            .and_then(|(scheme, struct_tvars)| {
                                let mut subst = Substitution::new();
                                for (&tv, concrete) in struct_tvars.iter().zip(type_args.iter()) {
                                    subst.bind(tv, concrete.clone());
                                }
                                match subst.apply(&scheme.ty) {
                                    InferType::Fun(_, ret, ..) => match *ret {
                                        InferType::Named(n, mut args)
                                            if n == "Perhaps" && args.len() == 1 =>
                                        {
                                            Some(args.remove(0))
                                        }
                                        _ => None,
                                    },
                                    _ => None,
                                }
                            })
                    } else {
                        None
                    };
                    // Fall back to the Iterable registry (concrete impls).
                    let elem = elem_from_scheme.or_else(|| {
                        let type_name = infer_type_name(&resolved_iter).map(ToOwned::to_owned);
                        type_name
                            .as_deref()
                            .and_then(|name| ctx.iterable_elem_type(name))
                            .cloned()
                            .map(InferType::Concrete)
                    });
                    match elem {
                        Some(t) => {
                            ctx.add_constraint(elem_ty.clone(), t, fi.span.clone());
                        }
                        None => {
                            return Err(MetelError::type_error(
                                TypeErrorCode::T0001,
                                format!("type `{resolved_iter}` does not implement `Iterable<T>`"),
                                &fi.span,
                            ));
                        }
                    }
                }
            }
            ctx.push_scope();
            ctx.bind_mono(&fi.binding, elem_ty, fi.mutable);
            ctx.enter_loop();
            infer_block(&fi.body, ctx, fun_generalizations)?;
            ctx.exit_loop();
            ctx.pop_scope();
            Ok(InferType::unit())
        }
    }
}

// Exhaustive match over every AST/type-system variant; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
pub(super) fn infer_expr(
    expr: &Expr,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<InferType, MetelError> {
    match expr {
        Expr::Literal(lit, _) => Ok(infer_literal(lit, ctx)),
        Expr::Ident(name, span) => {
            if let Some(err) = ctx.check_glob_conflict(name, span) {
                return Err(err);
            }
            // RFC-0137 slice 2 (metel-core#858): a binding with a field moved out
            // reads at its narrowed residual type from that point on.
            if let Some(narrowed) = ctx.narrowed_infertype(name) {
                return Ok(narrowed);
            }
            if let Some(ty) = ctx.lookup(name) {
                return Ok(ty);
            }
            if let Some(fields) = ctx.get_struct_fields(name) {
                if fields.is_empty() {
                    let type_args: Vec<InferType> = ctx
                        .get_struct_type_params(name)
                        .cloned()
                        .unwrap_or_default()
                        .into_iter()
                        .map(|_| ctx.fresh_var())
                        .collect();
                    return Ok(InferType::Named(name.clone(), type_args));
                }
            }
            if ctx.registry().has_variant_named(name) {
                // RFC-0111 §3.1: defer to pass 2, which resolves against the expected
                // type. Recorded so a deferral that never resolves is reported after
                // solving instead of being silently accepted (metel-core#285).
                let var = ctx.fresh_var();
                if let InferType::Var(tv) = var {
                    ctx.record_variant_deferral(span.clone(), name.clone(), tv);
                }
                return Ok(var);
            }
            Err(MetelError::type_error(
                TypeErrorCode::T0003,
                format!("undefined name `{name}`"),
                span,
            ))
        }
        Expr::ResolvedPath {
            resolved,
            symbol_id: _,
            original,
            span,
        } => {
            if let Some(err) = ctx.check_glob_conflict(resolved, span) {
                return Err(err);
            }
            ctx.lookup(resolved).ok_or_else(|| {
                MetelError::type_error(
                    TypeErrorCode::T0003,
                    format!("undefined name `{}`", original.join("::")),
                    span,
                )
            })
        }
        Expr::BinOp(lhs, op, rhs, span) => {
            infer_binop(lhs, op, rhs, span, ctx, fun_generalizations)
        }
        Expr::UnaryOp(op, operand, span) => {
            infer_unaryop(op, operand, span, ctx, fun_generalizations)
        }
        Expr::Tuple(elems, _) => {
            let elem_tys: Vec<InferType> = elems
                .iter()
                .map(|e| infer_expr(e, ctx, fun_generalizations))
                .collect::<Result<_, _>>()?;
            Ok(InferType::Tuple(elem_tys))
        }
        Expr::RecordLiteral { fields, .. } => {
            let mut inferred_fields = Vec::with_capacity(fields.len());
            for (name, expr) in fields {
                inferred_fields.push((name.clone(), infer_expr(expr, ctx, fun_generalizations)?));
            }
            Ok(InferType::Record(inferred_fields))
        }
        Expr::Array(elems, span) => {
            if elems.is_empty() {
                return Ok(InferType::Array(Box::new(ctx.fresh_var())));
            }
            let first_ty = infer_expr(&elems[0], ctx, fun_generalizations)?;
            for elem in &elems[1..] {
                let ty = infer_expr(elem, ctx, fun_generalizations)?;
                ctx.add_constraint(ty, first_ty.clone(), span.clone());
            }
            Ok(InferType::Array(Box::new(first_ty)))
        }
        Expr::RepeatArray(elem, n, _span) => {
            let elem_ty = infer_expr(elem, ctx, fun_generalizations)?;
            Ok(InferType::SizedArray(Box::new(elem_ty), *n))
        }
        Expr::Call {
            callee, args, span, ..
        } => {
            // Overloaded free-function call (METEL-180): infer argument types,
            // select the exact-match candidate, and yield its return type. The
            // selected definition's SymbolId is stamped in the construction pass.
            if let Some(name) = super::super::overload::callee_name(callee) {
                if ctx.is_overloaded(name) {
                    let arg_infer: Vec<InferType> = args
                        .iter()
                        .map(|a| infer_expr(a, ctx, fun_generalizations))
                        .collect::<Result<_, _>>()?;
                    // Default unresolved literal vars (a bare `42` is i64, a bare
                    // float literal is f64) so literals participate in selection
                    // the same way they type everywhere else.
                    let solved = ctx.solve()?;
                    let solved = ctx.default_literal_vars(&solved);
                    // When no candidate matches (or args can't resolve), a call
                    // can fall back to a non-overload binding of the same name
                    // from an outer source (the prelude / imports — e.g. the
                    // generic std::core `print` when a module overloads `print`
                    // for specific types). Local overload sets EXTEND such a
                    // binding rather than replace it.
                    let fallback = |ctx: &mut InferContext,
                                    arg_infer: &[InferType]|
                     -> Result<InferType, MetelError> {
                        let callee_ty = ctx
                            .lookup(name)
                            .expect("has_binding checked before fallback");
                        let ret_var = ctx.fresh_var();
                        ctx.add_constraint(
                            callee_ty,
                            InferType::fun(arg_infer.to_vec(), ret_var.clone()),
                            span.clone(),
                        );
                        Ok(ret_var)
                    };
                    let arg_types: Result<Vec<Type>, ()> = arg_infer
                        .iter()
                        .map(|t| infer_type_to_type(&solved.apply(t), span).map_err(|_| ()))
                        .collect();
                    let arg_types = match arg_types {
                        Ok(tys) => tys,
                        Err(()) if ctx.has_binding(name) => {
                            return fallback(ctx, &arg_infer);
                        }
                        Err(()) => {
                            return Err(MetelError::type_error(
                                TypeErrorCode::T0002,
                                format!(
                                "cannot resolve argument types for overloaded call to `{name}`; \
                                     add type annotations"
                            ),
                                span,
                            ))
                        }
                    };
                    let entries = ctx.overload_candidates(name).unwrap();
                    let entry =
                        if let Some(entry) = super::super::overload::select(entries, &arg_types) {
                            entry.clone()
                        } else {
                            if ctx.has_binding(name) {
                                return fallback(ctx, &arg_infer);
                            }
                            let entries = ctx.overload_candidates(name).unwrap();
                            return Err(super::super::overload::no_match_error(
                                name, &arg_types, entries, span,
                            ));
                        };
                    // Commit the selection: constrain each argument to the chosen
                    // candidate's parameter type so defaulted literal vars resolve
                    // to what selection assumed.
                    for (arg_ty, param) in arg_infer.iter().zip(&entry.params) {
                        ctx.add_constraint(arg_ty.clone(), type_to_infer(param), span.clone());
                    }
                    let ret_var = ctx.fresh_var();
                    ctx.add_constraint(ret_var.clone(), type_to_infer(&entry.ret), span.clone());
                    return Ok(ret_var);
                }
            }

            // Check for opaque-returning function and do dedicated instantiation
            if let Some(callee_name) = super::super::overload::callee_name(callee) {
                if let Some(scheme) = ctx.poly_scheme(callee_name) {
                    if !scheme.opaque_returns.is_empty() {
                        // This function has opaque returns - do dedicated instantiation
                        let arg_infer: Vec<InferType> = args
                            .iter()
                            .map(|a| infer_expr(a, ctx, fun_generalizations))
                            .collect::<Result<_, _>>()?;

                        // Solve constraints to get a complete substitution
                        let solved = ctx.solve()?;
                        let _solved = ctx.default_literal_vars(&solved);

                        // Instantiate the scheme with renaming to get fresh vars.
                        // Must mint from ctx's own live TypeVar generator (not a
                        // disposable one forked via fresh_var_generator, which
                        // snapshots the counter without ever advancing it) --
                        // otherwise every subsequent ordinary ctx.fresh_var() call
                        // in the rest of this function body reissues the exact
                        // same ids just handed out here, aliasing this call's
                        // opaque marker with unrelated later TypeVars. Confirmed
                        // by reproduction: three or more opaque-returning calls in
                        // one block, with .display() called on at least two of
                        // them before a third, corrupted the third's inferred type.
                        let (instantiated_ty, renaming) = ctx.instantiate_with_renaming(&scheme);

                        if let InferType::Fun(params, ret, ..) = instantiated_ty {
                            // Constrain arguments to match the instantiated function type
                            for (arg_ty, param) in arg_infer.iter().zip(params.iter()) {
                                ctx.add_constraint(arg_ty.clone(), param.clone(), span.clone());
                            }

                            // Register aspect bounds and mark opacity guards for each opaque return
                            for (i, opaque) in scheme.opaque_returns.iter().enumerate() {
                                if let Some((aspect, _)) = opaque {
                                    if let Some(&orig_tv) = scheme.quantified_vars.get(i) {
                                        if let Some(&fresh_tv) = renaming.get(&orig_tv) {
                                            ctx.register_type_var_bound(fresh_tv, aspect.clone());
                                            ctx.mark_opaque_return_var(fresh_tv);
                                        }
                                    }
                                }
                            }

                            return Ok(*ret);
                        }
                    }
                }
            }

            let callee_ty = infer_expr(callee, ctx, fun_generalizations)?;
            // Auto-deref: &(() -> T) and &mut (() -> T) are callable directly.
            let callee_ty = match ctx.solve()?.apply(&callee_ty) {
                InferType::Reference(inner) | InferType::MutReference(inner)
                    if matches!(*inner, InferType::Fun(..)) =>
                {
                    *inner
                }
                _ => callee_ty,
            };
            let arg_tys: Vec<InferType> = args
                .iter()
                .map(|a| infer_expr(a, ctx, fun_generalizations))
                .collect::<Result<_, _>>()?;
            // RFC-0137 slice 2: a by-value argument that partially moves a struct
            // field narrows the base binding for the rest of the block.
            for arg in args {
                ctx.note_consumed_infer(arg);
            }
            if let InferType::Fun(params, ret, ..) = &callee_ty {
                if params.len() != arg_tys.len() {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0004,
                        format!(
                            "expected {} argument(s), got {}",
                            params.len(),
                            arg_tys.len()
                        ),
                        span,
                    ));
                }
                for (arg_ty, param) in arg_tys.iter().zip(params.iter()) {
                    ctx.add_constraint(arg_ty.clone(), param.clone(), span.clone());
                }
                return Ok(*ret.clone());
            }
            let ret_var = ctx.fresh_var();
            // `callee_ty` on the right, the caller-built `Fun` on the left (#266
            // continuation) -- not just style. `unify`'s `(Var, _)` case binds
            // its *first* argument's var to its second, so whichever side ends
            // up as `unify`'s `a` when this constraint's two `Fun`s are matched
            // param-by-param loses its identity: a declared-name tag applied to
            // one of `callee_ty`'s own fresh vars (via `ctx.instantiate`, tagged
            // from `TypeScheme.param_names`) only survives into the solved
            // substitution if `callee_ty`'s params end up as `unify`'s *second*
            // argument at each position, not the first -- the same
            // union-find-direction root cause diagnosed for #236's method-
            // dispatch bug, here affecting name-tagging instead of literal
            // defaulting. Swapping which side is `lhs` restores that.
            ctx.add_constraint(
                InferType::fun(arg_tys, ret_var.clone()),
                callee_ty,
                span.clone(),
            );
            Ok(ret_var)
        }
        Expr::Index {
            object,
            index,
            span,
        } => {
            let obj_ty = infer_expr(object, ctx, fun_generalizations)?;
            // Index expression type is checked in the construction pass (must be u64).
            // No inference constraint needed here; plain int literals are promoted to u64 by construction.
            let _idx_ty = infer_expr(index, ctx, fun_generalizations)?;
            let resolved_obj = ctx.solve()?.apply(&obj_ty);
            match peel_all_references(&resolved_obj) {
                InferType::Array(elem) | InferType::SizedArray(elem, _) => Ok(*elem),
                _ => {
                    let elem_var = ctx.fresh_var();
                    ctx.add_constraint(
                        obj_ty,
                        InferType::Array(Box::new(elem_var.clone())),
                        span.clone(),
                    );
                    Ok(elem_var)
                }
            }
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            span,
        } => {
            let cond_ty = infer_expr(condition, ctx, fun_generalizations)?;
            ctx.add_constraint(cond_ty, InferType::bool(), span.clone());

            // metel-core#958: row-narrowing move state is path-sensitive across
            // the arms. Each arm forks from the pre-`if` state, and the arms
            // join after — so the `else` arm never sees the `then` arm's partial
            // moves, and a move on either arm still narrows the binding for the
            // code after the `if` (the join is the union of the arms' moves).
            let entry_flow = ctx.flow_ref().clone();
            let then_ty = infer_block(then_branch, ctx, fun_generalizations)?;
            let then_flow = std::mem::replace(ctx.flow_mut(), entry_flow.clone());
            let mut joined_flow = entry_flow.clone();
            joined_flow.union_from(&then_flow);

            let result = if let Some(else_block) = else_branch {
                let else_ty = infer_block(else_block, ctx, fun_generalizations)?;
                let else_flow = std::mem::replace(ctx.flow_mut(), entry_flow);
                joined_flow.union_from(&else_flow);
                // RFC-0152: a function-valued conditional joins at the least
                // permissive capability. Both arms then widen to that joined type.
                let joined = match (&then_ty, &else_ty) {
                    (
                        InferType::Fun(then_params, then_ret, then_call, then_use, then_mut),
                        InferType::Fun(else_params, else_ret, else_call, else_use, else_mut),
                    ) if then_params.len() == else_params.len() => InferType::Fun(
                        then_params.clone(),
                        Box::new((**then_ret).clone()),
                        if *then_call == crate::types::CallMultiplicity::Once
                            || *else_call == crate::types::CallMultiplicity::Once
                        {
                            crate::types::CallMultiplicity::Once
                        } else {
                            crate::types::CallMultiplicity::Many
                        },
                        if *then_use == crate::types::UseMultiplicity::Move
                            || *else_use == crate::types::UseMultiplicity::Move
                        {
                            crate::types::UseMultiplicity::Move
                        } else {
                            crate::types::UseMultiplicity::Copy
                        },
                        if *then_mut == crate::types::CallMutation::Mutating
                            || *else_mut == crate::types::CallMutation::Mutating
                        {
                            crate::types::CallMutation::Mutating
                        } else {
                            crate::types::CallMutation::Reading
                        },
                    ),
                    _ => then_ty.clone(),
                };
                ctx.add_constraint(then_ty, joined.clone(), span.clone());
                ctx.add_constraint(else_ty, joined.clone(), span.clone());
                joined
            } else {
                ctx.add_constraint(then_ty, InferType::unit(), span.clone());
                InferType::unit()
            };
            *ctx.flow_mut() = joined_flow;
            Ok(result)
        }
        Expr::Assign {
            target,
            op,
            value,
            span,
        } => {
            let target_ty = match target {
                AssignTarget::Ident(name, target_span) => {
                    // RFC-0110 §4.2: bare assignment to an identifier always *rebinds*,
                    // for reference-typed bindings exactly as for every other type.
                    // RFC-0067a's implicit whole-value write-through is retired — it was
                    // the one auto-deref mechanism competing with a second sensible
                    // reading of the same syntax, and it made repointing a `&var T`
                    // unrepresentable. `*p = v` (AssignTarget::Deref) is now the spelling
                    // that writes through.
                    ctx.lookup_for_write(name, target_span)?
                }
                // RFC-0110: `*p = v` writes through to the referent. The value's type is
                // the referent type, so peel exactly the layer `*` names.
                AssignTarget::Deref {
                    object,
                    span: target_span,
                } => {
                    let obj_ty = infer_expr(object, ctx, fun_generalizations)?;
                    let inner = ctx.fresh_var();
                    ctx.add_constraint(
                        obj_ty,
                        InferType::MutReference(Box::new(inner.clone())),
                        target_span.clone(),
                    );
                    inner
                }
                AssignTarget::Index {
                    object,
                    index,
                    span: target_span,
                } => {
                    let raw_obj_ty = infer_expr(object, ctx, fun_generalizations)?;
                    // RFC-0110 §4.1: an index target reaches through a reference at the
                    // root, the same way a field target already does. Peel before
                    // constraining, or `xs[0] = v` for `xs: &var i64[]` would try to
                    // unify `&var i64[]` with `?t[]` and fail.
                    let obj_ty = peel_all_references(&raw_obj_ty);
                    // Index type checked in construction pass; no inference constraint here.
                    let _idx_ty = infer_expr(index, ctx, fun_generalizations)?;
                    let elem_var = ctx.fresh_var();
                    ctx.add_constraint(
                        obj_ty,
                        InferType::Array(Box::new(elem_var.clone())),
                        target_span.clone(),
                    );
                    elem_var
                }
                AssignTarget::FieldAccess {
                    object,
                    field,
                    span: target_span,
                } => infer_field_assign_type(object, field, target_span, ctx, fun_generalizations)?,
                AssignTarget::TupleAccess {
                    object,
                    index,
                    span: target_span,
                } => {
                    infer_tuple_assign_type(object, *index, target_span, ctx, fun_generalizations)?
                }
            };
            let value_ty = infer_expr(value, ctx, fun_generalizations)?;
            // RFC-0137 slice 2: the RHS may itself partially move a struct field;
            // then a plain `a.f := …` widens `a`'s type back by reinitializing
            // that place.
            ctx.note_consumed_infer(value);
            match op {
                AssignOp::Assign => {
                    ctx.add_constraint(target_ty, value_ty, span.clone());
                    ctx.note_reassigned_infer(target);
                }
                AssignOp::AddAssign
                | AssignOp::SubAssign
                | AssignOp::MulAssign
                | AssignOp::DivAssign
                | AssignOp::RemAssign => {
                    let result = ctx.fresh_var();
                    ctx.add_constraint(target_ty, result.clone(), span.clone());
                    ctx.add_constraint(value_ty, result, span.clone());
                }
            }
            Ok(InferType::unit())
        }
        Expr::FieldAccess {
            object,
            field,
            span,
        } => {
            let obj_ty = infer_expr(object, ctx, fun_generalizations)?;
            let obj_ty = ctx.solve()?.apply(&obj_ty);
            let peeled = peel_all_references(&obj_ty);
            // RFC-0137 (metel-core#857): a Residual resolves field access exactly like
            // Record does -- directly from its own field list, no struct-registry lookup
            // needed (it already carries each projected field's resolved type).
            if let InferType::Record(fields) | InferType::Residual { fields, .. } = &peeled {
                return fields
                    .iter()
                    .find(|(name, _)| name == field)
                    .map(|(_, ty)| ty.clone())
                    .ok_or_else(|| {
                        MetelError::type_error(
                            TypeErrorCode::T0003,
                            format!("no field `{field}` on {peeled}"),
                            span,
                        )
                    });
            }
            // Abstract, row-bounded generic type parameter (`<record T: { x: f64, .. }>`):
            // resolve `field` against the row bound the same way MethodCall's slow path
            // (below) resolves a method against an aspect bound, instead of falling
            // through to the nominal-struct path, which can't name a struct for a bare
            // TypeVar and would otherwise mislead with "add a type annotation" — no
            // annotation fixes a missing row-bound field.
            if let InferType::Var(tv) = &peeled {
                if let Some(result) = resolve_row_bound_field(ctx, *tv, field, span) {
                    return result;
                }
            }
            let struct_name = named_type_name(&obj_ty).ok_or_else(|| {
                MetelError::type_error(
                    TypeErrorCode::T0002,
                    "cannot infer struct type for field access; add a type annotation",
                    span,
                )
            })?;
            let type_args = match &obj_ty {
                InferType::Named(_, args) => args.clone(),
                InferType::Reference(inner) | InferType::MutReference(inner) => {
                    match inner.as_ref() {
                        InferType::Named(_, args) => args.clone(),
                        _ => vec![],
                    }
                }
                _ => vec![],
            };
            let fields = ctx
                .get_struct_fields(&struct_name)
                .ok_or_else(|| {
                    MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!("unknown type `{struct_name}`"),
                        span,
                    )
                })?
                .clone();
            let field_entry = fields
                .iter()
                .find(|entry| entry.name == *field)
                .ok_or_else(|| {
                    MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!("no field `{field}` on `{struct_name}`"),
                        span,
                    )
                })?;
            check_field_visibility(
                field_entry,
                &struct_name,
                ctx.current_module_path(),
                ctx.registry()
                    .struct_declaring_module(ctx.current_module_path(), &struct_name),
                ctx.registry()
                    .struct_visibility_for(ctx.current_module_path(), &struct_name),
                span,
                "access",
            )?;
            let raw_ty = field_entry.ty.clone();
            // For generic structs, substitute declared type params with the resolved args.
            if let Some(type_params) = ctx.get_struct_type_params(&struct_name).cloned() {
                let mut remap = Substitution::new();
                for (&tp, arg) in type_params.iter().zip(type_args.iter()) {
                    remap.bind(tp, arg.clone());
                }
                Ok(remap.apply(&raw_ty))
            } else {
                Ok(raw_ty)
            }
        }
        Expr::MethodCall {
            receiver,
            method,
            args,
            span,
            ..
        } => {
            let recv_ty = infer_expr(receiver, ctx, fun_generalizations)?;
            let solved = ctx.solve()?;
            let recv_ty = solved.apply(&recv_ty);
            // If the receiver is (or resolves through a chain of unifications to)
            // a numeric literal TypeVar, default it to i64/f64 so method dispatch
            // can proceed with a concrete type. `default_literal_vars` walks that
            // chain; a bare `is_integer_literal_var`/`is_float_literal_var` check
            // on the post-`solve()` var only catches the receiver being the
            // literal's own original TypeVar, not one merely unified with it —
            // which is exactly what a generic struct field recovers to (#236:
            // `Pair { first = 1, .. }.first` carries `A`'s own fresh TypeVar,
            // constrained equal to the literal `1`'s TypeVar, not that TypeVar
            // itself, so `p.first.to_string()` failed with T0002 even though
            // `p.first + 1` — which goes through `default_literal_vars` via the
            // arithmetic path below — already worked).
            let defaulted = ctx.default_literal_vars(&solved);
            let recv_ty = defaulted.apply(&recv_ty);

            let arg_tys: Vec<InferType> = args
                .iter()
                .map(|a| infer_expr(a, ctx, fun_generalizations))
                .collect::<Result<_, _>>()?;

            if let Some(result) = builtin_pattern_method_type(&recv_ty, method, &arg_tys, span) {
                return result;
            }

            // Fast path: concrete named type — look up method as usual.
            let peeled_recv = peel_all_references(&recv_ty);
            if let InferType::Array(elem) = &peeled_recv {
                let method_ty = if let Some(ty) = ctx.get_array_method_type(method).cloned() {
                    ty
                } else if let Some((scheme, struct_tvars)) = ctx
                    .array_method_scheme_for(method)
                    .map(|(s, t)| (s.clone(), t.clone()))
                {
                    let (instance, renaming) = ctx.instantiate_with_renaming(&scheme);
                    let mut pin = Substitution::new();
                    for (&tv, arg) in struct_tvars.iter().zip(std::iter::once(elem.as_ref())) {
                        if let Some(&fresh) = renaming.get(&tv) {
                            pin.bind(fresh, arg.clone());
                        }
                    }
                    pin.apply(&instance)
                } else {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!("no method `{method}` on array type"),
                        span,
                    ));
                };

                if matches!(
                    ctx.get_array_method_receiver_kind(method),
                    Some(crate::ast::ReceiverKind::RefMut)
                ) && !chain_provides_mut_access(&recv_ty)
                {
                    // T0006, not T0008 — T0008 is "non-exhaustive match". This site
                    // has been miscoding the error since it was written; no fixture
                    // covered it, so nothing caught it. The spelling is `&var self`
                    // too: `&mut` is not syntax this language has (#301).
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0006,
                        format!(
                            "cannot call `&var self` method `{method}` through a shared reference"
                        ),
                        span,
                    ));
                }

                if let InferType::Fun(params, ret, ..) = &method_ty {
                    if params.len().saturating_sub(1) != arg_tys.len() {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0004,
                            format!(
                                "expected {} argument(s), got {}",
                                params.len().saturating_sub(1),
                                arg_tys.len()
                            ),
                            span,
                        ));
                    }
                    for (arg_ty, param) in arg_tys.iter().zip(params.iter().skip(1)) {
                        ctx.add_constraint(arg_ty.clone(), param.clone(), span.clone());
                    }
                    return Ok(*ret.clone());
                }
                return Err(MetelError::internal("array method type is not a function"));
            }

            // Fast path: concrete named type — look up method as usual.
            if let Some(struct_name) = named_type_name(&recv_ty) {
                let recv_type_args = match &recv_ty {
                    InferType::Named(_, args) => args.clone(),
                    InferType::Reference(inner) | InferType::MutReference(inner) => {
                        match inner.as_ref() {
                            InferType::Named(_, args) => args.clone(),
                            _ => vec![],
                        }
                    }
                    _ => vec![],
                };

                // Try concrete method_env first; fall back to method_scheme_env for generic structs.
                let method_ty = if let Some(ty) = ctx.get_method_type(&struct_name, method).cloned()
                {
                    ty
                } else if let Some((scheme, struct_tvars)) = ctx
                    .method_scheme_for(&struct_name, method)
                    .map(|(s, t)| (s.clone(), t.clone()))
                {
                    // Instantiate the scheme with a fresh TypeVar for EVERY
                    // quantified var — the struct's type params and the method's
                    // own generics (e.g. `U` in `fun map<U>(...)`). Instantiating
                    // only the struct tvars would leave the method-level generics
                    // as stale shared vars, so two call sites would collide and a
                    // single call could not resolve `U` from its arguments.
                    let (instance, renaming) = ctx.instantiate_with_renaming(&scheme);
                    // Pin the struct's (now fresh) type params to the receiver's
                    // concrete type args so `self`/return types line up.
                    let mut pin = Substitution::new();
                    for (&tv, arg) in struct_tvars.iter().zip(recv_type_args.iter()) {
                        if let Some(&fresh) = renaming.get(&tv) {
                            pin.bind(fresh, arg.clone());
                        }
                    }
                    pin.apply(&instance)
                } else {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!("no method `{method}` on `{struct_name}`"),
                        span,
                    ));
                };

                if matches!(
                    ctx.get_method_receiver_kind(&struct_name, method),
                    Some(crate::ast::ReceiverKind::RefMut)
                ) && !chain_provides_mut_access(&recv_ty)
                {
                    // Reached through a shared reference: reject outright, the way
                    // the array-method site above already does. The binding check
                    // below cannot speak for a receiver that is not a binding
                    // (`pair.0.bump()`), which let mutation through a `&T` past.
                    if is_shared_reference_chain(&recv_ty) {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0006,
                            format!(
                                "cannot call `&var self` method `{method}` through a shared reference"
                            ),
                            span,
                        ));
                    }
                    if let Expr::Ident(name, recv_span) = receiver.as_ref() {
                        let _ = ctx.lookup_for_write(name, recv_span)?;
                    }
                }

                let ret_var = ctx.fresh_var();
                let receiver_ty_for_method = peel_all_references(&recv_ty);
                let expected = InferType::fun(
                    std::iter::once(receiver_ty_for_method)
                        .chain(arg_tys)
                        .collect(),
                    ret_var.clone(),
                );
                ctx.add_constraint(method_ty, expected, span.clone());
                return Ok(ret_var);
            }

            // `dyn Aspect` receiver (RFC-0008 slice 2): the aspect is already known
            // statically from the receiver's own type — no bound lookup needed the
            // way a generic type param's `T: Aspect` bound requires below. Resolve
            // the method straight off the aspect's own declaration. Object safety
            // (already checked before Pass 1 even starts — `projections::check`
            // runs first) guarantees no method signature mentions `Self` or an
            // associated type outside receiver position, so unlike the TypeVar slow
            // path below, no `Self`-substitution or associated-type-projection
            // handling is needed — the only substitution is the aspect's own
            // generic params against this `dyn Aspect`'s type args (`dyn
            // Callable<A, B>`'s `A`/`B`).
            let peeled_recv_for_dyn = peel_all_references(&recv_ty);
            if let InferType::Dyn { aspect, type_args } = &peeled_recv_for_dyn {
                let method_def = ctx
                    .get_aspect_method_defs(aspect)
                    .and_then(|methods| methods.iter().find(|m| m.name == *method).cloned())
                    .ok_or_else(|| {
                        MetelError::type_error(
                            TypeErrorCode::T0003,
                            format!("no method `{method}` on `dyn {aspect}`"),
                            span,
                        )
                    })?;

                let aspect_generics = ctx.aspect_generics(aspect).cloned().unwrap_or_default();
                let alias_types: HashMap<String, InferType> = aspect_generics
                    .iter()
                    .cloned()
                    .zip(type_args.iter().cloned())
                    .collect();
                let env = SignatureEnv {
                    generic_vars: HashMap::new(),
                    alias_types,
                    // `Self` cannot appear outside receiver position in an
                    // object-safe aspect's method (rule 1), so this is never
                    // actually consulted — a harmless placeholder, not a bound.
                    self_ty: InferType::unit(),
                };

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
                for (arg_ty, param) in arg_tys.iter().zip(declared_params.iter()) {
                    if let Some(ann) = &param.type_ann {
                        let param_ty = signature_type_expr_to_infer(ann, &env);
                        ctx.add_constraint(arg_ty.clone(), param_ty, span.clone());
                    }
                }

                // Mutable-access guard, mirroring the concrete-receiver and
                // bounded-TypeVar paths.
                let receiver_kind = method_def
                    .params
                    .iter()
                    .find(|p| p.name == "self")
                    .and_then(|p| p.receiver.clone());
                if matches!(receiver_kind, Some(crate::ast::ReceiverKind::RefMut))
                    && !chain_provides_mut_access(&recv_ty)
                {
                    if is_shared_reference_chain(&recv_ty) {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0006,
                            format!(
                                "cannot call `&var self` method `{method}` through a shared reference"
                            ),
                            span,
                        ));
                    }
                    if let Expr::Ident(name, recv_span) = receiver.as_ref() {
                        let _ = ctx.lookup_for_write(name, recv_span)?;
                    }
                }

                let ret_ty = method_def
                    .return_type
                    .as_ref()
                    .map_or(InferType::unit(), |rt| {
                        signature_type_expr_to_infer(rt, &env)
                    });
                let ret_var = ctx.fresh_var();
                ctx.add_constraint(ret_var.clone(), ret_ty, span.clone());
                return Ok(ret_var);
            }

            // Slow path: TypeVar receiver — may be a bounded generic type param.
            //
            // Peeled first, so `x: &T` under `T: Show` reaches the same bound
            // lookup as `x: T` (#334). The concrete-receiver path above already
            // peels; without it here, a borrowing generic could not call an
            // aspect method on its own parameter, which is the shape every
            // read-only generic wants once move checking pushes it to borrow.
            let peeled_recv_for_bounds = peel_all_references(&recv_ty);
            if let InferType::Var(tv) = &peeled_recv_for_bounds {
                if let Some(aspect_names) = ctx.bounds_for_type_var(*tv) {
                    let self_generic_map: HashMap<String, TypeVar> =
                        std::iter::once(("Self".to_string(), *tv)).collect();
                    for aspect_name in aspect_names.iter().filter_map(GenericBound::aspect_name) {
                        if let Some(methods) = ctx.get_aspect_method_defs(aspect_name).cloned() {
                            if let Some(method_def) = methods.iter().find(|m| m.name == *method) {
                                // Resolve return type: Self → the TypeVar itself. A bare
                                // associated-type name (RFC-0082 §1.2 sugar, e.g. `Item` in
                                // `fun next(...) -> Perhaps<Item>`'s inner `Item`, or here the
                                // whole return type) means `Self::Item` -- mint the same
                                // projection placeholder as an explicit `T::Item` would.
                                let ret_ty = method_def.return_type.as_ref().map_or(
                                    InferType::unit(),
                                    |rt| match rt {
                                        TypeExpr::Named(n, _) if n == "Self" => InferType::Var(*tv),
                                        TypeExpr::Named(n, args)
                                            if args.is_empty()
                                                && ctx
                                                    .aspect_assoc_type_decls(aspect_name)
                                                    .is_some_and(|decls| {
                                                        decls.iter().any(|d| d.name == *n)
                                                    }) =>
                                        {
                                            InferType::Var(ctx.fresh_assoc_projection_var(
                                                *tv,
                                                aspect_name,
                                                n,
                                            ))
                                        }
                                        other => type_expr_to_infer_with_generics(
                                            other,
                                            &self_generic_map,
                                        ),
                                    },
                                );

                                // Collect declared non-self params for arity + type checking.
                                let declared_params: Vec<&Param> = method_def
                                    .params
                                    .iter()
                                    .filter(|p| p.name != "self")
                                    .collect();

                                // Arity check.
                                if args.len() != declared_params.len() {
                                    return Err(MetelError::type_error(
                                        TypeErrorCode::T0004,
                                        format!(
                                            "`{aspect_name}::{method}` expects {} argument(s), got {}",
                                            declared_params.len(), args.len()
                                        ),
                                        span,
                                    ));
                                }

                                // Infer arg types and constrain each against the declared param type.
                                let arg_tys: Vec<InferType> = args
                                    .iter()
                                    .map(|a| infer_expr(a, ctx, fun_generalizations))
                                    .collect::<Result<_, _>>()?;

                                for (arg_ty, param) in arg_tys.iter().zip(declared_params.iter()) {
                                    if let Some(ann) = &param.type_ann {
                                        let param_ty = type_expr_to_infer_with_generics(
                                            ann,
                                            &self_generic_map,
                                        );
                                        ctx.add_constraint(arg_ty.clone(), param_ty, span.clone());
                                    }
                                }

                                // Mutable-access guard, mirroring the concrete-receiver
                                // path above. Peeling the receiver (#334) is what makes
                                // this reachable at all: without it a `&var self` method
                                // on a bounded `T` was rejected for the wrong reason —
                                // "cannot infer receiver type" — and peeling alone would
                                // have made `x.bump()` legal through a shared `&T`.
                                let receiver_kind = method_def
                                    .params
                                    .iter()
                                    .find(|p| p.name == "self")
                                    .and_then(|p| p.receiver.clone());
                                if matches!(receiver_kind, Some(crate::ast::ReceiverKind::RefMut))
                                    && !chain_provides_mut_access(&recv_ty)
                                {
                                    if is_shared_reference_chain(&recv_ty) {
                                        return Err(MetelError::type_error(
                                            TypeErrorCode::T0006,
                                            format!(
                                                "cannot call `&var self` method `{method}` through a shared reference"
                                            ),
                                            span,
                                        ));
                                    }
                                    if let Expr::Ident(name, recv_span) = receiver.as_ref() {
                                        let _ = ctx.lookup_for_write(name, recv_span)?;
                                    }
                                }

                                let ret_var = ctx.fresh_var();
                                ctx.add_constraint(ret_var.clone(), ret_ty, span.clone());
                                return Ok(ret_var);
                            }
                        }
                    }
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!(
                            "no method `{method}` on type parameter (bounds: {})",
                            aspect_names
                                .iter()
                                .map(ToString::to_string)
                                .collect::<Vec<_>>()
                                .join(" + ")
                        ),
                        span,
                    ));
                }
            }

            Err(MetelError::type_error(
                TypeErrorCode::T0002,
                "cannot infer receiver type for method call; add a type annotation",
                span,
            ))
        }
        Expr::StructLiteral {
            path, fields, span, ..
        } => {
            if path.len() == 2 {
                infer_enum_variant_literal(
                    &path[0],
                    &path[1],
                    fields,
                    span,
                    ctx,
                    fun_generalizations,
                )
            } else if path.len() == 1
                && ctx.registry().has_variant_named(&path[0])
                && ctx.get_struct_fields(&path[0]).is_none()
            {
                let var = ctx.fresh_var();
                if let InferType::Var(tv) = var {
                    ctx.record_variant_deferral(span.clone(), path[0].clone(), tv);
                }
                Ok(var)
            } else {
                let struct_name = path
                    .last()
                    .ok_or_else(|| MetelError::internal("empty path in struct literal"))?
                    .clone();
                infer_struct_literal(struct_name, fields, span, ctx, fun_generalizations)
            }
        }
        Expr::RecordProjection { path, fields, span } => {
            let base_expr = record_projection_base_expr(path, span);
            let base_ty = infer_expr(&base_expr, ctx, fun_generalizations)?;
            let base_ty = ctx.solve()?.apply(&base_ty);
            // RFC-0137 slice 2: re-projecting a narrowed residual is fine, as long
            // as every named field is still in its current row.
            if let InferType::Residual {
                brand,
                fields: res_fields,
            } = &base_ty
            {
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
            }
            let struct_name = named_type_name(&base_ty)
                .or_else(|| match &base_ty {
                    InferType::Residual { brand, .. } => Some(brand.clone()),
                    _ => None,
                })
                .ok_or_else(|| {
                    MetelError::type_error(
                        TypeErrorCode::T0002,
                        "record projection requires a nominal struct value",
                        span,
                    )
                })?;
            let type_args = match &base_ty {
                InferType::Named(_, args) => args.clone(),
                InferType::Reference(inner) | InferType::MutReference(inner) => {
                    match inner.as_ref() {
                        InferType::Named(_, args) => args.clone(),
                        _ => vec![],
                    }
                }
                _ => vec![],
            };
            let declared_fields = ctx
                .get_struct_fields(&struct_name)
                .ok_or_else(|| {
                    MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!("unknown type `{struct_name}`"),
                        span,
                    )
                })?
                .clone();
            let mut projected = Vec::with_capacity(fields.len());
            for field in fields {
                let field_entry = declared_fields
                    .iter()
                    .find(|entry| entry.name == *field)
                    .ok_or_else(|| {
                        MetelError::type_error(
                            TypeErrorCode::T0003,
                            format!("no field `{field}` on `{struct_name}`"),
                            span,
                        )
                    })?;
                let raw_ty = field_entry.ty.clone();
                let ty =
                    if let Some(type_params) = ctx.get_struct_type_params(&struct_name).cloned() {
                        let mut remap = Substitution::new();
                        for (&tp, arg) in type_params.iter().zip(type_args.iter()) {
                            remap.bind(tp, arg.clone());
                        }
                        remap.apply(&raw_ty)
                    } else {
                        raw_ty
                    };
                projected.push((field.clone(), ty));
            }
            // RFC-0137 (metel-core#857): branded, not a bare Record -- and a full-width
            // projection normalizes back to the plain struct type (mirrors
            // `resolve_record_projection_type` in `conversions.rs`, which does the same
            // for the type-annotation form; both must agree, or a signature naming
            // `Self.{ fd }` and a call site producing it from `h.{ fd }` would disagree
            // over what type it actually is).
            if projected.len() == declared_fields.len() {
                return Ok(InferType::Named(struct_name, type_args));
            }
            projected.sort_by(|(a, _), (b, _)| a.cmp(b));
            Ok(InferType::Residual {
                brand: struct_name,
                fields: projected,
            })
        }
        Expr::Ascribe { expr, ann, span } => {
            let inner_ty = infer_expr(expr, ctx, fun_generalizations)?;
            let ascribed_ty = ann_to_infer(ann, ctx);
            Ok(constrain_with_read_copy(
                ctx,
                inner_ty,
                ascribed_ty,
                span.clone(),
            ))
        }

        Expr::Cast {
            expr,
            target_type,
            span,
        } => {
            let source_ty = infer_expr(expr, ctx, fun_generalizations)?;
            let target_ty = ann_to_infer(target_type, ctx);
            let solved = ctx.solve()?;
            let subst = ctx.default_literal_vars(&solved);
            let source_resolved = subst.apply(&source_ty);
            let target_resolved = subst.apply(&target_ty);
            // Identity casts always allowed.
            if source_resolved == target_resolved {
                return Ok(target_ty);
            }
            // Check via From aspect registry: target must implement From<source>.
            let source_concrete = infer_to_type_for_from(&source_resolved);
            let target_name = infer_type_name(&target_resolved);
            let valid = match (source_concrete.as_ref(), target_name) {
                (Some(src_t), Some(tgt)) => ctx.has_from_impl(tgt, src_t),
                _ => false,
            };
            if !valid {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0007,
                    format!("cannot cast `{source_resolved}` to `{target_resolved}` — no `impl From<{source_resolved}> for {target_resolved}` found"),
                    span,
                ));
            }
            Ok(target_ty)
        }
        Expr::TupleAccess {
            object,
            index,
            span,
        } => {
            let obj_ty = infer_expr(object, ctx, fun_generalizations)?;
            let obj_ty = ctx.solve()?.apply(&obj_ty);
            let peeled = peel_all_references(&obj_ty);
            match &peeled {
                InferType::Tuple(elems) => elems.get(*index).cloned().ok_or_else(|| {
                    MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!(
                            "tuple index {index} out of bounds (tuple has {} elements)",
                            elems.len()
                        ),
                        span,
                    )
                }),
                _ => Err(MetelError::type_error(
                    TypeErrorCode::T0002,
                    "cannot infer tuple type for index access; add a type annotation",
                    span,
                )),
            }
        }
        Expr::Loop { body, span } => {
            let break_var = ctx.fresh_var();
            let saved_break = ctx.push_break_type(break_var.clone());
            ctx.enter_loop();
            infer_block(body, ctx, fun_generalizations)?;
            ctx.exit_loop();
            ctx.pop_break_type(saved_break);
            let _ = span;
            Ok(break_var)
        }
        Expr::Path(segments, span) => {
            // For 2-segment paths, first try TypeName::member (static methods, enum variants).
            if let [type_name, member_name] = segments.as_slice() {
                if let Some(fun_ty) = ctx.get_method_type(type_name, member_name).cloned() {
                    return Ok(fun_ty);
                }
                // Try builtin static constructors registered as joined-path poly schemes (e.g. "List::new").
                let joined = format!("{type_name}::{member_name}");
                if let Some(ty) = ctx.lookup(&joined) {
                    return Ok(ty);
                }
                // Static method on a generic struct/enum registered as a polymorphic
                // method scheme (e.g. native `List::new`). Resolving it here — from the
                // method scheme env rather than the prelude's joined-key schemes — lets
                // std::core reference its own static methods (e.g. `List::new()` inside
                // `List::map`) regardless of how the prelude is seeded.
                if let Some((scheme, _)) = ctx
                    .method_scheme_for(type_name, member_name)
                    .map(|(s, t)| (s.clone(), t.clone()))
                {
                    return Ok(ctx.instantiate(&scheme));
                }
                if let Some(info) = ctx.get_enum(type_name).cloned() {
                    if let Some(variant) = info.variants.iter().find(|v| v.name == *member_name) {
                        if variant.fields.is_empty() {
                            let type_args: Vec<InferType> =
                                info.type_params.iter().map(|_| ctx.fresh_var()).collect();
                            return Ok(InferType::Named(type_name.clone(), type_args));
                        }
                    }
                }
            }
            let path_str = segments.join("::");
            Err(MetelError::type_error(
                TypeErrorCode::T0003,
                format!("unresolved path `{path_str}`"),
                span,
            ))
        }
        Expr::Closure {
            captures,
            call_multiplicity,
            call_mutation,
            params,
            return_type,
            body,
            span,
            ..
        } => {
            let param_types: Vec<InferType> = params
                .iter()
                .map(|p| {
                    if let Some(ann) = &p.type_ann {
                        ann_to_infer(ann, ctx)
                    } else {
                        ctx.fresh_var()
                    }
                })
                .collect();
            // Not rewritten to `map_or_else` (clippy's own suggestion): both
            // closures would capture `ctx` mutably, and `map_or_else` requires
            // constructing both simultaneously as arguments, which the borrow
            // checker rejects (unlike this sequential match).
            let ret_ty = match &return_type {
                Some(ann) => ann_to_infer(ann, ctx),
                None => ctx.fresh_var(),
            };
            ctx.push_scope();
            for capture in captures {
                let (name, mutable) = match capture {
                    // Construction performs the closure-specific capture diagnostic. Keeping
                    // this binding writable here prevents the generic immutable-binding check
                    // from pre-empting the required `&var` diagnostic.
                    crate::ast::CaptureSpec::Owned { name, .. }
                    | crate::ast::CaptureSpec::Clone { name, .. }
                    | crate::ast::CaptureSpec::SharedRef { name, .. }
                    | crate::ast::CaptureSpec::MutRef { name, .. } => (name, true),
                };
                if let Some(ty) = ctx.lookup(name) {
                    ctx.bind_mono(name, ty, mutable);
                }
            }
            for (p, pt) in params.iter().zip(param_types.iter()) {
                ctx.bind_mono(&p.name, pt.clone(), p.mutable);
            }
            let saved_ret = ctx.push_return_type(ret_ty.clone());
            let saved_loop_depth = ctx.push_loop_depth_reset();
            let body_ty = infer_block(body, ctx, fun_generalizations)?;
            ctx.pop_loop_depth(saved_loop_depth);
            constrain_with_read_copy(ctx, body_ty, ret_ty.clone(), body.span.clone());
            ctx.pop_return_type(saved_ret);
            ctx.pop_scope();
            ctx.record_closure_return_type(span.clone(), ret_ty.clone());
            Ok(InferType::Fun(
                param_types,
                Box::new(ret_ty),
                *call_multiplicity,
                crate::types::UseMultiplicity::Move,
                *call_mutation,
            ))
        }
        Expr::Match(m) => infer_match(m, ctx, fun_generalizations),
        Expr::PropagateError { expr, span } => {
            infer_propagate_error(expr, span, ctx, fun_generalizations)
        }
        // Issue #229: `return`/`break`/`continue` as expressions of type `!`.
        Expr::Return(r) => {
            let ret_ty = match &r.value {
                Some(e) => infer_expr(e, ctx, fun_generalizations)?,
                None => InferType::unit(),
            };
            if let Some(expected) = ctx.current_return_type().cloned() {
                constrain_with_read_copy(ctx, ret_ty, expected, r.span.clone());
            }
            Ok(InferType::never())
        }
        Expr::Break(b) => {
            if !ctx.is_in_loop() {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0021,
                    "`break` used with no enclosing loop",
                    &b.span,
                ));
            }
            let break_ty = match &b.value {
                Some(e) => infer_expr(e, ctx, fun_generalizations)?,
                None => InferType::unit(),
            };
            if let Some(expected) = ctx.current_break_type().cloned() {
                constrain_with_read_copy(ctx, break_ty, expected, b.span.clone());
            }
            Ok(InferType::never())
        }
        Expr::Continue(span) => {
            if !ctx.is_in_loop() {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0021,
                    "`continue` used with no enclosing loop",
                    span,
                ));
            }
            Ok(InferType::never())
        }
    }
}
