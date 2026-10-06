use super::{
    AssignOp, AssignTarget, Expr, ForInit, FunGeneralization, GenericBound, HashMap, InferContext,
    InferType, MetelError, Param, SignatureEnv, Stmt, Substitution, Type, TypeErrorCode, TypeExpr,
    TypeVar, ann_to_infer, builtin_pattern_method_type, chain_provides_mut_access,
    check_field_visibility, constrain_with_read_copy, infer_binop, infer_block,
    infer_enum_variant_literal, infer_field_assign_type, infer_literal, infer_match,
    infer_propagate_error, infer_struct_literal, infer_to_type_for_from, infer_tuple_assign_type,
    infer_type_name, infer_type_to_type, infer_unaryop, is_shared_reference_chain, named_type_name,
    peel_all_references, record_projection_base_expr, resolve_row_bound_field,
    signature_type_expr_to_infer, type_expr_to_infer_with_generics, type_to_infer,
};
use crate::pipeline::type_checking::type_engine::{GenericMethodEntailment, TypeScheme};

/// Enforce RFC-0173 D6(2) for the direct parameter-passing shape.  General
/// unification still relates the two signatures; this check supplies the one
/// fact unification must not invent: that a declared argument grants every
/// bound required by the callee's corresponding parameter.
fn check_forwarded_generic_bounds(
    callee_name: &str,
    scheme: &TypeScheme,
    renaming: &HashMap<TypeVar, TypeVar>,
    param_ty: &InferType,
    arg_ty: &InferType,
    span: &crate::data::ast::Span,
    ctx: &InferContext,
) -> Result<(), MetelError> {
    let (InferType::Var(param_var), InferType::Var(arg_var)) = (param_ty, arg_ty) else {
        return Ok(());
    };
    let Some((index, _)) = scheme
        .quantified_vars
        .iter()
        .enumerate()
        .find(|(_, original)| {
            renaming
                .get(original)
                .is_some_and(|fresh| fresh == param_var)
        })
    else {
        return Ok(());
    };
    let available = ctx.bounds_for_type_var(*arg_var).unwrap_or_default();
    // An open-row parameter is represented by the anonymous type variable of
    // its `{ ..R }` parameter, rather than by `R` itself.  It consequently has
    // no declared type-parameter name, but its `Row`/`AllFields` bounds still
    // identify it as an abstract generic row.  Do not apply this rule to an
    // ordinary inference variable: only a declared parameter or an open-row
    // parameter can forward an entitlement from a generic body.
    let argument_name = ctx.declared_type_param_name(*arg_var);
    let is_open_row_parameter = available
        .iter()
        .any(|bound| matches!(bound, GenericBound::Row(_) | GenericBound::AllFields { .. }));
    if argument_name.is_none() && !is_open_row_parameter {
        return Ok(());
    }
    // RFC-0121 §4 / RFC-0123: passing an abstract open-row parameter by value
    // to another open-row parameter with named fields can discard fields that
    // neither signature names. That is sound only when the caller explicitly
    // grants `Copy` for every such field; concrete arguments remain
    // construction's responsibility. A tail-only `{ ..R }` parameter does not
    // narrow its argument, so its ordinary field-wise bound forwarding below is
    // sufficient.
    let required = scheme.bounds.get(index).map_or(&[][..], Vec::as_slice);
    let callee_narrows_by_value = required
        .iter()
        .any(|bound| matches!(bound, GenericBound::Row(row) if !row.fields.is_empty()));
    if scheme.open_row_params.get(index).copied().unwrap_or(false)
        && is_open_row_parameter
        && callee_narrows_by_value
        && !available.iter().any(|bound| {
            matches!(bound, GenericBound::AllFields { aspects, .. } if aspects.iter().any(|aspect| aspect == "Copy"))
        })
    {
        return Err(MetelError::type_error(
            TypeErrorCode::T0033,
            format!(
                "passing an abstract open-row parameter by value to `{callee_name}` may forget \
                 fields that are not `Copy`; add `where all R: Copy` to this declaration \
                 (RFC-0121 §4)"
            ),
            span,
        ));
    }
    let granted = |need: &GenericBound| {
        available.iter().any(|have| match (have, need) {
            (GenericBound::Aspect(left), GenericBound::Aspect(right)) => left == right,
            (GenericBound::Row(left), GenericBound::Row(right)) => {
                format!("{left:?}") == format!("{right:?}")
            }
            (
                GenericBound::AllFields {
                    aspects: left_aspects,
                    except: left_except,
                },
                GenericBound::AllFields {
                    aspects: right_aspects,
                    except: right_except,
                },
            ) => left_aspects == right_aspects && left_except == right_except,
            _ => false,
        })
    };
    if let Some(missing) = required.iter().find(|need| !granted(need)) {
        return Err(MetelError::type_error(
            TypeErrorCode::T0012,
            format!(
                "{} does not satisfy required bound `{missing}` for generic call to \
                 `{callee_name}`",
                argument_name.map_or_else(
                    || "open-row parameter".to_owned(),
                    |name| format!("type parameter `{name}`"),
                )
            ),
            span,
        ));
    }
    Ok(())
}

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
                    let elem_from_scheme = if let InferType::Named(name, type_args, ..) =
                        &resolved_iter
                    {
                        ctx.method_scheme_for(name, "next")
                            .and_then(|(scheme, struct_tvars)| {
                                let mut subst = Substitution::new();
                                for (&tv, concrete) in struct_tvars.iter().zip(type_args.iter()) {
                                    subst.bind(tv, concrete.clone());
                                }
                                match subst.apply(&scheme.ty) {
                                    InferType::Fun(_, ret, ..) => match *ret {
                                        InferType::Named(n, mut args, ..)
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
            if let Some(fields) = ctx.get_struct_fields(name)
                && fields.is_empty()
            {
                let type_args: Vec<InferType> = ctx
                    .get_struct_type_params(name)
                    .cloned()
                    .unwrap_or_default()
                    .into_iter()
                    .map(|_| ctx.fresh_var())
                    .collect();
                // metel-core#1137: `name` is a bare identifier written right
                // here in this module's own source, so it's always resolvable
                // from this module's own scope -- the same reasoning #1129
                // uses for a written type annotation.
                let type_id = ctx
                    .registry()
                    .resolve_type_id(ctx.current_module_path(), name);
                return Ok(InferType::Named(
                    name.clone(),
                    type_args,
                    crate::data::types::NominalId(type_id),
                ));
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
                return Ok(InferType::SizedArray(Box::new(ctx.fresh_var()), 0));
            }
            let first_ty = infer_expr(&elems[0], ctx, fun_generalizations)?;
            for elem in &elems[1..] {
                let ty = infer_expr(elem, ctx, fun_generalizations)?;
                ctx.add_constraint(ty, first_ty.clone(), span.clone());
            }
            // RFC-0053/RFC-0177: an unannotated literal is an owning fixed-size
            // array. It can still coerce to `[T]` at an explicit view-typed use
            // site; keeping the intrinsic length here is what lets later lookup
            // distinguish construction from that coercion.
            Ok(InferType::SizedArray(
                Box::new(first_ty),
                elems.len() as u64,
            ))
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
            if let Some(name) = super::super::overload::callee_name(callee)
                && ctx.is_overloaded(name)
            {
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
                        ));
                    }
                };
                let entries = ctx.overload_candidates(name).unwrap();
                let entry = if let Some(entry) = super::super::overload::select(entries, &arg_types)
                {
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

            // Check for opaque-returning function and do dedicated instantiation
            if let Some(callee_name) = super::super::overload::callee_name(callee)
                && let Some(scheme) = ctx.poly_scheme(callee_name)
                && !scheme.opaque_returns.is_empty()
            {
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
                ctx.stamp_row_remainders(span);

                if let InferType::Fun(params, ret, ..) = instantiated_ty {
                    // Constrain arguments to match the instantiated function type
                    for (arg_ty, param) in arg_infer.iter().zip(params.iter()) {
                        ctx.add_constraint(arg_ty.clone(), param.clone(), span.clone());
                    }

                    // Register aspect bounds and mark opacity guards for each opaque return
                    for (i, opaque) in scheme.opaque_returns.iter().enumerate() {
                        if let Some((aspect, _)) = opaque
                            && let Some(&orig_tv) = scheme.quantified_vars.get(i)
                            && let Some(&fresh_tv) = renaming.get(&orig_tv)
                        {
                            ctx.register_type_var_bound(fresh_tv, aspect.clone());
                            ctx.mark_opaque_return_var(fresh_tv);
                        }
                    }

                    return Ok(*ret);
                }
            }

            // RFC-0173 D6(2): a generic body cannot defer a callee's bound
            // check to construction.  Instantiate the named callee here so a
            // direct declared parameter argument is checked against the
            // callee's own scheme while the caller's declared bounds are in
            // scope.  Concrete arguments retain construction's ordinary
            // call-site diagnostic.
            if let Some(callee_name) = super::super::overload::callee_name(callee)
                && let Some(scheme) = ctx.poly_scheme(callee_name)
                && !scheme.quantified_vars.is_empty()
            {
                let (callee_ty, renaming) = ctx.instantiate_with_renaming(&scheme);
                let InferType::Fun(params, ret, ..) = callee_ty else {
                    return Err(MetelError::internal(
                        "function scheme is not a function type",
                    ));
                };
                if params.len() != args.len() {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0004,
                        format!("expected {} argument(s), got {}", params.len(), args.len()),
                        span,
                    ));
                }
                let arg_tys: Vec<InferType> = args
                    .iter()
                    .map(|arg| infer_expr(arg, ctx, fun_generalizations))
                    .collect::<Result<_, _>>()?;
                for (arg_ty, param_ty) in arg_tys.iter().zip(params.iter()) {
                    check_forwarded_generic_bounds(
                        callee_name,
                        &scheme,
                        &renaming,
                        param_ty,
                        arg_ty,
                        span,
                        ctx,
                    )?;
                    ctx.add_constraint(arg_ty.clone(), param_ty.clone(), span.clone());
                }
                return Ok(*ret);
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
                        if *then_call == crate::data::types::CallMultiplicity::Once
                            || *else_call == crate::data::types::CallMultiplicity::Once
                        {
                            crate::data::types::CallMultiplicity::Once
                        } else {
                            crate::data::types::CallMultiplicity::Many
                        },
                        if *then_use == crate::data::types::UseMultiplicity::Move
                            || *else_use == crate::data::types::UseMultiplicity::Move
                        {
                            crate::data::types::UseMultiplicity::Move
                        } else {
                            crate::data::types::UseMultiplicity::Copy
                        },
                        if *then_mut == crate::data::types::CallMutation::Mutating
                            || *else_mut == crate::data::types::CallMutation::Mutating
                        {
                            crate::data::types::CallMutation::Mutating
                        } else {
                            crate::data::types::CallMutation::Reading
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
            // RFC-0121 remainder (#1306, #1310): a row extension preserves its
            // explicitly declared fields while its tail supplies every other
            // field. Construction has already solved the tail for a concrete
            // value; in an abstract body, a row-bound tail is handled by the
            // ordinary variable path below.
            if let InferType::RowExtend { fields, tail } = &peeled {
                if let Some((_, ty)) = fields.iter().find(|(name, _)| name == field) {
                    return Ok(ty.clone());
                }
                match tail.as_ref() {
                    InferType::Record(tail_fields)
                    | InferType::Residual {
                        fields: tail_fields,
                        ..
                    } => {
                        return tail_fields
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
                    InferType::Var(tv)
                        if let Some(result) = resolve_row_bound_field(ctx, *tv, field, span) =>
                    {
                        return result;
                    }
                    InferType::Var(tv) if let Some(param) = ctx.declared_type_param_name(*tv) => {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0035,
                            format!(
                                "field `{field}` is not granted by the declared bounds of type \
                                 parameter `{param}`"
                            ),
                            span,
                        ));
                    }
                    _ => {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0003,
                            format!("no field `{field}` on {peeled}"),
                            span,
                        ));
                    }
                }
            }
            // Abstract, row-bounded generic type parameter (`<record T: { x: f64, .. }>`):
            // resolve `field` against the row bound the same way MethodCall's slow path
            // (below) resolves a method against an aspect bound, instead of falling
            // through to the nominal-struct path, which can't name a struct for a bare
            // TypeVar and would otherwise mislead with "add a type annotation" — no
            // annotation fixes a missing row-bound field.
            if let InferType::Var(tv) = &peeled
                && let Some(result) = resolve_row_bound_field(ctx, *tv, field, span)
            {
                return result;
            }
            if let InferType::Var(tv) = &peeled
                && let Some(param) = ctx.declared_type_param_name(*tv)
            {
                // RFC-0173 D2: only a row bound grants a field of a declared parameter.
                return Err(MetelError::type_error(
                    TypeErrorCode::T0035,
                    format!(
                        "field `{field}` is not granted by the declared bounds of type \
                         parameter `{param}`"
                    ),
                    span,
                ));
            }
            let struct_name = named_type_name(&obj_ty).ok_or_else(|| {
                MetelError::type_error(
                    TypeErrorCode::T0002,
                    "cannot infer struct type for field access; add a type annotation",
                    span,
                )
            })?;
            let type_args = match &obj_ty {
                InferType::Named(_, args, ..) => args.clone(),
                InferType::Reference(inner) | InferType::MutReference(inner) => {
                    match inner.as_ref() {
                        InferType::Named(_, args, ..) => args.clone(),
                        _ => vec![],
                    }
                }
                _ => vec![],
            };
            // metel-core#1222: the value's own type already carries the
            // declaration's identity (populated when its annotation was
            // resolved from the declaring module, e.g. a function's return
            // type) -- prefer it over a bare-name lookup, which conflates
            // same-named structs declared in different modules.
            let nominal_struct_id = match &peeled {
                InferType::Named(_, _, id) => id.get(),
                _ => None,
            };
            let (field_entry, declaring_module, visibility, resolved_type_params) =
                super::resolve_struct_field_by_identity(
                    ctx,
                    nominal_struct_id,
                    &struct_name,
                    field,
                    span,
                )?;
            check_field_visibility(
                &field_entry,
                &struct_name,
                ctx.current_module_path(),
                declaring_module.as_ref(),
                visibility.as_ref(),
                span,
                "access",
            )?;
            let raw_ty = field_entry.ty.clone();
            // For generic structs, substitute declared type params with the resolved args.
            if let Some(type_params) = resolved_type_params {
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
            if let InferType::Array(elem) | InferType::SizedArray(elem, _) = &peeled_recv {
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
                    Some(crate::data::ast::ReceiverKind::RefMut)
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

            // A record receiver (`{ w = 2, h = 3 }.area()`) dispatches through the
            // impls whose target is a record type and whose row condition it satisfies.
            if matches!(
                &peeled_recv,
                InferType::Record(_) | InferType::Residual { .. }
            ) && !ctx
                .registry()
                .record_method_scheme_variants_for(method)
                .is_empty()
            {
                return infer_record_method_call(
                    receiver,
                    &recv_ty,
                    &peeled_recv,
                    method,
                    &arg_tys,
                    span,
                    ctx,
                );
            }

            // RFC-0173 D6: record-target conditional methods can be selected
            // against an abstract open-row parameter only when its declared
            // row/all-fields bounds entail the selected impl's requirements.
            // A concrete record continues through `infer_record_method_call`
            // above, where its actual fields are checked directly.
            if let InferType::Var(receiver_tv) = &peeled_recv {
                let record_candidates = ctx.registry().record_method_scheme_variants_for(method);
                if !record_candidates.is_empty()
                    && ctx.bounds_for_type_var(*receiver_tv).is_some_and(|bounds| {
                        bounds.iter().any(|bound| {
                            matches!(bound, GenericBound::Row(_) | GenericBound::AllFields { .. })
                        })
                    })
                {
                    let assumptions = ctx.current_aspect_assumptions();
                    let Some((scheme, receiver_tvars, _)) = record_candidates
                        .iter()
                        .rev()
                        .find(|(scheme, receiver_tvars, _)| {
                            ctx.registry().generic_method_receiver_bounds_hold(
                                ctx.current_module_path(),
                                scheme,
                                receiver_tvars,
                                std::slice::from_ref(&peeled_recv),
                                GenericMethodEntailment {
                                    aspect_assumptions: &assumptions,
                                    bounds: ctx.type_param_bounds(),
                                    negative_bounds: ctx.negative_type_param_bounds(),
                                },
                            )
                        })
                        .cloned()
                    else {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0035,
                            format!(
                                "method `{method}` is not granted by the declared bounds of this \
                                 record parameter; its conditional implementation requirements are \
                                 not entailed"
                            ),
                            span,
                        ));
                    };
                    return infer_record_method_call_with_scheme(
                        &RecordMethodCall {
                            receiver,
                            recv_ty: &recv_ty,
                            peeled_recv: &peeled_recv,
                            method,
                            arg_tys: &arg_tys,
                            span,
                        },
                        ctx,
                        &scheme,
                        &receiver_tvars,
                    );
                }
            }

            // Fast path: concrete named type — look up method as usual.
            if let Some(struct_name) = named_type_name(&recv_ty) {
                let recv_type_args = match &recv_ty {
                    InferType::Named(_, args, ..) => args.clone(),
                    InferType::Reference(inner) | InferType::MutReference(inner) => {
                        match inner.as_ref() {
                            InferType::Named(_, args, ..) => args.clone(),
                            _ => vec![],
                        }
                    }
                    _ => vec![],
                };

                // A conditional generic impl is visible in a generic body only
                // when its receiver requirements are entailed by the body's
                // declared bounds.  Concrete receivers keep the existing
                // construction-time bound diagnostic; the definition-time
                // check matters when an argument is an opaque parameter.
                let generic_candidates = ctx
                    .registry()
                    .method_scheme_variants_for(ctx.current_module_path(), &struct_name, method)
                    .to_vec();
                let declared_receiver_param = recv_type_args.iter().find_map(|arg| {
                    let InferType::Var(tv) = arg else {
                        return None;
                    };
                    ctx.declared_type_param_name(*tv)
                        .map(|name| (name.to_string(), *tv))
                });
                let assumptions = ctx.current_aspect_assumptions();
                // An inherited aspect default is checked with `Self: Aspect`
                // in scope. Its receiver may already have been constrained to
                // a nominal generic target, but that does not erase the aspect
                // guarantee: resolving another method of the same aspect must
                // remain legal without re-proving which conditional impl will
                // supply it at construction time.
                let self_aspect_grants_method = ctx
                    .type_params()
                    .get("Self")
                    .and_then(|tv| ctx.bounds_for_type_var(*tv))
                    .is_some_and(|bounds| {
                        generic_candidates.iter().any(|(_, _, aspect)| {
                            aspect.as_ref().is_some_and(|candidate| {
                                bounds.iter().any(|bound| {
                                    bound.aspect_name().is_some_and(|known| known == candidate)
                                })
                            })
                        })
                    });
                let generic_method = generic_candidates
                    .iter()
                    .rev()
                    .find(|(scheme, receiver_tvars, _)| {
                        ctx.registry().generic_method_receiver_bounds_hold(
                            ctx.current_module_path(),
                            scheme,
                            receiver_tvars,
                            &recv_type_args,
                            GenericMethodEntailment {
                                aspect_assumptions: &assumptions,
                                bounds: ctx.type_param_bounds(),
                                negative_bounds: ctx.negative_type_param_bounds(),
                            },
                        )
                    })
                    .cloned()
                    // A concrete receiver is diagnosed by construction's
                    // scheme-bound check, which can render its actual type.
                    .or_else(|| {
                        (declared_receiver_param.is_none() || self_aspect_grants_method)
                            .then(|| generic_candidates.last().cloned())
                            .flatten()
                    });

                // Try concrete method_env first; fall back to a generic method scheme.
                let method_ty = if let Some(ty) = ctx.get_method_type(&struct_name, method).cloned()
                {
                    ty
                } else if let Some((scheme, struct_tvars, _)) = generic_method {
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
                            // RFC-0121 §2: a pending `Rest` derivation watches the fresh
                            // `R` var, which the local pin alone never binds in the
                            // solver -- bind it there too, so the derivation can fire.
                            if !scheme.row_remainders.is_empty() {
                                ctx.add_constraint(
                                    InferType::Var(fresh),
                                    arg.clone(),
                                    span.clone(),
                                );
                            }
                        }
                    }
                    ctx.stamp_row_remainders(span);
                    pin.apply(&instance)
                } else if let Some((param, _)) = declared_receiver_param
                    && !generic_candidates.is_empty()
                {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0035,
                        format!(
                            "method `{method}` is not granted by the declared bounds of type \
                             parameter `{param}`; its conditional implementation requirements \
                             are not entailed"
                        ),
                        span,
                    ));
                } else if ctx
                    .registry()
                    .record_method_variant_for(ctx.current_module_path(), method, &peeled_recv)
                    .is_some()
                {
                    // Brand-keyed impls first, then a record-target impl whose row this
                    // nominal record's fields satisfy (RFC-0121 §3, legality-2).
                    return infer_record_method_call(
                        receiver,
                        &recv_ty,
                        &peeled_recv,
                        method,
                        &arg_tys,
                        span,
                        ctx,
                    );
                } else {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!("no method `{method}` on `{struct_name}`"),
                        span,
                    ));
                };

                if matches!(
                    ctx.get_method_receiver_kind(&struct_name, method),
                    Some(crate::data::ast::ReceiverKind::RefMut)
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
                if matches!(receiver_kind, Some(crate::data::ast::ReceiverKind::RefMut))
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
            if let InferType::Var(tv) = &peeled_recv_for_bounds
                && let Some(aspect_names) = ctx.bounds_for_type_var(*tv)
            {
                let self_generic_map: HashMap<String, TypeVar> =
                    std::iter::once(("Self".to_string(), *tv)).collect();
                for aspect_name in aspect_names.iter().filter_map(GenericBound::aspect_name) {
                    if let Some(methods) = ctx.get_aspect_method_defs(aspect_name).cloned()
                        && let Some(method_def) = methods.iter().find(|m| m.name == *method)
                    {
                        // The method's own generic parameters (`fun sink<U>(self, x: U)`)
                        // are fresh at every call. Left unmapped they would resolve to a
                        // concrete type named `U`, or -- worse -- to the caller's own
                        // parameter of the same name (RFC-0173).
                        let mut method_generic_map = self_generic_map.clone();
                        for gp in &method_def.generics {
                            method_generic_map.insert(gp.name.clone(), ctx.fresh_type_var_raw());
                        }
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
                                other => {
                                    type_expr_to_infer_with_generics(other, &method_generic_map)
                                }
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
                                    declared_params.len(),
                                    args.len()
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
                                let param_ty =
                                    type_expr_to_infer_with_generics(ann, &method_generic_map);
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
                        if matches!(receiver_kind, Some(crate::data::ast::ReceiverKind::RefMut))
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
                let bounds_list = aspect_names
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" + ");
                // RFC-0173 D2: on a declared parameter this is "not granted by the
                // declared bounds"; on any other bounded variable (an opaque
                // `extends Aspect` return value) it stays an ordinary missing method.
                return Err(match ctx.declared_type_param_name(*tv) {
                    Some(param) => MetelError::type_error(
                        TypeErrorCode::T0035,
                        format!(
                            "method `{method}` is not granted by the declared bounds of type \
                             parameter `{param}` (bounds: {bounds_list})"
                        ),
                        span,
                    ),
                    None => MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!("no method `{method}` on type parameter (bounds: {bounds_list})"),
                        span,
                    ),
                });
            }

            if let InferType::Var(tv) = &peeled_recv_for_bounds
                && let Some(param) = ctx.declared_type_param_name(*tv)
            {
                // RFC-0173 D2: a declared parameter with no bounds grants no method.
                return Err(MetelError::type_error(
                    TypeErrorCode::T0035,
                    format!(
                        "method `{method}` is not granted by the declared bounds of type \
                         parameter `{param}` (it has none)"
                    ),
                    span,
                ));
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
        Expr::RecordProjection {
            path,
            path_span,
            fields,
            span,
        } => {
            let base_expr = record_projection_base_expr(path, path_span);
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
                InferType::Named(_, args, ..) => args.clone(),
                InferType::Reference(inner) | InferType::MutReference(inner) => {
                    match inner.as_ref() {
                        InferType::Named(_, args, ..) => args.clone(),
                        _ => vec![],
                    }
                }
                _ => vec![],
            };
            // metel-core#1137: carry the base value's own identity through a
            // full-width projection instead of dropping it -- the base could be
            // of a type from any module, so this is more correct than (and must
            // not be re-derived from) `ctx.current_module_path()`.
            let struct_id = match &base_ty {
                InferType::Named(_, _, id) => id.get(),
                InferType::Reference(inner) | InferType::MutReference(inner) => {
                    match inner.as_ref() {
                        InferType::Named(_, _, id) => id.get(),
                        _ => None,
                    }
                }
                _ => None,
            };
            // metel-core#1222: prefer the identity captured above over a
            // bare-name lookup, which conflates same-named structs declared
            // in different modules.
            let (declared_fields, resolved_type_params) = if let Some(id) = struct_id
                && let Some(fields) = ctx.registry().struct_fields_by_id(id)
            {
                (
                    fields.clone(),
                    ctx.registry().struct_type_params_by_id(id).cloned(),
                )
            } else {
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
                (fields, ctx.get_struct_type_params(&struct_name).cloned())
            };
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
                let ty = if let Some(type_params) = &resolved_type_params {
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
                return Ok(InferType::Named(
                    struct_name,
                    type_args,
                    crate::data::types::NominalId(struct_id),
                ));
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
                    format!(
                        "cannot cast `{source_resolved}` to `{target_resolved}` — no `impl From<{source_resolved}> for {target_resolved}` found"
                    ),
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
        Expr::Path(segments, _, span) => {
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
                if let Some(info) = ctx.get_enum(type_name).cloned()
                    && let Some(variant) = info.variants.iter().find(|v| v.name == *member_name)
                {
                    if variant.fields.is_empty() {
                        let type_args: Vec<InferType> =
                            info.type_params.iter().map(|_| ctx.fresh_var()).collect();
                        // metel-core#1137: `type_name` is written right here in
                        // this module's own source (a 2-segment path segment),
                        // always resolvable from this module's own scope.
                        let type_id = ctx
                            .registry()
                            .resolve_type_id(ctx.current_module_path(), type_name);
                        return Ok(InferType::Named(
                            type_name.clone(),
                            type_args,
                            crate::data::types::NominalId(type_id),
                        ));
                    }
                    // metel-core#1108: a fieldful variant has no bare-value
                    // form -- Metel's grammar has no positional/tuple-variant
                    // syntax, only `Variant { field: Type, ... }`, so there is
                    // no "declared order" a constructor call could mean
                    // without inventing that as new language semantics (a
                    // design question of its own, not a bug fix). Point at
                    // the two forms that do exist instead of the generic
                    // "unresolved path".
                    let fields = variant
                        .fields
                        .iter()
                        .map(|f| format!("{} = ...", f.name))
                        .collect::<Vec<_>>()
                        .join(", ");
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0003,
                        format!(
                            "`{type_name}::{member_name}` is a fieldful variant and has no \
                                 bare-value form -- construct it with `{type_name}::{member_name} \
                                 {{ {fields} }}`, or destructure it in a `match`"
                        ),
                        span,
                    ));
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
                    crate::data::ast::CaptureSpec::Owned { name, .. }
                    | crate::data::ast::CaptureSpec::Clone { name, .. }
                    | crate::data::ast::CaptureSpec::SharedRef { name, .. }
                    | crate::data::ast::CaptureSpec::MutRef { name, .. } => (name, true),
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
                crate::data::types::UseMultiplicity::Move,
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

/// Type a method call whose receiver is a record, through the record-target impl
/// candidates (RFC-0121 §3). The receiver var of the chosen candidate's scheme is
/// pinned to the receiver's own type; the arguments are constrained against the
/// remaining parameters and the call has the declared return type.
fn infer_record_method_call(
    receiver: &Expr,
    recv_ty: &InferType,
    peeled_recv: &InferType,
    method: &str,
    arg_tys: &[InferType],
    span: &crate::data::ast::Span,
    ctx: &mut InferContext,
) -> Result<InferType, MetelError> {
    let Some((scheme, receiver_tvars, _)) = ctx
        .registry()
        .record_method_variant_for(ctx.current_module_path(), method, peeled_recv)
        .cloned()
    else {
        return Err(MetelError::type_error(
            TypeErrorCode::T0003,
            format!("no method `{method}` on this record type: no `extend` for it provides one"),
            span,
        ));
    };
    infer_record_method_call_with_scheme(
        &RecordMethodCall {
            receiver,
            recv_ty,
            peeled_recv,
            method,
            arg_tys,
            span,
        },
        ctx,
        &scheme,
        &receiver_tvars,
    )
}

struct RecordMethodCall<'a> {
    receiver: &'a Expr,
    recv_ty: &'a InferType,
    peeled_recv: &'a InferType,
    method: &'a str,
    arg_tys: &'a [InferType],
    span: &'a crate::data::ast::Span,
}

fn infer_record_method_call_with_scheme(
    call: &RecordMethodCall<'_>,
    ctx: &mut InferContext,
    scheme: &TypeScheme,
    receiver_tvars: &[TypeVar],
) -> Result<InferType, MetelError> {
    let RecordMethodCall {
        receiver,
        recv_ty,
        peeled_recv,
        method,
        arg_tys,
        span,
    } = *call;
    let (instance, renaming) = ctx.instantiate_with_renaming(scheme);
    let mut pin = Substitution::new();
    for &tv in receiver_tvars {
        if let Some(&fresh) = renaming.get(&tv) {
            pin.bind(fresh, peeled_recv.clone());
        }
    }
    let method_ty = pin.apply(&instance);
    if matches!(
        ctx.registry().record_method_receiver_kind(method),
        Some(crate::data::ast::ReceiverKind::RefMut)
    ) && !chain_provides_mut_access(recv_ty)
    {
        if is_shared_reference_chain(recv_ty) {
            return Err(MetelError::type_error(
                TypeErrorCode::T0006,
                format!("cannot call `&var self` method `{method}` through a shared reference"),
                span,
            ));
        }
        if let Expr::Ident(name, recv_span) = receiver {
            let _ = ctx.lookup_for_write(name, recv_span)?;
        }
    }
    let InferType::Fun(params, ret, ..) = &method_ty else {
        return Err(MetelError::internal("record method type is not a function"));
    };
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
    Ok(*ret.clone())
}
