use super::{
    AssocResolveCtx, ConstructCtx, Expr, GenericBound, HashMap, InferType, MetelError,
    MethodDispatch, RowConstraint, Span, Substitution, SymbolId, Type, TypeDefinitionRegistry,
    TypeErrorCode, TypeExpr, TypeScheme, TypeVar, TypeVarGenerator, TypedExpr, construct_expr,
    infer_type_to_type, maybe_dyn_coerce, reject_dynamic_array_where_sized_expected, type_engine,
    type_expr_to_infer_with_assoc_ctx, type_to_infer, unify,
};

fn is_through_shared_reference(expr: &TypedExpr) -> bool {
    match expr {
        TypedExpr::FieldAccess { object, .. }
        | TypedExpr::TupleAccess { object, .. }
        | TypedExpr::Index { object, .. } => {
            matches!(object.ty(), Type::Reference(_)) || is_through_shared_reference(object)
        }
        _ => matches!(expr.ty(), Type::Reference(_)),
    }
}

/// Build a typed Call expression.
///
/// For polymorphic callees (Idents in `scheme_env` whose type still contains free
/// vars), re-instantiate the scheme against the concrete argument types using
/// local unification. This is the Pass 2 counterpart of the inline
/// solve-and-generalize done in `infer_fun_decl`.
// Exhaustive match over every AST/type-system variant; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
// arch-implements: ["arch.move-check.requirement-3"]
pub(super) fn construct_call(
    callee: &Expr,
    type_args: &[TypeExpr],
    args: &[Expr],
    span: &Span,
    expected_ty: Option<&Type>,
    ctx: &mut ConstructCtx,
) -> Result<TypedExpr, MetelError> {
    // Overloaded free-function call (METEL-180): select the candidate whose
    // parameter types exactly match the argument types and stamp its SymbolId
    // into the call; the evaluator dispatches through its symbol registry.
    // No implicit coercion participates in selection.
    if let Some(name) = super::super::overload::callee_name(callee)
        && ctx.overloads.contains_key(name)
    {
        let typed_args: Vec<TypedExpr> = args
            .iter()
            .map(|a| construct_expr(a, None, ctx))
            .collect::<Result<_, _>>()?;
        let arg_types: Vec<Type> = typed_args.iter().map(|a| a.ty().clone()).collect();
        let entries = &ctx.overloads[name];
        match super::super::overload::select(entries, &arg_types) {
            Some(entry) => {
                let fun_ty =
                    crate::data::types::default_fun_type(entry.params.clone(), entry.ret.clone());
                let typed_callee = TypedExpr::Ident(
                    name.to_string(),
                    ctx.binding_id_at(callee.span()),
                    fun_ty,
                    callee.span().clone(),
                );
                return Ok(TypedExpr::Call {
                    callee: Box::new(typed_callee),
                    args: typed_args,
                    ty: entry.ret.clone(),
                    callee_id: Some(entry.symbol_id),
                    span: span.clone(),
                });
            }
            // No exact match: fall back to a non-overload binding of the
            // same name (prelude/imports), mirroring the inference pass.
            // The normal path below re-constructs the arguments.
            None if ctx.lookup(name).is_some() || ctx.scheme_env.contains_key(name) => {}
            None => {
                return Err(super::super::overload::no_match_error(
                    name, &arg_types, entries, span,
                ));
            }
        }
    }
    // For monomorphic callee identifiers already in scope, extract param types as hints so
    // inherently ambiguous args (bare `[]`, `None`) can resolve without requiring ascription.
    // Generic (scheme-based) callees need arg types first for instantiation — no hints there.
    let param_hints: Vec<Option<Type>> = match callee {
        Expr::Ident(name, _) => match ctx.lookup(name) {
            Some(Type::Fun(params, ..)) if params.len() == args.len() => {
                params.iter().map(|p| Some(p.clone())).collect()
            }
            _ => vec![None; args.len()],
        },
        Expr::Path(segments, _, _) => {
            let last = segments.last().map_or("", std::string::String::as_str);
            match ctx.lookup(last) {
                Some(Type::Fun(params, ..)) if params.len() == args.len() => {
                    params.iter().map(|p| Some(p.clone())).collect()
                }
                _ => vec![None; args.len()],
            }
        }
        Expr::ResolvedPath { resolved, .. } => match ctx.lookup(resolved) {
            Some(Type::Fun(params, ..)) if params.len() == args.len() => {
                params.iter().map(|p| Some(p.clone())).collect()
            }
            _ => vec![None; args.len()],
        },
        _ => vec![None; args.len()],
    };

    let typed_args: Vec<TypedExpr> = args
        .iter()
        .zip(param_hints.iter())
        .map(|(a, hint)| {
            let typed = construct_expr(a, hint.as_ref(), ctx)?;
            reject_dynamic_array_where_sized_expected(hint.as_ref(), &typed)?;
            Ok(typed)
        })
        .collect::<Result<_, _>>()?;
    let arg_types: Vec<&Type> = typed_args
        .iter()
        .map(crate::data::typed_ast::TypedExpr::ty)
        .collect();

    // Resolve explicit type args once, outside the match.
    let explicit_tys: Option<Vec<Type>> = if type_args.is_empty() {
        None
    } else {
        Some(
            type_args
                .iter()
                .map(|te| infer_type_to_type(&ctx.type_expr_to_infer_ctx(te), span))
                .collect::<Result<_, _>>()?,
        )
    };

    let (typed_callee, fun_ty) = match callee {
        Expr::Ident(name, ident_span) if ctx.lookup(name).is_none() => {
            let scheme = ctx.scheme_env.get(name.as_str()).ok_or_else(|| {
                MetelError::type_error(
                    TypeErrorCode::T0003,
                    format!("undefined name `{name}`"),
                    ident_span,
                )
            })?;
            let (concrete, var_map) = match &explicit_tys {
                Some(tys) => instantiate_scheme_with_turbofish(
                    scheme,
                    tys,
                    span,
                    ctx.registry,
                    ctx.current_module,
                )?,
                None => {
                    match instantiate_scheme_for_call(
                        scheme,
                        &arg_types,
                        span,
                        &mut ctx.type_var_gen,
                        ctx.registry,
                        ctx.current_module,
                    ) {
                        Ok(result) => result,
                        Err(e) => {
                            // Arg-based instantiation failed (e.g. zero-arg generic call
                            // whose only free type variable appears in the return type).
                            // Try resolving it from the expected type via unification,
                            // same fallback as the qualified-path call branch below.
                            match expected_ty {
                                Some(expected) => instantiate_scheme_with_expected_ret(
                                    scheme,
                                    &arg_types,
                                    expected,
                                    span,
                                    &mut ctx.type_var_gen,
                                    ctx.registry,
                                    ctx.current_module,
                                )
                                .map_err(|_| e)?,
                                None => return Err(e),
                            }
                        }
                    }
                }
            };
            check_fun_call_bounds(name, &var_map, span, ctx.registry, ctx.current_module)?;
            check_scheme_bounds(
                name,
                scheme,
                &var_map,
                span,
                ctx.registry,
                ctx.current_module,
            )?;
            check_fun_call_assoc_eq(name, &var_map, span, ctx.registry, ctx.current_module)?;
            check_scheme_assoc_eq(
                name,
                scheme,
                &var_map,
                span,
                ctx.registry,
                ctx.current_module,
            )?;
            check_fun_call_neg_bounds(name, &var_map, span, ctx.registry, ctx.current_module)?;
            check_scheme_neg_bounds(
                name,
                scheme,
                &var_map,
                span,
                ctx.registry,
                ctx.current_module,
            )?;
            let typed = TypedExpr::Ident(
                name.clone(),
                ctx.binding_id_at(ident_span),
                concrete.clone(),
                ident_span.clone(),
            );
            (typed, concrete)
        }
        // Qualified static constructors like "List::new" / "List::from" registered as joined-key schemes.
        Expr::Path(segments, _, path_span)
            if {
                let joined = segments.join("::");
                ctx.lookup(&joined).is_none() && ctx.scheme_env.contains_key(joined.as_str())
            } =>
        {
            let joined = segments.join("::");
            let scheme = ctx.scheme_env.get(joined.as_str()).unwrap();
            let (concrete, var_map) = match &explicit_tys {
                Some(tys) => instantiate_scheme_with_turbofish(
                    scheme,
                    tys,
                    span,
                    ctx.registry,
                    ctx.current_module,
                )?,
                None => {
                    match instantiate_scheme_for_call(
                        scheme,
                        &arg_types,
                        span,
                        &mut ctx.type_var_gen,
                        ctx.registry,
                        ctx.current_module,
                    ) {
                        Ok(result) => result,
                        Err(e) => {
                            // Arg-based instantiation failed (e.g. zero-arg generic constructor).
                            // Try resolving the return type from the expected type via unification.
                            match expected_ty {
                                Some(expected) => instantiate_scheme_with_expected_ret(
                                    scheme,
                                    &arg_types,
                                    expected,
                                    span,
                                    &mut ctx.type_var_gen,
                                    ctx.registry,
                                    ctx.current_module,
                                )
                                .map_err(|_| e)?,
                                None => return Err(e),
                            }
                        }
                    }
                }
            };
            check_fun_call_bounds(&joined, &var_map, span, ctx.registry, ctx.current_module)?;
            check_scheme_bounds(
                &joined,
                scheme,
                &var_map,
                span,
                ctx.registry,
                ctx.current_module,
            )?;
            check_fun_call_assoc_eq(&joined, &var_map, span, ctx.registry, ctx.current_module)?;
            check_scheme_assoc_eq(
                &joined,
                scheme,
                &var_map,
                span,
                ctx.registry,
                ctx.current_module,
            )?;
            check_fun_call_neg_bounds(&joined, &var_map, span, ctx.registry, ctx.current_module)?;
            check_scheme_neg_bounds(
                &joined,
                scheme,
                &var_map,
                span,
                ctx.registry,
                ctx.current_module,
            )?;
            // metel-core#1093: identity only for the clean 2-segment shape
            // (`Type::member`), matching `expressions.rs`'s own boundary —
            // `None` for anything module-qualified, never guessed.
            let type_id = match segments.as_slice() {
                [type_name, _] => ctx.type_symbol_id(type_name),
                _ => None,
            };
            let typed = TypedExpr::Path {
                segments: segments.clone(),
                type_id,
                variant_id: None,
                ty: concrete.clone(),
                span: path_span.clone(),
            };
            (typed, concrete)
        }
        Expr::Path(segments, _, path_span)
            if {
                let last = segments.last().map_or("", std::string::String::as_str);
                ctx.lookup(last).is_none()
                && ctx.scheme_env.contains_key(last)
                // Only use scheme instantiation if method_env doesn't have it
                && !(segments.len() == 2
                    && ctx
                        .concrete_method(segments[0].as_str(), segments[1].as_str())
                        .is_some())
            } =>
        {
            let last = segments.last().unwrap().clone();
            let scheme = ctx.scheme_env.get(last.as_str()).unwrap();
            let (concrete, var_map) = match &explicit_tys {
                Some(tys) => instantiate_scheme_with_turbofish(
                    scheme,
                    tys,
                    span,
                    ctx.registry,
                    ctx.current_module,
                )?,
                None => instantiate_scheme_for_call(
                    scheme,
                    &arg_types,
                    span,
                    &mut ctx.type_var_gen,
                    ctx.registry,
                    ctx.current_module,
                )?,
            };
            check_fun_call_bounds(&last, &var_map, span, ctx.registry, ctx.current_module)?;
            check_scheme_bounds(
                &last,
                scheme,
                &var_map,
                span,
                ctx.registry,
                ctx.current_module,
            )?;
            check_fun_call_assoc_eq(&last, &var_map, span, ctx.registry, ctx.current_module)?;
            check_scheme_assoc_eq(
                &last,
                scheme,
                &var_map,
                span,
                ctx.registry,
                ctx.current_module,
            )?;
            check_fun_call_neg_bounds(&last, &var_map, span, ctx.registry, ctx.current_module)?;
            check_scheme_neg_bounds(
                &last,
                scheme,
                &var_map,
                span,
                ctx.registry,
                ctx.current_module,
            )?;
            // metel-core#1093: same 2-segment-only boundary as above.
            let type_id = match segments.as_slice() {
                [type_name, _] => ctx.type_symbol_id(type_name),
                _ => None,
            };
            let typed = TypedExpr::Path {
                segments: segments.clone(),
                type_id,
                variant_id: None,
                ty: concrete.clone(),
                span: path_span.clone(),
            };
            (typed, concrete)
        }
        Expr::ResolvedPath {
            resolved,
            symbol_id,
            original: _,
            span: rspan,
        } if ctx.lookup(resolved).is_none() && ctx.scheme_env.contains_key(resolved.as_str()) => {
            let scheme = ctx.scheme_env.get(resolved.as_str()).unwrap();
            let (concrete, var_map) = match &explicit_tys {
                Some(tys) => instantiate_scheme_with_turbofish(
                    scheme,
                    tys,
                    span,
                    ctx.registry,
                    ctx.current_module,
                )?,
                None => instantiate_scheme_for_call(
                    scheme,
                    &arg_types,
                    span,
                    &mut ctx.type_var_gen,
                    ctx.registry,
                    ctx.current_module,
                )?,
            };
            check_fun_call_bounds(resolved, &var_map, span, ctx.registry, ctx.current_module)?;
            check_scheme_bounds(
                resolved,
                scheme,
                &var_map,
                span,
                ctx.registry,
                ctx.current_module,
            )?;
            check_fun_call_assoc_eq(resolved, &var_map, span, ctx.registry, ctx.current_module)?;
            check_scheme_assoc_eq(
                resolved,
                scheme,
                &var_map,
                span,
                ctx.registry,
                ctx.current_module,
            )?;
            check_fun_call_neg_bounds(resolved, &var_map, span, ctx.registry, ctx.current_module)?;
            check_scheme_neg_bounds(
                resolved,
                scheme,
                &var_map,
                span,
                ctx.registry,
                ctx.current_module,
            )?;
            let typed = TypedExpr::Ident(
                resolved.clone(),
                symbol_id.map(crate::identity::BindingId::Global),
                concrete.clone(),
                rspan.clone(),
            );
            (typed, concrete)
        }
        _ => {
            let typed = construct_expr(callee, None, ctx)?;
            let ty = typed.ty().clone();
            (typed, ty)
        }
    };

    // Re-construct args with the now-known concrete param types as hints if
    // pre-construction defaulting diverged (e.g. unsuffixed integer literals in
    // turbofish calls: clamp::<i32>(5, 0, 10) would have built I64 args).
    let fun_ty_for_hints = match &fun_ty {
        Type::Reference(inner) | Type::MutReference(inner)
            if matches!(inner.as_ref(), Type::Fun(..)) =>
        {
            inner.as_ref()
        }
        other => other,
    };
    let typed_args = if let Type::Fun(params, ..) = fun_ty_for_hints {
        if params.len() == typed_args.len()
            && typed_args
                .iter()
                .zip(params.iter())
                .any(|(a, p)| a.ty() != p)
        {
            args.iter()
                .zip(params.iter())
                .map(|(a, p)| construct_expr(a, Some(p), ctx))
                .collect::<Result<_, _>>()?
        } else {
            typed_args
        }
    } else {
        typed_args
    };

    // RFC-0008 §6: coerce each argument to `dyn Aspect` where its param
    // declares one. Argument-passing doesn't go through `maybe_read_copy`/
    // `maybe_singleton_coerce`/`maybe_dyn_coerce`'s usual let/return/tail call
    // sites at all — it's enforced by the plain `Type` equality check just
    // below instead, so this is the one place that needs its own explicit
    // coercion pass. A no-op for every param that isn't `Type::Dyn` (or
    // already matches).
    let typed_args = if let Type::Fun(params, ..) = fun_ty_for_hints {
        typed_args
            .into_iter()
            .zip(params.iter())
            .map(|(arg, p)| {
                let arg_span = arg.span().clone();
                maybe_dyn_coerce(p, arg, &arg_span, ctx)
            })
            .collect::<Result<Vec<_>, _>>()?
    } else {
        typed_args
    };

    // #775: turbofish pins each quantified var directly from the explicit
    // `::<T>` types, bypassing the unification against actual argument types
    // that an inferred call gets for free inside instantiate_scheme_for_call.
    // Nothing downstream checked the arguments actually agree with those
    // pinned types, so a real mismatch (`identity::<i64>("hello")`) was
    // silently accepted. The reconstruction-with-hints step above already
    // resolves the one legitimate case that can *look* like a mismatch here
    // — an unsuffixed integer literal defaulted before the turbofish type was
    // known (`clamp::<i32>(5, 0, 10)`) — so check for a real mismatch after
    // it runs, not before: `construct_expr` doesn't coerce a value to a hint
    // it structurally can't satisfy, so anything still disagreeing here is
    // genuine, not a literal that just needed the hint.
    if explicit_tys.is_some()
        && let Type::Fun(params, ..) = fun_ty_for_hints
        && params.len() == typed_args.len()
        && typed_args
            .iter()
            .zip(params.iter())
            .any(|(arg, param)| unify(&type_to_infer(arg.ty()), &type_to_infer(param)).is_err())
    {
        return Err(MetelError::type_error(
            TypeErrorCode::T0001,
            "argument type mismatch",
            span,
        ));
    }

    // Auto-deref: calling through a &Fun or &mut Fun is allowed.
    let fun_ty_inner = match &fun_ty {
        Type::Reference(inner) | Type::MutReference(inner)
            if matches!(inner.as_ref(), Type::Fun(..)) =>
        {
            inner.as_ref()
        }
        other => other,
    };
    match fun_ty_inner {
        Type::Fun(params, ret, _, _, call_mutation) => {
            if *call_mutation == crate::data::types::CallMutation::Mutating
                && is_through_shared_reference(&typed_callee)
            {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0029,
                    "cannot call a `var` closure through a shared reference",
                    span,
                ));
            }
            if params.len() != typed_args.len() {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0004,
                    format!(
                        "expected {} argument(s), got {}",
                        params.len(),
                        typed_args.len()
                    ),
                    span,
                ));
            }
            Ok(TypedExpr::Call {
                callee: Box::new(typed_callee),
                args: typed_args,
                ty: *ret.clone(),
                callee_id: ctx.resolved_callee_id(callee),
                span: span.clone(),
            })
        }
        _ => Err(MetelError::type_error(
            TypeErrorCode::T0001,
            "called a non-function value",
            span,
        )),
    }
}

/// Check that the concrete types instantiated for a function's generic type params
/// satisfy the aspect bounds declared on that function. Emits T0012 on the call span.
pub(super) fn check_fun_call_bounds(
    fun_name: &str,
    var_to_type: &HashMap<TypeVar, Type>,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<(), MetelError> {
    let bounds_map = registry.fun_bounds_for(fun_name);
    let record_kinds = registry.fun_record_kinds_for(fun_name);
    let projection_tail_constraints = registry.fun_projection_tail_constraints_for(fun_name);
    let open_row_params = registry.fun_open_row_params_for(fun_name);
    let generic_types_by_name: HashMap<String, Type> = HashMap::new();
    for (tv, concrete) in var_to_type {
        let bounds = bounds_map
            .and_then(|map| map.get(tv))
            .map_or(&[][..], Vec::as_slice);
        let record_kind = record_kinds
            .and_then(|map| map.get(tv))
            .copied()
            .unwrap_or(false);
        let is_open_row_param = open_row_params.is_some_and(|vars| vars.contains(tv));
        if let Some((expected_brand, row)) = projection_tail_constraints.and_then(|map| map.get(tv))
        {
            check_projection_tail_constraint(
                concrete,
                expected_brand,
                row,
                span,
                registry,
                current_module,
                &generic_types_by_name,
            )?;
            if is_open_row_param {
                check_width_subtyping(concrete, row, span, registry, current_module)?;
            }
        }
        if bounds.is_empty() && !record_kind {
            continue;
        }
        check_type_satisfies_bounds(
            concrete,
            bounds,
            record_kind,
            fun_name,
            span,
            registry,
            current_module,
            &generic_types_by_name,
        )?;
        if is_open_row_param {
            for bound in bounds {
                if let GenericBound::Row(row) = bound {
                    check_width_subtyping(concrete, row, span, registry, current_module)?;
                }
            }
        }
    }
    Ok(())
}

/// RFC-0121 §4, width subtyping, concrete case: an open-row-tailed parameter
/// (`{ x, ..R }` / `Handle.{ fd, ..R }`) takes its argument *by value*, so the
/// call narrows it to the named fields and silently forgets the rest. Sound
/// only when every forgotten field is `Copy` -- a non-`Copy` field would have
/// no owner left to drop it (or to discharge a linear field's use-once
/// obligation). Borrow position carries no such restriction, but an
/// open-row-tailed parameter's type is grammar-restricted to the top level of
/// a `fun_decl_param` (never under `&`), so only the by-value case is
/// reachable and this runs unconditionally for those parameters.
///
/// The abstract case -- the remainder is itself an unconstrained row inside a
/// generic body -- has no fields to walk and needs RFC-0123's `all R: Copy`
/// (metel-core#1302); an argument whose fields aren't structurally known is
/// skipped here, not rejected.
fn check_width_subtyping(
    concrete: &Type,
    row: &RowConstraint,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<(), MetelError> {
    let Some(record_fields) =
        structural_fields_for_row_check(concrete, registry, current_module, span)
    else {
        return Ok(());
    };
    for (label, ty) in &record_fields {
        if row.fields.iter().any(|required| &required.label == label) {
            continue;
        }
        let is_copy = matches!(
            ty,
            Type::Fun(_, _, _, crate::data::types::UseMultiplicity::Copy, _)
        ) || registry.type_satisfies_aspect(current_module, ty, "Copy");
        if !is_copy {
            return Err(MetelError::type_error(
                TypeErrorCode::T0033,
                format!(
                    "passing `{concrete}` by value to an open row parameter forgets field \
                     `{label}` of type `{ty}`, which is not `Copy` -- no owner would be left \
                     for it (RFC-0121 §4)"
                ),
                span,
            ));
        }
    }
    Ok(())
}

/// Try instantiating one candidate method scheme against the receiver's
/// concrete type args and constructing the call's arguments against it,
/// running the same bound/neg-bound/assoc-eq checks an ordinary single-scheme
/// resolution would. Returns `Err` if this particular candidate doesn't apply
/// (wrong arg count, bounds not satisfied, ...) -- the caller tries the next
/// candidate rather than surfacing this as the final error.
#[allow(clippy::too_many_arguments)]
pub(super) fn try_generic_method_scheme(
    scheme: &TypeScheme,
    struct_tvars: &[TypeVar],
    receiver_type_args: &[Type],
    explicit_method_tys: Option<&[Type]>,
    args: &[Expr],
    method: &str,
    span: &Span,
    ctx: &mut ConstructCtx,
) -> Result<(Type, Vec<TypedExpr>), MetelError> {
    let mut subst = Substitution::new();
    for (&tv, concrete) in struct_tvars.iter().zip(receiver_type_args.iter()) {
        subst.bind(tv, type_to_infer(concrete));
    }
    if let Some(explicit) = explicit_method_tys {
        let free: Vec<TypeVar> = {
            let mut fv: Vec<TypeVar> = type_engine::free_vars(&scheme.ty)
                .into_iter()
                .filter(|v| !struct_tvars.contains(v))
                .collect();
            fv.sort();
            fv
        };
        if explicit.len() != free.len() {
            return Err(MetelError::type_error(
                TypeErrorCode::T0004,
                format!(
                    "expected {} type argument(s), got {}",
                    free.len(),
                    explicit.len()
                ),
                span,
            ));
        }
        for (tv, concrete_ty) in free.iter().zip(explicit.iter()) {
            subst.bind(*tv, type_to_infer(concrete_ty));
        }
    }
    let partial_params: Vec<InferType> = match subst.apply(&scheme.ty) {
        InferType::Fun(p, ..) => p,
        _ => return Err(MetelError::internal("method scheme is not a function type")),
    };
    let typed_args: Vec<TypedExpr> = args
        .iter()
        .enumerate()
        .map(|(i, a)| {
            // params[0] is self; arguments line up with params[1..].
            let hint = partial_params
                .get(i + 1)
                .and_then(|it| infer_type_to_type(&subst.apply(it), span).ok());
            let typed = construct_expr(a, hint.as_ref(), ctx)?;
            reject_dynamic_array_where_sized_expected(hint.as_ref(), &typed)?;
            // RFC-0008 §6: coerce to `dyn Aspect` where the (now-substituted,
            // e.g. `List<dyn Shape>.push`'s `T` -> `dyn Shape`) param hint
            // calls for one. Slice 2 wired this into every other
            // expected-type site but missed generic method-call arguments —
            // this is that gap, metel-core#864.
            match &hint {
                Some(h) => maybe_dyn_coerce(h, typed, span, ctx),
                None => Ok(typed),
            }
        })
        .collect::<Result<_, _>>()?;
    for (param_it, arg) in partial_params.iter().skip(1).zip(typed_args.iter()) {
        let arg_it = type_to_infer(arg.ty());
        if let Ok(s) = type_engine::unify(&subst.apply(param_it), &arg_it) {
            subst = subst.compose(&s);
        }
    }
    // RFC-0121 §2: derive an impl's `Rest` from the receiver's `R`. This path
    // instantiates the scheme in place (no renaming), so the map is the identity.
    if !scheme.row_remainders.is_empty() {
        let identity: HashMap<TypeVar, TypeVar> =
            scheme.quantified_vars.iter().map(|&v| (v, v)).collect();
        backfill_row_remainders(
            scheme,
            &identity,
            &mut subst,
            span,
            ctx.registry,
            ctx.current_module,
        )?;
    }
    let mut var_to_type: HashMap<TypeVar, Type> = HashMap::new();
    for &tv in &scheme.quantified_vars {
        if let Ok(t) = infer_type_to_type(&subst.apply(&InferType::Var(tv)), span) {
            var_to_type.insert(tv, t);
        }
    }
    check_scheme_bounds(
        method,
        scheme,
        &var_to_type,
        span,
        ctx.registry,
        ctx.current_module,
    )?;
    check_scheme_neg_bounds(
        method,
        scheme,
        &var_to_type,
        span,
        ctx.registry,
        ctx.current_module,
    )?;
    check_scheme_assoc_eq(
        method,
        scheme,
        &var_to_type,
        span,
        ctx.registry,
        ctx.current_module,
    )?;
    let method_fun_ty = infer_type_to_type(&subst.apply(&scheme.ty), span)?;
    Ok((method_fun_ty, typed_args))
}

/// Resolve a method call against every candidate scheme registered for
/// `method` (issue #272: more than one exists when different aspects register
/// the same method name for the same/overlapping generic or structural
/// target -- coherence rejects that pair upfront unless their bounds are
/// provably disjoint, so at most one candidate's bounds can ever actually be
/// satisfied by a given concrete instantiation). Returns the first candidate
/// whose bounds the receiver's concrete type args satisfy, along with the
/// winning candidate's owning aspect name (if any); if none do, propagates the
/// last candidate's error (matching plain single-candidate behavior when
/// there's exactly one, the overwhelmingly common case).
///
/// The caller uses the returned aspect name to stamp the call site's
/// `MethodDispatch` with the specific aspect that was actually selected here,
/// rather than leaving it `Dynamic` -- a later, per-program (not per-call-
/// site) pass would otherwise have no way to reproduce this same bound-based
/// choice and could dispatch to the wrong candidate at runtime.
#[allow(clippy::too_many_arguments)]
pub(super) fn resolve_generic_method_call(
    candidates: &[(TypeScheme, Vec<TypeVar>, Option<String>)],
    receiver_type_args: &[Type],
    explicit_method_tys: Option<&[Type]>,
    args: &[Expr],
    method: &str,
    span: &Span,
    ctx: &mut ConstructCtx,
) -> Result<(Type, Vec<TypedExpr>, Option<String>, usize), MetelError> {
    let mut last_err = None;
    for (index, (scheme, struct_tvars, aspect_name)) in candidates.iter().enumerate() {
        match try_generic_method_scheme(
            scheme,
            struct_tvars,
            receiver_type_args,
            explicit_method_tys,
            args,
            method,
            span,
            ctx,
        ) {
            // The winner's index into `candidates`, so a caller can say *which* impl's
            // method it chose (metel-core#1322), not only which aspect it belongs to.
            Ok((ty, typed_args)) => return Ok((ty, typed_args, aspect_name.clone(), index)),
            Err(e) => last_err = Some(e),
        }
    }
    Err(last_err.expect("resolve_generic_method_call requires a non-empty candidate list"))
}

/// Resolve `aspect_name` to its stable `SymbolId`, the same lookup
/// `construct_impl_decl` uses for `TypedImplBlock::aspect_id`. `None` if no
/// resolver context is available (single-program path) or the name doesn't
/// resolve -- callers fall back to `MethodDispatch::Dynamic` in that case,
/// same as before this existed.
pub(super) fn resolve_aspect_id(ctx: &ConstructCtx, aspect_name: &str) -> Option<SymbolId> {
    let declaring_module = ctx
        .registry
        .aspect_declaring_module_in(ctx.current_module, aspect_name)?;
    ctx.symbols?
        .get(&(declaring_module.clone(), aspect_name.to_string()))
        .copied()
}

/// The `MethodDispatch` to stamp for a generic/structural method call once
/// `resolve_generic_method_call` has already picked the correct candidate
/// (issue #272): `Aspect { aspect_id }` when the winner belongs to a resolvable
/// aspect, so the evaluator dispatches to that exact aspect impl rather than
/// re-deriving (and potentially mis-deriving) the choice itself; `Dynamic`
/// otherwise, unchanged from prior behavior.
pub(super) fn dispatch_for_resolved_method(
    ctx: &ConstructCtx,
    aspect_name: Option<&str>,
) -> MethodDispatch {
    aspect_name
        .and_then(|name| resolve_aspect_id(ctx, name))
        .map_or(MethodDispatch::Dynamic, |aspect_id| {
            MethodDispatch::Aspect { aspect_id }
        })
}

/// Enforce the aspect bounds carried ON a scheme (`TypeScheme::bounds`,
/// positional per quantified var). This is how bounds on prelude/imported
/// schemes are checked — the TypeVar-keyed `fun_bounds` registry above only
/// matches schemes from the defining module.
pub(super) fn check_scheme_bounds(
    fun_name: &str,
    scheme: &TypeScheme,
    var_to_type: &HashMap<TypeVar, Type>,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<(), MetelError> {
    let generic_types_by_name: HashMap<String, Type> = scheme
        .quantified_vars
        .iter()
        .zip(&scheme.param_names)
        .filter_map(|(tv, name)| var_to_type.get(tv).cloned().map(|ty| (name.clone(), ty)))
        .collect();
    for (index, tv) in scheme.quantified_vars.iter().enumerate() {
        let bounds = scheme.bounds.get(index).map_or(&[][..], Vec::as_slice);
        let record_kind = scheme.record_kinds.get(index).copied().unwrap_or(false);
        if bounds.is_empty() && !record_kind {
            continue;
        }
        let Some(concrete) = var_to_type.get(tv) else {
            continue;
        };
        check_type_satisfies_bounds(
            concrete,
            bounds,
            record_kind,
            fun_name,
            span,
            registry,
            current_module,
            &generic_types_by_name,
        )?;
        if scheme.open_row_params.get(index).copied().unwrap_or(false) {
            for bound in bounds {
                if let GenericBound::Row(row) = bound {
                    check_width_subtyping(concrete, row, span, registry, current_module)?;
                }
            }
        }
    }
    Ok(())
}

/// RFC-0082 §4: enforce associated-type equality constraints from `fun_bounds`.
pub(super) fn check_fun_call_assoc_eq(
    fun_name: &str,
    var_to_type: &HashMap<TypeVar, Type>,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<(), MetelError> {
    let Some(eq_map) = registry.fun_assoc_eq_constraints_for(fun_name) else {
        return Ok(());
    };
    for (tv, constraints) in eq_map {
        let Some(concrete) = var_to_type.get(tv) else {
            continue;
        };
        for (aspect, assoc, expected_infer) in constraints {
            let Some(actual_ty) =
                registry.impl_assoc_type(current_module, &concrete.to_string(), aspect, assoc)
            else {
                continue;
            };
            // Substitute the expected type through var_to_type.
            let expected_subst = match expected_infer {
                InferType::Var(v) => {
                    if let Some(t) = var_to_type.get(v) {
                        type_to_infer(t)
                    } else {
                        continue; // still free — skip comparison
                    }
                }
                other => other.clone(),
            };
            let expected_ty = match expected_subst {
                InferType::Concrete(t) => t,
                InferType::Named(n, ..) => {
                    Type::Named(n, vec![], crate::data::types::NominalId::NONE)
                }
                _ => continue,
            };
            if *actual_ty != expected_ty {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0012,
                    format!(
                        "associated type equality constraint violated: `{aspect}::{assoc}` \
                         is `{actual_ty}` but expected `{expected_ty}`"
                    ),
                    span,
                ));
            }
        }
    }
    Ok(())
}

/// RFC-0082 §4: enforce associated-type equality constraints from a scheme's
/// `assoc_eq_constraints` field.
pub(super) fn check_scheme_assoc_eq(
    _fun_name: &str,
    scheme: &TypeScheme,
    var_to_type: &HashMap<TypeVar, Type>,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<(), MetelError> {
    if scheme.assoc_eq_constraints.is_empty() {
        return Ok(());
    }
    for (tv, constraints) in scheme
        .quantified_vars
        .iter()
        .zip(&scheme.assoc_eq_constraints)
    {
        if constraints.is_empty() {
            continue;
        }
        let Some(concrete) = var_to_type.get(tv) else {
            continue;
        };
        for (aspect, assoc, expected_infer) in constraints {
            let Some(actual_ty) =
                registry.impl_assoc_type(current_module, &concrete.to_string(), aspect, assoc)
            else {
                continue;
            };
            let expected_subst = match expected_infer {
                InferType::Var(v) => {
                    if let Some(t) = var_to_type.get(v) {
                        type_to_infer(t)
                    } else {
                        continue;
                    }
                }
                other => other.clone(),
            };
            let expected_ty = match expected_subst {
                InferType::Concrete(t) => t,
                InferType::Named(n, ..) => {
                    Type::Named(n, vec![], crate::data::types::NominalId::NONE)
                }
                _ => continue,
            };
            if *actual_ty != expected_ty {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0012,
                    format!(
                        "associated type equality constraint violated: `{aspect}::{assoc}` \
                         is `{actual_ty}` but expected `{expected_ty}`"
                    ),
                    span,
                ));
            }
        }
    }
    Ok(())
}

pub(super) fn resolve_row_field_type(
    ty: &TypeExpr,
    generic_types_by_name: &HashMap<String, Type>,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<Type, MetelError> {
    let mut generic_map = HashMap::new();
    let mut subst = Substitution::new();
    for (index, (name, concrete)) in generic_types_by_name.iter().enumerate() {
        let tv = TypeVar(index.try_into().expect("generic map index fits in u32"));
        generic_map.insert(name.clone(), tv);
        subst.bind(tv, type_to_infer(concrete));
    }
    let assoc_ctx = AssocResolveCtx {
        registry,
        current_module,
        current_aspect: None,
    };
    let inferred = type_expr_to_infer_with_assoc_ctx(ty, &generic_map, None, &assoc_ctx);
    infer_type_to_type(&subst.apply(&inferred), span)
}

pub(super) fn row_bound_error_prefix(bound: &GenericBound) -> String {
    match bound {
        GenericBound::Row(_) => format!("row bound `{bound}`"),
        GenericBound::Aspect(name) => format!("bound `{name}`"),
        GenericBound::AllFields { aspects, .. } => {
            format!("field-wise bound `all: {}`", aspects.join(" + "))
        }
    }
}

/// The structural field list a row bound checks against, for any value that
/// carries one -- an anonymous record (`Type::Record`, fields already
/// concrete), a narrowed struct/record residual (`Type::Residual`, fields
/// already concrete, RFC-0137), or a whole named record (`Type::Named`,
/// fields resolved from the registry's declared field templates with the
/// type's own generic arguments substituted in, the same way
/// `try_generic_method_scheme` resolves a generic receiver's method scheme
/// above). `None` for any other shape; callers only reach this after
/// `check_record_kind_requirement` has already rejected anything ineligible,
/// so `None` here just means "no row bound to check," never "unsoundly
/// skipped."
fn structural_fields_for_row_check(
    concrete: &Type,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
    span: &Span,
) -> Option<Vec<(String, Type)>> {
    match concrete {
        Type::Record(fields) | Type::Residual { fields, .. } => Some(fields.clone()),
        Type::Named(name, args, ..) => {
            let (id, _, _) = registry.projection_struct_fields(current_module, name)?;
            // `struct_type_params_by_id` has no entry at all for a non-generic
            // struct/record (never registered, not registered-as-empty) --
            // that's zero type params, not a resolution failure.
            let type_params: &[TypeVar] = registry
                .struct_type_params_by_id(id)
                .map_or(&[][..], Vec::as_slice);
            let field_templates = registry.struct_fields_by_id(id)?;
            let mut subst = Substitution::new();
            for (&tv, concrete_arg) in type_params.iter().zip(args.iter()) {
                subst.bind(tv, type_to_infer(concrete_arg));
            }
            let mut fields: Vec<(String, Type)> = field_templates
                .iter()
                .filter_map(|f| {
                    infer_type_to_type(&subst.apply(&f.ty), span)
                        .ok()
                        .map(|ty| (f.name.clone(), ty))
                })
                .collect();
            fields.sort_by(|a, b| a.0.cmp(&b.0));
            Some(fields)
        }
        _ => None,
    }
}

pub(super) fn check_record_kind_requirement(
    concrete: &Type,
    bounds: &[GenericBound],
    record_kind: bool,
    fun_name: &str,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<(), MetelError> {
    let has_row_bound = bounds
        .iter()
        .any(|bound| matches!(bound, GenericBound::Row(_)));
    if has_row_bound && !record_kind {
        return Err(MetelError::type_error(
            TypeErrorCode::T0012,
            format!(
                "row bound requires a record-kinded type parameter in `{fun_name}`; add `record` before the type parameter"
            ),
            span,
        ));
    }
    if !record_kind {
        return Ok(());
    }
    // RFC-0120 §3's eligibility rule (restated from RFC-0137 §3): visibility to
    // structural matching is scoped to the brand, fixed at declaration and
    // inherited unchanged by every narrowing -- a `Residual`'s own row content
    // is irrelevant to whether it is eligible, only its brand's declared kind
    // is. So `Named` and `Residual` are checked identically, by brand name.
    let brand = match concrete {
        Type::Record(_) => return Ok(()),
        Type::Named(name, ..) | Type::Residual { brand: name, .. } => name.as_str(),
        other => {
            return Err(MetelError::type_error(
                TypeErrorCode::T0012,
                format!(
                    "`{other}` is not a record, and only records satisfy a `record` type parameter"
                ),
                span,
            ));
        }
    };
    let kind = match concrete {
        Type::Named(_, _, nominal_id) => nominal_id
            .get()
            .and_then(|id| registry.visible_type_kind_by_id(id))
            .or_else(|| registry.visible_type_kind(current_module, brand)),
        _ => registry.visible_type_kind(current_module, brand),
    };
    match kind {
        Some(crate::pipeline::type_checking::type_engine::VisibleTypeKind::Record) => Ok(()),
        Some(crate::pipeline::type_checking::type_engine::VisibleTypeKind::Struct) => {
            Err(MetelError::type_error(
                TypeErrorCode::T0012,
                format!(
                    "`{brand}` is a struct, but a struct never satisfies a row bound; declare it as a `record` instead"
                ),
                span,
            ))
        }
        _ => Err(MetelError::type_error(
            TypeErrorCode::T0012,
            format!(
                "`{brand}` is not a record, and only records satisfy a `record` type parameter"
            ),
            span,
        )),
    }
}

pub(super) fn check_positive_row_bound(
    record_fields: &[(String, Type)],
    row: &RowConstraint,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
    generic_types_by_name: &HashMap<String, Type>,
) -> Result<(), MetelError> {
    let bound = GenericBound::Row(row.clone());
    let actual_labels: Vec<&str> = record_fields
        .iter()
        .map(|(label, _)| label.as_str())
        .collect();
    if !row.open && record_fields.len() != row.fields.len() {
        return Err(MetelError::type_error(
            TypeErrorCode::T0012,
            format!(
                "{} requires exactly these labels, but the record has: {}",
                row_bound_error_prefix(&bound),
                actual_labels.join(", ")
            ),
            span,
        ));
    }
    for required in &row.fields {
        let Ok(index) = record_fields
            .binary_search_by(|(label, _)| label.as_str().cmp(required.label.as_str()))
        else {
            return Err(MetelError::type_error(
                TypeErrorCode::T0012,
                format!(
                    "{} requires label `{}`, but the record has: {}",
                    row_bound_error_prefix(&bound),
                    required.label,
                    actual_labels.join(", ")
                ),
                span,
            ));
        };
        if let Some(expected_ty_expr) = &required.ty {
            let expected_ty = resolve_row_field_type(
                expected_ty_expr,
                generic_types_by_name,
                span,
                registry,
                current_module,
            )?;
            let actual_ty = &record_fields[index].1;
            if actual_ty != &expected_ty {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0012,
                    format!(
                        "{} requires label `{}` to have type `{expected_ty}`, but it is `{actual_ty}`",
                        row_bound_error_prefix(&bound),
                        required.label
                    ),
                    span,
                ));
            }
        }
    }
    Ok(())
}

/// RFC-0121 installment 2: `Handle.{ fd, ..R }` as a `fun_decl` parameter's
/// type. Unlike a row bound (RFC-0118/0120, `record`-kind only), this is
/// RFC-0117/0137's existing residual-projection/narrowing mechanism with an
/// open tail: it accepts a plain `struct`'s residual too, as long as the
/// concrete argument's own brand matches the one named in the projection
/// (`Handle`) and its *current* row has at least the named fields.
pub(super) fn check_projection_tail_constraint(
    concrete: &Type,
    expected_brand: &str,
    row: &RowConstraint,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
    generic_types_by_name: &HashMap<String, Type>,
) -> Result<(), MetelError> {
    let actual_brand = match concrete {
        Type::Named(name, ..) => name.as_str(),
        Type::Residual { brand, .. } => brand.as_str(),
        other => {
            return Err(MetelError::type_error(
                TypeErrorCode::T0001,
                format!("expected `{expected_brand}` (or a residual of it), found `{other}`"),
                span,
            ));
        }
    };
    if actual_brand != expected_brand {
        return Err(MetelError::type_error(
            TypeErrorCode::T0001,
            format!("expected `{expected_brand}` (or a residual of it), found `{actual_brand}`"),
            span,
        ));
    }
    let Some(fields) = structural_fields_for_row_check(concrete, registry, current_module, span)
    else {
        return Err(MetelError::type_error(
            TypeErrorCode::T0001,
            format!("cannot resolve `{expected_brand}`'s current fields"),
            span,
        ));
    };
    check_positive_row_bound(
        &fields,
        row,
        span,
        registry,
        current_module,
        generic_types_by_name,
    )
}

pub(super) fn check_negative_row_bound(
    record_fields: &[(String, Type)],
    row: &RowConstraint,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
    generic_types_by_name: &HashMap<String, Type>,
) -> Result<(), MetelError> {
    let bound = GenericBound::Row(row.clone());
    for forbidden in &row.fields {
        let Ok(index) = record_fields
            .binary_search_by(|(label, _)| label.as_str().cmp(forbidden.label.as_str()))
        else {
            continue;
        };
        let actual_ty = &record_fields[index].1;
        let matches = if let Some(expected_ty_expr) = &forbidden.ty {
            let expected_ty = resolve_row_field_type(
                expected_ty_expr,
                generic_types_by_name,
                span,
                registry,
                current_module,
            )?;
            actual_ty == &expected_ty
        } else {
            true
        };
        if matches {
            return Err(MetelError::type_error(
                TypeErrorCode::T0012,
                format!(
                    "negative row bound `!{}` is not satisfied because the record has label `{}`",
                    bound, forbidden.label
                ),
                span,
            ));
        }
    }
    Ok(())
}

/// RFC-0123 `where all R: Aspect`, concrete case: every field of the argument
/// outside `except` (the labels the parameter already names) must satisfy each
/// aspect. Vacuous on an empty remainder.
fn check_all_fields(
    record_fields: &[(String, Type)],
    aspects: &[String],
    except: &[String],
    fun_name: &str,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<(), MetelError> {
    for (label, ty) in record_fields
        .iter()
        .filter(|(label, _)| !except.contains(label))
    {
        for aspect in aspects {
            let holds = (aspect == "Copy"
                && matches!(
                    ty,
                    Type::Fun(_, _, _, crate::data::types::UseMultiplicity::Copy, _)
                ))
                || registry.type_satisfies_aspect(current_module, ty, aspect);
            if !holds {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0012,
                    format!(
                        "field `{label}` of type `{ty}` does not implement `{aspect}` \
                         (required of every field by `where all .. : {aspect}` on `{fun_name}`)"
                    ),
                    span,
                ));
            }
        }
    }
    Ok(())
}

/// Check one concrete type against a set of required bounds. Aspect bounds are
/// checked against the impl registry; row bounds are handled structurally.
#[allow(clippy::too_many_arguments)] // threads registry + module + generic map through bound checking
#[allow(clippy::too_many_lines)] // structural/reference Copy diagnostics extend the central bound checker
pub(super) fn check_type_satisfies_bounds(
    concrete: &Type,
    bounds: &[GenericBound],
    record_kind: bool,
    fun_name: &str,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
    generic_types_by_name: &HashMap<String, Type>,
) -> Result<(), MetelError> {
    check_record_kind_requirement(
        concrete,
        bounds,
        record_kind,
        fun_name,
        span,
        registry,
        current_module,
    )?;
    if let Some(record_fields) =
        structural_fields_for_row_check(concrete, registry, current_module, span)
    {
        for bound in bounds {
            match bound {
                GenericBound::Row(row) => check_positive_row_bound(
                    &record_fields,
                    row,
                    span,
                    registry,
                    current_module,
                    generic_types_by_name,
                )?,
                GenericBound::AllFields { aspects, except } => check_all_fields(
                    &record_fields,
                    aspects,
                    except,
                    fun_name,
                    span,
                    registry,
                    current_module,
                )?,
                GenericBound::Aspect(_) => {}
            }
        }
    }

    let type_name = match concrete {
        Type::Named(n, ..) => n.clone(),
        Type::Array(elem) => {
            for aspect in bounds.iter().filter_map(GenericBound::aspect_name) {
                if !registry.type_satisfies_aspect(current_module, concrete, aspect) {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0012,
                        format!(
                            "`{concrete}` does not implement `{aspect}` (required by `{fun_name}`)\n       hint: arrays implement `{aspect}` only when their element type `{elem}` does"
                        ),
                        span,
                    ));
                }
            }
            return Ok(());
        }
        Type::SizedArray(elem, _) => {
            for aspect in bounds.iter().filter_map(GenericBound::aspect_name) {
                if !registry.type_satisfies_aspect(current_module, concrete, aspect) {
                    let message = if aspect == "Copy" {
                        format!(
                            "`{concrete}` does not implement `{aspect}` (required by `{fun_name}`)\n       hint: fixed-size arrays implement `{aspect}` only when their element type `{elem}` does"
                        )
                    } else {
                        format!(
                            "`{concrete}` does not implement `{aspect}` (required by `{fun_name}`)"
                        )
                    };
                    return Err(MetelError::type_error(TypeErrorCode::T0012, message, span));
                }
            }
            return Ok(());
        }
        Type::Tuple(_) => {
            for aspect in bounds.iter().filter_map(GenericBound::aspect_name) {
                if !registry.type_satisfies_aspect(current_module, concrete, aspect) {
                    let message = if aspect == "Copy" {
                        format!(
                            "`{concrete}` does not implement `{aspect}` (required by `{fun_name}`)\n       hint: tuples implement `{aspect}` only when every element does"
                        )
                    } else {
                        format!(
                            "`{concrete}` does not implement `{aspect}` (required by `{fun_name}`)\n       hint: tuple impls are not yet provided; use a named struct instead"
                        )
                    };
                    return Err(MetelError::type_error(TypeErrorCode::T0012, message, span));
                }
            }
            return Ok(());
        }
        Type::Reference(_) | Type::MutReference(_) | Type::Fun(..) => {
            for aspect in bounds.iter().filter_map(GenericBound::aspect_name) {
                if !registry.type_satisfies_aspect(current_module, concrete, aspect) {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0012,
                        format!(
                            "`{concrete}` does not implement `{aspect}` (required by `{fun_name}`)"
                        ),
                        span,
                    ));
                }
            }
            return Ok(());
        }
        Type::Record(_) => {
            for aspect in bounds.iter().filter_map(GenericBound::aspect_name) {
                if !registry.type_satisfies_aspect(current_module, concrete, aspect) {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0012,
                        format!(
                            "`{concrete}` does not implement `{aspect}` (required by `{fun_name}`)\n       hint: an anonymous record satisfies the auto-derived aspects field-wise, and an aspect only through an `extend` on a record target whose row it has (`extend<row R: {{ .. }}> {{ ..R }}: {aspect}`); otherwise declare a `struct` and implement `{aspect}` there"
                        ),
                        span,
                    ));
                }
            }
            return Ok(());
        }
        other => match super::super::inference::primitive_type_name(other) {
            Some(n) => n,
            None => return Ok(()),
        },
    };
    for aspect in bounds.iter().filter_map(GenericBound::aspect_name) {
        if !registry.type_satisfies_aspect(current_module, concrete, aspect) {
            return Err(MetelError::type_error(
                TypeErrorCode::T0012,
                format!("`{type_name}` does not implement `{aspect}` (required by `{fun_name}`)"),
                span,
            ));
        }
    }
    Ok(())
}

/// Check that a concrete type does NOT satisfy a set of negative bounds.
#[allow(clippy::too_many_arguments)] // mirrors check_type_satisfies_bounds' parameter list
pub(super) fn check_type_does_not_satisfy_bound(
    concrete: &Type,
    neg_bounds: &[GenericBound],
    record_kind: bool,
    fun_name: &str,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
    generic_types_by_name: &HashMap<String, Type>,
) -> Result<(), MetelError> {
    check_record_kind_requirement(
        concrete,
        neg_bounds,
        record_kind,
        fun_name,
        span,
        registry,
        current_module,
    )?;
    if let Some(record_fields) =
        structural_fields_for_row_check(concrete, registry, current_module, span)
    {
        for bound in neg_bounds {
            if let GenericBound::Row(row) = bound {
                check_negative_row_bound(
                    &record_fields,
                    row,
                    span,
                    registry,
                    current_module,
                    generic_types_by_name,
                )?;
            }
        }
    }

    // Unlike `check_type_satisfies_bounds` above, this doesn't need a per-shape
    // hint message (the negative-bound loop below never had one, even for
    // `Type::Named`) — only a display string, so every structural shape can
    // share one arm via `Type`'s own `Display` impl. Without these arms, any
    // `concrete` that isn't `Type::Named` or a recognized primitive — every
    // tuple, array, record, reference, and function type — fell through to
    // `None => return Ok(())` below and skipped the aspect check entirely
    // (#632). Observable today for tuples, fixed-size arrays, and shared
    // references, which really are `Copy` — a `T: !Copy` bound silently
    // accepted them. Records and function types aren't classified `Copy` by
    // `type_satisfies_aspect` either way (confirmed: the positive `T: Copy`
    // path already rejects both), so this closes the same hole for whichever
    // aspect they do end up satisfying, without changing today's behavior for
    // either shape.
    let type_name = match concrete {
        Type::Named(n, ..) => n.clone(),
        Type::Array(_)
        | Type::SizedArray(_, _)
        | Type::Tuple(_)
        | Type::Reference(_)
        | Type::MutReference(_)
        | Type::Fun(..)
        | Type::Record(_) => concrete.to_string(),
        other => match super::super::inference::primitive_type_name(other) {
            Some(n) => n,
            None => return Ok(()),
        },
    };
    for aspect in neg_bounds.iter().filter_map(GenericBound::aspect_name) {
        if registry.type_satisfies_aspect(current_module, concrete, aspect) {
            if aspect == "Drop" && registry.type_satisfies_aspect(current_module, concrete, "Copy")
            {
                continue;
            }
            return Err(MetelError::type_error(
                TypeErrorCode::T0012,
                format!(
                    "`{type_name}` implements `{aspect}`; `!{aspect}` bound not satisfied (required by `{fun_name}`)"
                ),
                span,
            ));
        }
    }
    Ok(())
}

/// Check negative bounds via the TypeVar-keyed registry (module-local, same
/// lifetime as `fun_bounds`).
pub(super) fn check_fun_call_neg_bounds(
    fun_name: &str,
    var_to_type: &HashMap<TypeVar, Type>,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<(), MetelError> {
    let bounds_map = registry.neg_fun_bounds_for(fun_name);
    let record_kinds = registry.fun_record_kinds_for(fun_name);
    let generic_types_by_name: HashMap<String, Type> = HashMap::new();
    for (tv, concrete) in var_to_type {
        let bounds = bounds_map
            .and_then(|map| map.get(tv))
            .map_or(&[][..], Vec::as_slice);
        let record_kind = record_kinds
            .and_then(|map| map.get(tv))
            .copied()
            .unwrap_or(false);
        if bounds.is_empty() && !record_kind {
            continue;
        }
        check_type_does_not_satisfy_bound(
            concrete,
            bounds,
            record_kind,
            fun_name,
            span,
            registry,
            current_module,
            &generic_types_by_name,
        )?;
    }
    Ok(())
}

/// Check negative bounds carried ON a scheme (`TypeScheme::neg_bounds`,
/// positional per quantified var). Handles imported/prelude schemes whose
/// TypeVar-keyed `neg_fun_bounds` registry entry may not exist locally.
pub(super) fn check_scheme_neg_bounds(
    fun_name: &str,
    scheme: &TypeScheme,
    var_to_type: &HashMap<TypeVar, Type>,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<(), MetelError> {
    let generic_types_by_name: HashMap<String, Type> = scheme
        .quantified_vars
        .iter()
        .zip(&scheme.param_names)
        .filter_map(|(tv, name)| var_to_type.get(tv).cloned().map(|ty| (name.clone(), ty)))
        .collect();
    for (index, tv) in scheme.quantified_vars.iter().enumerate() {
        let bounds = scheme.neg_bounds.get(index).map_or(&[][..], Vec::as_slice);
        let record_kind = scheme.record_kinds.get(index).copied().unwrap_or(false);
        if bounds.is_empty() && !record_kind {
            continue;
        }
        let Some(concrete) = var_to_type.get(tv) else {
            continue;
        };
        check_type_does_not_satisfy_bound(
            concrete,
            bounds,
            record_kind,
            fun_name,
            span,
            registry,
            current_module,
            &generic_types_by_name,
        )?;
    }
    Ok(())
}

pub(super) fn instantiate_scheme_for_call(
    scheme: &TypeScheme,
    arg_types: &[&Type],
    span: &Span,
    type_var_gen: &mut TypeVarGenerator,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<(Type, HashMap<TypeVar, Type>), MetelError> {
    let (instance, renaming) = type_engine::instantiate_with_renaming(scheme, type_var_gen);

    let InferType::Fun(params, ret, call_mult, use_mult, call_mutation) = instance else {
        return Err(MetelError::internal("scheme type is not a function"));
    };

    let mut subst = Substitution::new();
    for (param, arg_ty) in params.iter().zip(arg_types.iter()) {
        let arg_infer = type_to_infer(arg_ty);
        let applied = subst.apply(param);
        // `unify` itself accepts a `dyn Aspect` paired with a concrete type as a
        // coercion (RFC-0008 §6) rather than failing -- whether `arg_ty` actually
        // implements the aspect is deferred to `maybe_dyn_coerce`, which runs
        // later against the constructed argument with full module-visibility
        // context and raises T0012 if it doesn't.
        let s = unify(&applied, &arg_infer).map_err(|_| {
            MetelError::type_error(TypeErrorCode::T0001, "argument type mismatch", span)
        })?;
        subst = subst.compose(&s);
    }

    // RFC-0082 backfill: for each projection in the scheme, resolve the base
    // type param to a concrete type and bind the projection's placeholder var
    // to the concrete associated type from the impl.
    for proj in scheme.assoc_projections.iter().flatten() {
        let (base_pos, aspect, assoc, placeholder_tv) = proj;
        let base_orig = scheme.quantified_vars[*base_pos];
        let fresh_base = renaming.get(&base_orig).copied().unwrap_or(base_orig);
        if let InferType::Named(base_name, ..) = subst.apply(&InferType::Var(fresh_base))
            && let Some(concrete_ty) =
                registry.impl_assoc_type(current_module, &base_name, aspect, assoc)
            && let Some(fresh_placeholder) = renaming.get(placeholder_tv)
        {
            subst.bind(*fresh_placeholder, InferType::Concrete(concrete_ty.clone()));
        }
    }

    // RFC-0121 §2 backfill: derive each decomposition equation's `Rest` from `R`.
    backfill_row_remainders(
        scheme,
        &renaming,
        &mut subst,
        span,
        registry,
        current_module,
    )?;
    // RFC-0037 backfill: for each opaque-return quantified var, bind its fresh
    // copy to the concrete type recorded at definition time. This lets the
    // `infer_type_to_type` calls below succeed using the known concrete type
    // rather than requiring ordinary substitution to have resolved it.
    for (i, opaque) in scheme.opaque_returns.iter().enumerate() {
        if let Some((_aspect, concrete_ty)) = opaque
            && let Some(&orig_tv) = scheme.quantified_vars.get(i)
            && let Some(&fresh_tv) = renaming.get(&orig_tv)
        {
            subst.bind(fresh_tv, InferType::Concrete(concrete_ty.clone()));
        }
    }

    let concrete_params: Vec<Type> = params
        .iter()
        .map(|p| infer_type_to_type(&subst.apply(p), span))
        .collect::<Result<_, _>>()?;
    let concrete_ret = infer_type_to_type(&subst.apply(&ret), span)?;

    // Build original-quantified-var → concrete-type mapping for bound checking.
    let mut var_to_concrete: HashMap<TypeVar, Type> = HashMap::new();
    for (orig_var, fresh_var) in &renaming {
        if let Ok(t) = infer_type_to_type(&subst.apply(&InferType::Var(*fresh_var)), span) {
            var_to_concrete.insert(*orig_var, t);
        }
    }

    Ok((
        Type::Fun(
            concrete_params,
            Box::new(concrete_ret),
            call_mult,
            use_mult,
            call_mutation,
        ),
        var_to_concrete,
    ))
}

/// RFC-0121 §2 (row decomposition): once a call has resolved `R` of a
/// `where R = { labels.., ..Rest }` equation to a closed record, `Rest` *is* that
/// record minus `labels`. Unifies the derived record with whatever `Rest` already
/// is -- unresolved (the usual case) simply binds it, while a conflicting
/// annotation (`let r: Session<{ other: i64 }> := authenticate(s)`) is rejected.
///
/// An `R` whose fields aren't structurally known here (still a type variable, or
/// not a record) leaves `Rest` alone, same as `check_width_subtyping`'s skip.
fn backfill_row_remainders(
    scheme: &TypeScheme,
    renaming: &HashMap<TypeVar, TypeVar>,
    subst: &mut Substitution,
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<(), MetelError> {
    for (i, remainder) in scheme.row_remainders.iter().enumerate() {
        let Some((r_pos, removed)) = remainder else {
            continue;
        };
        let (Some(&rest_orig), Some(&r_orig)) = (
            scheme.quantified_vars.get(i),
            scheme.quantified_vars.get(*r_pos),
        ) else {
            continue;
        };
        let (Some(&fresh_rest), Some(&fresh_r)) = (renaming.get(&rest_orig), renaming.get(&r_orig))
        else {
            continue;
        };
        let Ok(r_ty) = infer_type_to_type(&subst.apply(&InferType::Var(fresh_r)), span) else {
            continue;
        };
        let Some(fields) = structural_fields_for_row_check(&r_ty, registry, current_module, span)
        else {
            continue;
        };
        let mut remaining: Vec<(String, Type)> = fields
            .into_iter()
            .filter(|(label, _)| !removed.contains(label))
            .collect();
        remaining.sort_by(|a, b| a.0.cmp(&b.0));
        let derived = type_to_infer(&Type::Record(remaining));
        let s = type_engine::unify(&subst.apply(&InferType::Var(fresh_rest)), &derived).map_err(
            |_| {
                MetelError::type_error(
                    TypeErrorCode::T0001,
                    format!(
                        "row decomposition mismatch: `{r_ty}` minus {} does not match the \
                         expected remainder (RFC-0121 §2)",
                        removed
                            .iter()
                            .map(|l| format!("`{l}`"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    span,
                )
            },
        )?;
        *subst = subst.compose(&s);
    }
    Ok(())
}

pub(super) fn instantiate_scheme_with_turbofish(
    scheme: &TypeScheme,
    explicit_types: &[Type],
    span: &Span,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<(Type, HashMap<TypeVar, Type>), MetelError> {
    if explicit_types.len() != scheme.quantified_vars.len() {
        return Err(MetelError::type_error(
            TypeErrorCode::T0004,
            format!(
                "expected {} type argument(s), got {}",
                scheme.quantified_vars.len(),
                explicit_types.len()
            ),
            span,
        ));
    }
    let mut subst = Substitution::new();
    let mut var_to_concrete: HashMap<TypeVar, Type> = HashMap::new();
    for (&qvar, concrete_ty) in scheme.quantified_vars.iter().zip(explicit_types.iter()) {
        subst.bind(qvar, type_to_infer(concrete_ty));
        var_to_concrete.insert(qvar, concrete_ty.clone());
    }
    // RFC-0082 backfill: bind projection placeholder vars to their concrete associated types.
    for proj in scheme.assoc_projections.iter().flatten() {
        let (base_pos, aspect, assoc, placeholder_tv) = proj;
        if let Some(Type::Named(base_name, ..)) =
            var_to_concrete.get(&scheme.quantified_vars[*base_pos])
            && let Some(concrete_ty) =
                registry.impl_assoc_type(current_module, base_name, aspect, assoc)
        {
            subst.bind(*placeholder_tv, InferType::Concrete(concrete_ty.clone()));
        }
    }
    // RFC-0037 backfill: bind opaque-return vars to their concrete types.
    for (i, opaque) in scheme.opaque_returns.iter().enumerate() {
        if let Some((_aspect, concrete_ty)) = opaque
            && let Some(&orig_tv) = scheme.quantified_vars.get(i)
        {
            subst.bind(orig_tv, InferType::Concrete(concrete_ty.clone()));
        }
    }
    let instantiated = subst.apply(&scheme.ty);
    let concrete_ty = infer_type_to_type(&instantiated, span)?;
    Ok((concrete_ty, var_to_concrete))
}

/// Instantiate a scheme by unifying its return type with `expected_ret`.
/// Used for zero-arg generic constructors (e.g. `List::new()`) where T cannot
/// be inferred from arguments but is known from the enclosing let annotation.
pub(super) fn instantiate_scheme_with_expected_ret(
    scheme: &TypeScheme,
    arg_types: &[&Type],
    expected_ret: &Type,
    span: &Span,
    type_var_gen: &mut TypeVarGenerator,
    registry: &TypeDefinitionRegistry,
    current_module: &[String],
) -> Result<(Type, HashMap<TypeVar, Type>), MetelError> {
    let (instance, renaming) = type_engine::instantiate_with_renaming(scheme, type_var_gen);
    let InferType::Fun(params, ret, call_mult, use_mult, call_mutation) = instance else {
        return Err(MetelError::internal("scheme type is not a function"));
    };
    let mut subst = Substitution::new();
    for (param, arg_ty) in params.iter().zip(arg_types.iter()) {
        let applied = subst.apply(param);
        // `unify` accepts a `dyn Aspect`/concrete-type pairing as a coercion
        // (RFC-0008 §6) -- see the comment in `instantiate_scheme_for_call`.
        let s = type_engine::unify(&applied, &type_to_infer(arg_ty)).map_err(|_| {
            MetelError::type_error(TypeErrorCode::T0001, "argument type mismatch", span)
        })?;
        subst = subst.compose(&s);
    }
    let applied_ret = subst.apply(&ret);
    let s = type_engine::unify(&applied_ret, &type_to_infer(expected_ret)).map_err(|_| {
        MetelError::type_error(
            TypeErrorCode::T0001,
            "return type does not match annotation",
            span,
        )
    })?;
    subst = subst.compose(&s);
    // RFC-0082 backfill: bind projection placeholder vars to their concrete associated types.
    for proj in scheme.assoc_projections.iter().flatten() {
        let (base_pos, aspect, assoc, placeholder_tv) = proj;
        let base_orig = scheme.quantified_vars[*base_pos];
        let fresh_base = renaming.get(&base_orig).copied().unwrap_or(base_orig);
        if let InferType::Named(base_name, ..) = subst.apply(&InferType::Var(fresh_base))
            && let Some(concrete_ty) =
                registry.impl_assoc_type(current_module, &base_name, aspect, assoc)
            && let Some(fresh_placeholder) = renaming.get(placeholder_tv)
        {
            subst.bind(*fresh_placeholder, InferType::Concrete(concrete_ty.clone()));
        }
    }
    // RFC-0121 §2 backfill: derive each decomposition equation's `Rest` from `R`.
    backfill_row_remainders(
        scheme,
        &renaming,
        &mut subst,
        span,
        registry,
        current_module,
    )?;
    // RFC-0037 backfill: bind opaque-return vars to their concrete types.
    for (i, opaque) in scheme.opaque_returns.iter().enumerate() {
        if let Some((_aspect, concrete_ty)) = opaque
            && let Some(&orig_tv) = scheme.quantified_vars.get(i)
            && let Some(&fresh_tv) = renaming.get(&orig_tv)
        {
            subst.bind(fresh_tv, InferType::Concrete(concrete_ty.clone()));
        }
    }
    let concrete_params: Vec<Type> = params
        .iter()
        .map(|p| infer_type_to_type(&subst.apply(p), span))
        .collect::<Result<_, _>>()?;
    let concrete_ret = infer_type_to_type(&subst.apply(&ret), span)?;
    let mut var_to_concrete: HashMap<TypeVar, Type> = HashMap::new();
    for (orig_var, fresh_var) in &renaming {
        if let Ok(t) = infer_type_to_type(&subst.apply(&InferType::Var(*fresh_var)), span) {
            var_to_concrete.insert(*orig_var, t);
        }
    }
    Ok((
        Type::Fun(
            concrete_params,
            Box::new(concrete_ret),
            call_mult,
            use_mult,
            call_mutation,
        ),
        var_to_concrete,
    ))
}
