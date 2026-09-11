use super::{
    ann_to_infer, aspect_impl_method_signature_matches, build_assoc_projection_map,
    check_copy_impl_eligibility, closed_nominal_target, collect_fun_assoc_eq_constraints,
    collect_fun_type_var_bounds, collect_fun_type_var_record_kinds,
    collect_negative_fun_type_var_bounds, constrain_with_read_copy, dyn_array_elem_ann, free_vars,
    fun_generic_map, generalize, infer_block, infer_dyn_array_literal, infer_expr, infer_stmt,
    infer_type_to_type, native_fun_ty, primitive_type_from_name, type_expr_to_infer_with_assoc_ctx,
    type_expr_to_infer_with_ctx, type_expr_to_infer_with_generics,
    type_expr_to_infer_with_generics_and_self, type_expr_to_infer_with_self, type_to_infer,
    AspectMethod, AssocResolveCtx, Decl, Expr, FunDecl, FunGeneralization, GenericBound, HashMap,
    InferContext, InferType, MetelError, NativeFunTyResult, Polarity, Substitution, Type,
    TypeErrorCode, TypeExpr, TypeVar,
};

// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
pub(super) fn infer_decl(
    decl: &Decl,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<InferType, MetelError> {
    match decl {
        Decl::Let(ld) => {
            let env_fvs = ctx.env_free_vars();
            let val_ty = if let (Expr::Array(elems, arr_span), Some(elem_ann)) =
                (&ld.value, ld.type_ann.as_ref().and_then(dyn_array_elem_ann))
            {
                let elem_ty = ann_to_infer(elem_ann, ctx);
                infer_dyn_array_literal(elems, &elem_ty, arr_span, ctx, fun_generalizations)?
            } else {
                infer_expr(&ld.value, ctx, fun_generalizations)?
            };
            // RFC-0137 slice 2: a `let n := h.name;` initializer partially moves a
            // struct field, narrowing `h` for the rest of the block.
            ctx.note_consumed_infer(&ld.value);
            let bound_ty = if let Some(ann) = &ld.type_ann {
                let declared = ann_to_infer(ann, ctx);
                // RFC-0053 §4 (metel-core#757): `[T; N]` coerces to `T[]`,
                // never the reverse. `unify()` stays bidirectional for
                // Array/SizedArray -- it's shared by many symmetric/
                // structural unification call sites unrelated to
                // actual-vs-expected coercion checking, and an earlier
                // attempt that made it asymmetric there broke 5+ existing
                // fixtures (a match-pattern exhaustiveness case among them --
                // the array-literal bypass that attempt needed to add here,
                // to route around its own breaking change, itself broke a
                // *different* case by skipping `constrain_with_read_copy`
                // entirely for every array literal). So: check this one
                // direction explicitly and narrowly instead, skipped for a
                // literal (`[1, 2, 3]`) since a literal's Pass-1 type is
                // always `Array` regardless of context -- construction
                // validates a literal against its expected `[T; N]` shape
                // separately, and only a non-literal RHS (a plain identifier
                // already carrying a genuine `Array` type) is what this needs
                // to catch.
                if !matches!(&ld.value, Expr::Array(_, _)) {
                    if let (InferType::Array(_), InferType::SizedArray(_, n)) = (&val_ty, &declared)
                    {
                        return Err(MetelError::type_error(
                            crate::error::TypeErrorCode::T0001,
                            format!(
                                "expected a fixed-size array of {n} element(s), got a dynamically-sized array"
                            ),
                            &ld.span,
                        ));
                    }
                }
                constrain_with_read_copy(ctx, val_ty.clone(), declared, ld.span.clone())
            } else {
                val_ty.clone()
            };
            // metel-core#736 / RFC-0138: a bare reference to an already-declared
            // generic function (`let alias = identity;`) is, for this purpose, the
            // same shape as a closure literal -- `identity` was already auto-
            // instantiated with fresh vars by the `ctx.lookup` inside `infer_expr`
            // above, so re-generalizing that (still fully free, since nothing else
            // constrained it) below reconstructs a scheme equivalent to `identity`'s
            // own, under `alias`'s name.
            let is_generic_fn_ref = matches!(&ld.value, Expr::Ident(name, _)
                if ctx.poly_scheme(name).is_some_and(|s| !s.quantified_vars.is_empty()));
            // Let-polymorphism: generalize unannotated closure-valued let bindings
            // (and, per the above, bare references to an existing generic function).
            // If the resolved type still has free variables, they are quantified into a
            // polymorphic scheme so each call site gets a fresh instantiation.
            if (matches!(&ld.value, Expr::Closure { .. }) || is_generic_fn_ref)
                && ld.type_ann.is_none()
            {
                let solved = ctx.solve()?;
                let partial_subst = ctx.default_literal_vars(&solved);
                let resolved_ty = partial_subst.apply(&val_ty);
                let scheme = generalize(resolved_ty.clone(), &env_fvs);
                if !scheme.quantified_vars.is_empty() {
                    ctx.bind_poly(&ld.name, scheme);
                    fun_generalizations.push(FunGeneralization {
                        name: ld.name.clone(),
                        fun_ty: resolved_ty,
                        env_fvs,
                        name_map: HashMap::new(),
                        bounds: HashMap::new(),
                        neg_bounds: HashMap::new(),
                        record_kinds: HashMap::new(),
                        assoc_projections: HashMap::new(),
                        assoc_eq: HashMap::new(),
                        opaque_returns: HashMap::new(),
                    });
                    return Ok(InferType::unit());
                }
            }
            ctx.bind_mono(&ld.name, bound_ty, false);
            Ok(InferType::unit())
        }
        Decl::Mut(md) => {
            let val_ty = if let (Expr::Array(elems, arr_span), Some(elem_ann)) =
                (&md.value, md.type_ann.as_ref().and_then(dyn_array_elem_ann))
            {
                let elem_ty = ann_to_infer(elem_ann, ctx);
                infer_dyn_array_literal(elems, &elem_ty, arr_span, ctx, fun_generalizations)?
            } else {
                infer_expr(&md.value, ctx, fun_generalizations)?
            };
            ctx.note_consumed_infer(&md.value);
            let bound_ty = if let Some(ann) = &md.type_ann {
                let declared = ann_to_infer(ann, ctx);
                // RFC-0053 §4 (metel-core#757): see the matching check in
                // `Decl::Let` above for the full rationale.
                if !matches!(&md.value, Expr::Array(_, _)) {
                    if let (InferType::Array(_), InferType::SizedArray(_, n)) = (&val_ty, &declared)
                    {
                        return Err(MetelError::type_error(
                            crate::error::TypeErrorCode::T0001,
                            format!(
                                "expected a fixed-size array of {n} element(s), got a dynamically-sized array"
                            ),
                            &md.span,
                        ));
                    }
                }
                constrain_with_read_copy(ctx, val_ty, declared, md.span.clone())
            } else {
                val_ty
            };
            ctx.bind_mono(&md.name, bound_ty, true);
            Ok(InferType::unit())
        }
        Decl::Fun(fd) => {
            infer_fun_decl(fd, ctx, fun_generalizations)?;
            Ok(InferType::unit())
        }
        Decl::Struct(_) | Decl::Enum(_) | Decl::Aspect(_) => Ok(InferType::unit()),
        Decl::Impl(ib) => {
            if matches!(
                &ib.target_type,
                TypeExpr::Record(_) | TypeExpr::RecordProjection { .. }
            ) {
                if ib.aspect_name.is_none() {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0001,
                        "anonymous records cannot have inherent methods; declare a `struct` if you need methods",
                        &ib.span,
                    ));
                }
                if let Some(aspect_name) = &ib.aspect_name {
                    if aspect_name == "Drop" {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0001,
                            "anonymous records cannot implement `Drop`; teardown logic requires a nominal type",
                            &ib.span,
                        ));
                    }
                    if ctx
                        .registry()
                        .aspect_declaring_module(aspect_name)
                        .is_some_and(|module| module.as_slice() != ctx.current_module_path())
                    {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0014,
                            format!(
                                "`{aspect_name}` is not local to this module and cannot be implemented for an anonymous record; declare a `struct` and implement it there"
                            ),
                            &ib.span,
                        ));
                    }
                }
            }
            // Structural blanket impl targets (`T[]`) have no nominal head. As in
            // construction, keep a nominal target name only when one exists; generic
            // structural impl bodies are inferred against their own type-parameter map.
            crate::typechecker::reject_unregisterable_impl_target(ib)?;
            // Same classification as construction, but keyed on the *last*
            // segment — inference's registries are, and unifying the spelling
            // would change what they look up.
            let target_name = crate::typechecker::impl_target_head(&ib.target_type)
                .map(|name| name.rsplit("::").next().unwrap_or(name).to_string())
                .unwrap_or_default();
            if ib.polarity == Polarity::Positive {
                if let Some(aspect_name) = &ib.aspect_name {
                    if aspect_name == "Copy" {
                        check_copy_impl_eligibility(ib, &target_name, ctx)?;
                    } else if aspect_name == "Drop" {
                        if let Some(concrete_target) = closed_nominal_target(ib, &target_name) {
                            if ctx.registry().type_satisfies_aspect(
                                ctx.current_module_path(),
                                &concrete_target,
                                "Copy",
                            ) {
                                return Err(MetelError::type_error(
                                    TypeErrorCode::T0001,
                                    format!(
                                        "`{target_name}` cannot implement both `Copy` and `Drop`"
                                    ),
                                    &ib.span,
                                ));
                            }
                        }
                    }
                }
            }
            let mut inherited_defaults = vec![];
            // A negative impl (RFC-0081, issue #264) is a declaration of
            // non-implementation, not a real impl with missing overrides — it must
            // not be required to provide the aspect's methods, nor inherit its
            // default bodies. The parser already enforces `ib.methods.is_empty()`
            // for a negative impl; without this guard that empty method list would
            // otherwise look exactly like every required method being missing.
            if ib.polarity == Polarity::Positive {
                if let Some(aspect_name) = &ib.aspect_name {
                    if let Some(methods) = ctx.aspect_method_defs(aspect_name).cloned() {
                        let provided: std::collections::HashSet<&str> =
                            ib.methods.iter().map(|m| m.name.as_str()).collect();
                        let declared: std::collections::HashSet<&str> =
                            methods.iter().map(|m| m.name.as_str()).collect();
                        let provided_assoc: std::collections::HashSet<&str> =
                            ib.assoc_type_defs.iter().map(|d| d.name.as_str()).collect();
                        let missing_assoc_type = ctx
                            .registry()
                            .aspect_assoc_type_decls(aspect_name)
                            .is_some_and(|decls| {
                                decls
                                    .iter()
                                    .any(|decl| !provided_assoc.contains(decl.name.as_str()))
                            });
                        for method in &ib.methods {
                            let declared_method = methods
                                .iter()
                                .find(|declared_method| declared_method.name == method.name);
                            if !declared.contains(method.name.as_str()) {
                                return Err(MetelError::type_error(
                                    TypeErrorCode::T0001,
                                    format!(
                                        "`{}::{}` is not declared by aspect `{}`; put it in an inherent `extend {}` block instead",
                                        target_name, method.name, aspect_name, target_name
                                    ),
                                    &method.span,
                                ));
                            }
                            if !missing_assoc_type
                                && !declared_method.is_some_and(|declared_method| {
                                    aspect_impl_method_signature_matches(
                                        method,
                                        declared_method,
                                        ib,
                                        aspect_name,
                                        &target_name,
                                        ctx,
                                    )
                                })
                            {
                                return Err(MetelError::type_error(
                                    TypeErrorCode::T0012,
                                    format!(
                                        "`{}::{}` does not match the signature declared by aspect `{}`",
                                        target_name, method.name, aspect_name
                                    ),
                                    &method.span,
                                ));
                            }
                        }
                        for method in methods {
                            if provided.contains(method.name.as_str()) {
                                continue;
                            }
                            if method.default_body.is_none() {
                                return Err(MetelError::type_error(
                                    TypeErrorCode::T0012,
                                    format!(
                                        "`{}` does not implement `{}::{}` required by aspect `{}`",
                                        target_name, target_name, method.name, aspect_name
                                    ),
                                    &ib.span,
                                ));
                            }
                            inherited_defaults.push(method);
                        }
                    }
                    // RFC-0082 §2: check that the impl defines all associated types
                    // declared by the aspect. §1.1: if the declaration has a bound,
                    // the concrete binding must satisfy it.
                    // TODO(#241): generic impls are skipped above; assoc-type
                    // completeness for blanket impls is #241's job.
                    if let Some(assoc_decls) = ctx.aspect_assoc_type_decls(aspect_name).cloned() {
                        let provided_assoc: std::collections::HashMap<&str, &TypeExpr> = ib
                            .assoc_type_defs
                            .iter()
                            .map(|d| (d.name.as_str(), &d.ty))
                            .collect();
                        for decl in &assoc_decls {
                            if let Some(concrete_ty_expr) = provided_assoc.get(decl.name.as_str()) {
                                // §1.1: if the declaration has a bound, check the
                                // concrete binding satisfies it.
                                for bound in &decl.bounds {
                                    if let Some(bound_aspect) = bound.aspect_name() {
                                        if bound.polarity == Polarity::Positive {
                                            let concrete_infer = type_expr_to_infer_with_self(
                                                concrete_ty_expr,
                                                &target_name,
                                            );
                                            // Check that the concrete type satisfies the
                                            // bound aspect. For concrete target types the
                                            // concrete binding is also concrete, so we can
                                            // check via the registry's impl_aspect_env.
                                            let concrete_name = match &concrete_infer {
                                                InferType::Concrete(t) => Some(format!("{t}")),
                                                InferType::Named(n, _) => Some(n.clone()),
                                                _ => None,
                                            };
                                            if let Some(name) = concrete_name {
                                                // Check if this name matches one of the impl's own generic parameters
                                                if let Some(gp) =
                                                    ib.generics.iter().find(|p| p.name == name)
                                                {
                                                    // This is the impl's own generic parameter - check its declared bounds
                                                    let param_bounds = gp
                                                        .bounds
                                                        .iter()
                                                        .filter(|b| {
                                                            b.polarity == Polarity::Positive
                                                        })
                                                        .filter_map(|b| {
                                                            b.aspect_name().map(ToOwned::to_owned)
                                                        })
                                                        .collect::<Vec<_>>();

                                                    if param_bounds
                                                        .contains(&bound_aspect.to_string())
                                                    {
                                                        // The bound is satisfied by the impl's own parameter bounds
                                                        continue;
                                                    }
                                                    return Err(MetelError::type_error(
                                                        TypeErrorCode::T0012,
                                                        format!(
                                                            "associated type `{}` bound `{}` is not satisfied by `{}`",
                                                            decl.name, bound_aspect, name
                                                        ),
                                                        &ib.span,
                                                    ));
                                                }
                                                // Original behavior for concrete types
                                                if !ctx.registry().impl_aspect_env_has(
                                                    ctx.current_module_path(),
                                                    &name,
                                                    bound_aspect,
                                                ) {
                                                    return Err(MetelError::type_error(
                                                        TypeErrorCode::T0012,
                                                        format!(
                                                            "associated type `{}` bound `{}` is not satisfied by `{}`",
                                                            decl.name, bound_aspect, name
                                                        ),
                                                        &ib.span,
                                                    ));
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                // Missing associated type definition → T0017.
                                return Err(MetelError::type_error(
                                    TypeErrorCode::T0017,
                                    format!(
                                        "`{}` does not define associated type `{}` required by aspect `{}`",
                                        target_name, decl.name, aspect_name
                                    ),
                                    &ib.span,
                                ));
                            }
                        }
                    }
                }
            }
            for method in &ib.methods {
                infer_impl_method(method, ib, &target_name, ctx, fun_generalizations)?;
            }
            // `inherited_defaults` is only ever populated inside the `Some(aspect_name)`
            // branch above, so this is always `Some` when the loop body runs.
            if let Some(aspect_name) = ib.aspect_name.as_deref() {
                for method in &inherited_defaults {
                    infer_default_aspect_method(
                        method,
                        &target_name,
                        aspect_name,
                        ctx,
                        fun_generalizations,
                    )?;
                }
            }
            Ok(InferType::unit())
        }
        Decl::TypeAlias(_) => unreachable!("RFC-0160 type aliases are expanded before inference"),
        Decl::Stmt(stmt) => infer_stmt(stmt, ctx, fun_generalizations),
    }
}

/// Check whether a `TypeExpr` tree contains any `ImplAspect` nodes (RFC-0037).
/// Used to decide whether the return-type conversion needs opaque-return handling.
pub(super) fn type_expr_contains_impl_aspect(te: &TypeExpr) -> bool {
    match te {
        TypeExpr::ImplAspect { .. } => true,
        TypeExpr::Named(_, args) => args.iter().any(type_expr_contains_impl_aspect),
        TypeExpr::Tuple(elems) => elems.iter().any(type_expr_contains_impl_aspect),
        TypeExpr::Record(fields) => fields
            .iter()
            .any(|(_, ty)| type_expr_contains_impl_aspect(ty)),
        TypeExpr::Array(elem)
        | TypeExpr::SizedArray(elem, _)
        | TypeExpr::Reference(elem)
        | TypeExpr::MutReference(elem) => type_expr_contains_impl_aspect(elem),
        TypeExpr::Fun {
            params,
            return_type: ret,
            ..
        } => {
            params.iter().any(type_expr_contains_impl_aspect)
                || ret
                    .as_ref()
                    .is_some_and(|r| type_expr_contains_impl_aspect(r))
        }
        TypeExpr::DynAspect { bound, .. } => type_expr_contains_impl_aspect(bound),
        TypeExpr::Unit | TypeExpr::Projection { .. } | TypeExpr::RecordProjection { .. } => false,
    }
}

/// Recursively rewrite a `TypeExpr`, replacing each `ImplAspect { bound, .. }`
/// with `Named(placeholder_name, [])`. Returns the rewritten tree plus a list
/// of `(placeholder_name, aspect_name)` pairs, one per replaced node (RFC-0037).
pub(super) fn rewrite_impl_aspect_returns(
    te: &TypeExpr,
    counter: &mut usize,
    replacements: &mut Vec<(String, String)>,
) -> TypeExpr {
    match te {
        TypeExpr::ImplAspect { bound, .. } => {
            let aspect_name = match bound.as_ref() {
                TypeExpr::Named(name, _) => name.clone(),
                _ => String::new(),
            };
            let placeholder = format!("_OpaqueRet{counter}");
            *counter += 1;
            replacements.push((placeholder.clone(), aspect_name));
            TypeExpr::Named(placeholder, vec![])
        }
        TypeExpr::Named(name, args) => TypeExpr::Named(
            name.clone(),
            args.iter()
                .map(|a| rewrite_impl_aspect_returns(a, counter, replacements))
                .collect(),
        ),
        TypeExpr::Tuple(elems) => TypeExpr::Tuple(
            elems
                .iter()
                .map(|e| rewrite_impl_aspect_returns(e, counter, replacements))
                .collect(),
        ),
        TypeExpr::Record(fields) => TypeExpr::Record(
            fields
                .iter()
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        rewrite_impl_aspect_returns(ty, counter, replacements),
                    )
                })
                .collect(),
        ),
        TypeExpr::Array(elem) => TypeExpr::Array(Box::new(rewrite_impl_aspect_returns(
            elem,
            counter,
            replacements,
        ))),
        TypeExpr::SizedArray(elem, n) => TypeExpr::SizedArray(
            Box::new(rewrite_impl_aspect_returns(elem, counter, replacements)),
            *n,
        ),
        TypeExpr::Reference(elem) => TypeExpr::Reference(Box::new(rewrite_impl_aspect_returns(
            elem,
            counter,
            replacements,
        ))),
        TypeExpr::MutReference(elem) => TypeExpr::MutReference(Box::new(
            rewrite_impl_aspect_returns(elem, counter, replacements),
        )),
        TypeExpr::Fun {
            params,
            return_type: ret,
            call_multiplicity,
            call_mutation,
        } => TypeExpr::Fun {
            params: params
                .iter()
                .map(|p| rewrite_impl_aspect_returns(p, counter, replacements))
                .collect(),
            return_type: ret
                .as_ref()
                .map(|r| Box::new(rewrite_impl_aspect_returns(r, counter, replacements))),
            call_multiplicity: *call_multiplicity,
            call_mutation: *call_mutation,
        },
        TypeExpr::DynAspect { bound, span } => TypeExpr::DynAspect {
            bound: Box::new(rewrite_impl_aspect_returns(bound, counter, replacements)),
            span: span.clone(),
        },
        TypeExpr::Unit | TypeExpr::Projection { .. } | TypeExpr::RecordProjection { .. } => {
            te.clone()
        }
    }
}

// Exhaustive match over every AST/type-system variant; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
pub(super) fn infer_fun_decl(
    fun: &FunDecl,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<(), MetelError> {
    // Native functions have no Metel body to infer. Validate and record their
    // annotated signature for the construction pass; dispatch is by NativeKey.
    if fun.native.is_some() {
        let NativeFunTyResult {
            fun_ty,
            bounds,
            neg_bounds,
            record_kinds,
            assoc_eq,
        } = native_fun_ty(fun, ctx)?;
        // Overloaded native definitions (std::core's assert pair) are
        // dispatched by SymbolId and never enter the name-keyed scheme env.
        if ctx.is_overloaded(&fun.name) {
            return Ok(());
        }
        let env_fvs = ctx.env_free_vars();
        ctx.bind_poly(
            &fun.name,
            generalize(fun_ty.clone(), &env_fvs)
                .with_bounds(&bounds)
                .with_neg_bounds(&neg_bounds)
                .with_record_kinds(&record_kinds)
                .with_assoc_eq_constraints(&assoc_eq),
        );
        fun_generalizations.push(FunGeneralization {
            name: fun.name.clone(),
            fun_ty,
            env_fvs,
            name_map: HashMap::new(),
            bounds,
            neg_bounds,
            record_kinds,
            assoc_projections: HashMap::new(),
            assoc_eq,
            opaque_returns: HashMap::new(),
        });
        return Ok(());
    }

    // For generic functions, create fresh type variables for each parameter name.
    let generic_map = fun_generic_map(fun, ctx);

    // Collect merged bounds (inline + where clause) per TypeVar, register for call-site checking.
    let type_var_bounds = collect_fun_type_var_bounds(fun, &generic_map);
    if !type_var_bounds.is_empty() {
        ctx.register_fun_bounds(fun.name.clone(), type_var_bounds.clone());
    }
    let type_var_record_kinds = collect_fun_type_var_record_kinds(fun, &generic_map);
    if !type_var_record_kinds.is_empty() {
        ctx.register_fun_record_kinds(fun.name.clone(), type_var_record_kinds.clone());
    }
    let neg_type_var_bounds = collect_negative_fun_type_var_bounds(fun, &generic_map);
    if !neg_type_var_bounds.is_empty() {
        ctx.register_neg_fun_bounds(fun.name.clone(), neg_type_var_bounds.clone());
    }
    let assoc_eq_by_var = collect_fun_assoc_eq_constraints(fun, &generic_map);
    if !assoc_eq_by_var.is_empty() {
        ctx.register_fun_assoc_eq_constraints(fun.name.clone(), assoc_eq_by_var.clone());
    }

    let te_to_infer = |te: &TypeExpr, ctx: &mut InferContext| -> Result<InferType, MetelError> {
        // RFC-0082 §2 abstract-case: T::AssocType where T is a generic param.
        if let TypeExpr::Projection {
            base,
            ref assoc_name,
            span: proj_span,
            ..
        } = te
        {
            if let TypeExpr::Named(ref n, _) = **base {
                if let Some(&base_tv) = generic_map.get(n.as_str()) {
                    // Find the aspect(s) that declare this assoc type.
                    let mut matching_aspects: Vec<String> = Vec::new();
                    if let Some(bounds) = type_var_bounds.get(&base_tv) {
                        for aspect in bounds.iter().filter_map(GenericBound::aspect_name) {
                            if let Some(decls) = ctx.aspect_assoc_type_decls(aspect) {
                                if decls.iter().any(|d| d.name == *assoc_name) {
                                    matching_aspects.push(aspect.to_string());
                                }
                            }
                        }
                    }
                    if matching_aspects.len() > 1 {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0013,
                            format!(
                                "ambiguous associated type `{assoc_name}`: multiple aspects declare it: {}",
                                matching_aspects.join(", ")
                            ),
                            proj_span,
                        ));
                    }
                    if let Some(aspect) = matching_aspects.into_iter().next() {
                        return Ok(InferType::Var(
                            ctx.fresh_assoc_projection_var(base_tv, &aspect, assoc_name),
                        ));
                    }
                    // Fallback: named placeholder
                    return Ok(InferType::Named(format!("{n}::{assoc_name}"), vec![]));
                }
            }
        }
        Ok(type_expr_to_infer_with_ctx(te, &generic_map, ctx))
    };

    // #740 part B: swap the assoc-projection log in *before* resolving the
    // signature (params and return type), not just before the body. A
    // `T::AssocType` return-type annotation (e.g. `unwrap<T: Container>(c: &T)
    // -> T::Item`) mints its projection placeholder here, via `te_to_infer`'s
    // abstract-case branch above -- before this swap used to run, that
    // recording landed in whatever log preceded this function (or was lost
    // entirely at the top level) instead of this function's own isolated log,
    // so `build_assoc_projection_map` below never saw it and the scheme's
    // `assoc_projections` came back empty. The instantiation-time backfill in
    // `instantiate_scheme_for_call` (construction.rs) was always correct; it
    // just never had anything to backfill, since the projection was never
    // attached to the scheme in the first place -- which is exactly why this
    // failed with "cannot infer type" even for `let r = unwrap(&b);` calls
    // whose argument fully determines every type involved.
    let (saved_assoc_memo, saved_assoc_log) = ctx.swap_assoc_projections();

    let param_types: Vec<InferType> = fun
        .params
        .iter()
        .map(|p| {
            if let Some(ann) = &p.type_ann {
                te_to_infer(ann, ctx)
            } else {
                Ok(ctx.fresh_var())
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    // RFC-0037: return-position `impl Aspect`. When the return-type annotation
    // contains `ImplAspect` nodes (top-level or nested in Tuple/Array/etc.),
    // rewrite them into fresh anonymous type-param names, create marker TypeVars
    // for each, and record them for post-solve opaque-return processing.
    let mut pending_opaque_returns: Vec<(TypeVar, String)> = Vec::new();
    let ret_ty = if let Some(ann) = &fun.return_type {
        if type_expr_contains_impl_aspect(ann) {
            let mut rw_counter = 0usize;
            let mut replacements: Vec<(String, String)> = Vec::new();
            let rewritten = rewrite_impl_aspect_returns(ann, &mut rw_counter, &mut replacements);
            let mut extended_map = generic_map.clone();
            for (placeholder, aspect_name) in &replacements {
                let tv = ctx.fresh_type_var_raw();
                extended_map.insert(placeholder.clone(), tv);
                pending_opaque_returns.push((tv, aspect_name.clone()));
            }
            type_expr_to_infer_with_generics(&rewritten, &extended_map)
        } else {
            te_to_infer(ann, ctx)?
        }
    } else {
        ctx.fresh_var()
    };

    let env_fvs = ctx.env_free_vars();

    ctx.push_scope();
    let saved_flow = ctx.flow_enter_body();
    for (param, pt) in fun.params.iter().zip(param_types.iter()) {
        ctx.bind_mono(&param.name, pt.clone(), false);
    }

    // Build initial name_map from original TypeVars; will be resolved post-solve below.
    let orig_name_map: HashMap<TypeVar, String> =
        generic_map.iter().map(|(n, &tv)| (tv, n.clone())).collect();
    let saved_type_params = ctx.swap_type_params(generic_map);
    let saved_tp_bounds = ctx.swap_type_param_bounds(type_var_bounds.clone());
    let saved_row_field_vars = ctx.swap_row_field_vars();
    let saved_ret = ctx.push_return_type(ret_ty.clone());
    let body_ty = infer_block(&fun.body, ctx, fun_generalizations)?;

    constrain_with_read_copy(ctx, body_ty, ret_ty.clone(), fun.body.span.clone());

    ctx.pop_return_type(saved_ret);
    ctx.restore_row_field_vars(saved_row_field_vars);
    ctx.swap_type_param_bounds(saved_tp_bounds);
    ctx.swap_type_params(saved_type_params);
    // Capture the projection log recorded during this function's body BEFORE restoring.
    let body_assoc_log = ctx.take_recorded_assoc_projections();
    ctx.restore_assoc_projections(saved_assoc_memo, saved_assoc_log);
    ctx.flow_exit_body(saved_flow);
    ctx.pop_scope();

    let fun_ty = InferType::fun(param_types, ret_ty);

    // Overloaded functions have no single shared binding to constrain; each
    // definition stands alone (its concrete signature lives in the overload
    // table, keyed by SymbolId) and never enters the name-keyed scheme env.
    let is_overloaded = ctx.is_overloaded(&fun.name);

    if !is_overloaded {
        if let Some(pre_reg) = ctx.lookup(&fun.name) {
            ctx.add_constraint(pre_reg, fun_ty.clone(), fun.span.clone());
        }
    }

    // Inline solve-and-generalize: future call sites look up this function via the
    // poly_env and get a fresh instantiation per call, avoiding constraint conflicts
    // when the same polymorphic function is called at different types.
    let solved = ctx.solve()?;
    let partial_subst = ctx.default_literal_vars(&solved);

    // RFC-0037: process pending opaque-return markers. For each marker, check
    // whether the body's own solve resolved it to a concrete type (unlinked case)
    // or left it as a free Var (linked case, e.g. `fun transform(x: impl A) ->
    // impl A { x }` where the return is tied to a generic param).
    //
    // Unlinked markers are "re-abstracted": the concrete type is recorded in
    // `opaque_map` (keyed by a fresh placeholder TypeVar), and a re-abstraction
    // substitution prevents `partial_subst` from collapsing the marker in
    // `resolved_ty`. This makes the function appear polymorphic (the placeholder
    // is quantified by `generalize`) while the recorded concrete type lets
    // construction (Pass 2) backfill the concrete type at each call site.
    let mut opaque_map: HashMap<TypeVar, (String, Type)> = HashMap::new();
    let mut reabstraction = Substitution::new();
    for (marker_tv, aspect_name) in &pending_opaque_returns {
        let resolved_marker = partial_subst.apply(&InferType::Var(*marker_tv));
        #[allow(clippy::match_same_arms)]
        // Var and the wildcard document distinct, deliberate no-ops
        match &resolved_marker {
            InferType::Var(_) => {
                // Linked case: marker is still a free var (tied to a generic
                // param). Ordinary generalize/bind_poly handles it — the caller
                // can name the concrete type here, which is correct (the callee
                // returns the same value the caller handed in).
            }
            InferType::Concrete(_) | InferType::Named(_, _) => {
                // Unlinked case: marker collapsed to a concrete type during the
                // body's own solve. Convert to a `Type` for recording.
                let Ok(concrete_ty) = infer_type_to_type(&resolved_marker, &fun.span) else {
                    // The concrete type still has free vars (mixed case:
                    // real generics + opaque return). Not in the RFC's
                    // examples — skip opaque handling, let it fall through
                    // to ordinary generic behavior.
                    continue;
                };
                // Verify the aspect bound at definition time (RFC-0037 §1.1):
                // the concrete type must implement the declared aspect.
                if !ctx.registry().type_satisfies_aspect(
                    ctx.current_module_path(),
                    &concrete_ty,
                    aspect_name,
                ) {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0012,
                        format!(
                            "return type `{concrete_ty}` does not implement `{aspect_name}` \
                             (required by `{}` return type `impl {aspect_name}`)",
                            fun.name
                        ),
                        &fun.span,
                    ));
                }
                let placeholder_tv = ctx.fresh_type_var_raw();
                reabstraction.bind(*marker_tv, InferType::Var(placeholder_tv));
                opaque_map.insert(placeholder_tv, (aspect_name.clone(), concrete_ty));
            }
            _ => {}
        }
    }

    let resolved_ty = if opaque_map.is_empty() {
        partial_subst.apply(&fun_ty)
    } else {
        // Compose re-abstraction (self, wins on overlap) with partial_subst
        // (other), then apply the combined substitution to fun_ty. The marker
        // vars are rebound to fresh placeholders that partial_subst cannot
        // resolve, so they survive as free vars for `generalize` to quantify.
        reabstraction.compose(&partial_subst).apply(&fun_ty)
    };

    // Overloaded definitions are dispatched by SymbolId, never by name: the
    // scheme env and the export surface know nothing about them. The body was
    // still inferred and solved above, so type errors inside it are reported.
    if is_overloaded {
        return Ok(());
    }

    let mut scheme = generalize(resolved_ty.clone(), &env_fvs);
    let names_by_var: HashMap<TypeVar, String> = orig_name_map
        .iter()
        .filter_map(
            |(&original, name)| match partial_subst.apply(&InferType::Var(original)) {
                InferType::Var(resolved) => Some((resolved, name.clone())),
                _ => None,
            },
        )
        .collect();
    scheme.param_names = scheme
        .quantified_vars
        .iter()
        .map(|var| names_by_var.get(var).cloned().unwrap_or_default())
        .collect();
    // Attach assoc_projections if any projections were recorded during body inference.
    // `proj_map` is already keyed by the FINAL (post-`partial_subst`) TypeVar (see
    // `build_assoc_projection_map`), so it's carried into `FunGeneralization` as-is,
    // with no further remapping needed -- unlike `bounds`/`neg_bounds` below, which
    // are collected pre-solve and must still be remapped through `partial_subst`.
    let proj_map = if body_assoc_log.is_empty() {
        HashMap::new()
    } else {
        build_assoc_projection_map(&body_assoc_log, &partial_subst, &scheme)
    };
    let scheme = if proj_map.is_empty() {
        scheme
    } else {
        scheme.with_assoc_projections(&proj_map)
    };
    // RFC-0037: attach opaque-return metadata so the locally-bound scheme
    // (used by Pass 1 call-site instantiation) carries the same identity
    // info as the cross-module-exported scheme.
    let scheme = if opaque_map.is_empty() {
        scheme
    } else {
        scheme.with_opaque_returns(&opaque_map)
    };
    let scheme = scheme.with_record_kinds(&type_var_record_kinds);
    ctx.bind_poly(fun.name.clone(), scheme);

    // After solving, the original TypeVars may have been unified with others.
    // Remap name_map through partial_subst so quantified_vars (which are in the
    // resolved type) have correct names.
    let name_map: HashMap<TypeVar, String> = orig_name_map
        .into_iter()
        .filter_map(|(orig_tv, name)| {
            match partial_subst.apply(&InferType::Var(orig_tv)) {
                InferType::Var(final_tv) => Some((final_tv, name)),
                _ => None, // var was solved to a concrete type; no longer generic
            }
        })
        .collect();
    let bounds: HashMap<TypeVar, Vec<GenericBound>> = type_var_bounds
        .iter()
        .filter_map(
            |(orig_tv, b)| match partial_subst.apply(&InferType::Var(*orig_tv)) {
                InferType::Var(final_tv) => Some((final_tv, b.clone())),
                _ => None,
            },
        )
        .collect();
    let neg_bounds: HashMap<TypeVar, Vec<GenericBound>> = neg_type_var_bounds
        .iter()
        .filter_map(
            |(orig_tv, b)| match partial_subst.apply(&InferType::Var(*orig_tv)) {
                InferType::Var(final_tv) => Some((final_tv, b.clone())),
                _ => None,
            },
        )
        .collect();
    let record_kinds: HashMap<TypeVar, bool> = type_var_record_kinds
        .iter()
        .filter_map(
            |(orig_tv, is_record)| match partial_subst.apply(&InferType::Var(*orig_tv)) {
                InferType::Var(final_tv) => Some((final_tv, *is_record)),
                _ => None,
            },
        )
        .collect();
    // Remap equality constraints (RFC-0082 §4) the same way as bounds/neg_bounds:
    // keyed by the ORIGINAL declared TypeVar (from collect_fun_assoc_eq_constraints),
    // re-keyed to the FINAL post-solve TypeVar so it lines up with `resolved_ty`'s
    // free vars (what `generalize` re-quantifies over). Each constraint's expected
    // `InferType` is also substituted, since it may itself reference another
    // generic param (the `U` in `Deref<Target = U>`, RFC-0082 §3a's escape hatch).
    let assoc_eq: HashMap<TypeVar, Vec<(String, String, InferType)>> = assoc_eq_by_var
        .iter()
        .filter_map(
            |(orig_tv, constraints)| match partial_subst.apply(&InferType::Var(*orig_tv)) {
                InferType::Var(final_tv) => Some((
                    final_tv,
                    constraints
                        .iter()
                        .map(|(aspect, assoc, ty)| {
                            (aspect.clone(), assoc.clone(), partial_subst.apply(ty))
                        })
                        .collect(),
                )),
                _ => None,
            },
        )
        .collect();
    // Store resolved_ty (post-solve) so the re-generalization in check_impl uses the
    // already-solved type and is not perturbed by a now-empty final substitution.
    fun_generalizations.push(FunGeneralization {
        name: fun.name.clone(),
        fun_ty: resolved_ty,
        env_fvs,
        name_map,
        bounds,
        neg_bounds,
        record_kinds,
        assoc_projections: proj_map,
        assoc_eq,
        opaque_returns: opaque_map,
    });
    Ok(())
}

// Exhaustive match over every AST/type-system variant; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
pub(super) fn infer_impl_method(
    method: &FunDecl,
    ib: &crate::ast::ImplBlock,
    target_name: &str,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<(), MetelError> {
    let array_target_generic_name = match &ib.target_type {
        TypeExpr::Array(inner) => match inner.as_ref() {
            TypeExpr::Named(name, args) if args.is_empty() => ib
                .generics
                .iter()
                .find(|gp| gp.name == *name)
                .map(|_| name.as_str()),
            _ => None,
        },
        _ => None,
    };
    // Start with the method's own generic params.
    let mut generic_map: HashMap<String, TypeVar> = method
        .generics
        .iter()
        .map(|g| (g.name.clone(), ctx.fresh_type_var_raw()))
        .collect();
    // #746: captured *before* the struct's own params are merged into
    // `generic_map` below, so this holds exactly the method's own generics --
    // used later to decide whether this method needs a polymorphic scheme
    // even when the struct/impl contributes no generics of its own.
    let method_own_tvars: Vec<TypeVar> = method
        .generics
        .iter()
        .filter_map(|g| generic_map.get(&g.name).copied())
        .collect();
    // Captured at the same point, for the same reason: `generic_map` is later
    // moved into `ctx.swap_type_params`, so the method's own bounds (used
    // below to attach to the call-site-checked scheme) must be collected now.
    let method_own_bounds = collect_fun_type_var_bounds(method, &generic_map);
    let method_own_neg_bounds = collect_negative_fun_type_var_bounds(method, &generic_map);

    // Seed with the target struct/enum's generic params so that type annotations
    // referencing e.g. `T` in `impl SortedList<T>` resolve to TypeVars and
    // aspect methods on bounded params are available in the body.
    let mut struct_bounds: HashMap<TypeVar, Vec<GenericBound>> = HashMap::new();
    // Ordered TypeVars for the struct's generic params (same order as struct type args).
    let mut struct_tvars_ordered: Vec<TypeVar> = Vec::new();
    if let Some(names) = ctx.struct_generic_names_for(target_name).cloned() {
        let bounds_by_pos: Option<Vec<Vec<GenericBound>>> =
            ctx.get_type_param_bounds(target_name).cloned();
        for (i, name) in names.iter().enumerate() {
            if !generic_map.contains_key(name) {
                let tv = ctx.fresh_type_var_raw();
                generic_map.insert(name.clone(), tv);
                struct_tvars_ordered.push(tv);
                if let Some(ref bp) = bounds_by_pos {
                    if let Some(b) = bp.get(i) {
                        if !b.is_empty() {
                            struct_bounds.insert(tv, b.clone());
                        }
                    }
                }
            }
        }
    } else if let Some(name) = array_target_generic_name {
        if !generic_map.contains_key(name) {
            let tv = ctx.fresh_type_var_raw();
            generic_map.insert(name.to_string(), tv);
            struct_tvars_ordered.push(tv);
        }
    }

    // RFC-0036 §2.2: compute impl-level bounds (from the impl block's own
    // where clause / inline bounds) and merge them into `struct_bounds` so that
    // method dispatch and type annotations inside the body can see impl-level
    // constraints (e.g. `impl<T: Display> Greet for Box1<T>` needs `T: Display`
    // visible when resolving `self.value.to_string()`).
    let generic_names_for_impl: Vec<String> = if let Some(name) = array_target_generic_name {
        vec![name.to_string()]
    } else {
        ctx.struct_generic_names_for(target_name)
            .cloned()
            .unwrap_or_default()
    };
    let structural_self_type_expr = array_target_generic_name
        .map(|name| TypeExpr::Array(Box::new(TypeExpr::Named(name.to_string(), vec![]))));
    let synth =
        super::super::registry::synth_generics_for_impl(&generic_names_for_impl, &ib.generics);
    let impl_bounds: Vec<Vec<GenericBound>> =
        super::super::registry::collect_type_param_bounds(&synth, ib.where_clause.as_ref());
    let impl_neg_bounds: Vec<Vec<GenericBound>> =
        super::super::registry::collect_negative_type_param_bounds(
            &synth,
            ib.where_clause.as_ref(),
        );

    // Merge impl-level bounds into struct_bounds (union: keep any existing
    // struct-level bounds and add the impl's).
    for (i, tv) in struct_tvars_ordered.iter().enumerate() {
        if let Some(ib_bounds) = impl_bounds.get(i) {
            if !ib_bounds.is_empty() {
                struct_bounds
                    .entry(*tv)
                    .or_default()
                    .extend(ib_bounds.iter().cloned());
            }
        }
    }

    // #746: a method's *own* generic bound (`fun describe<U: Display2>(...)`,
    // inline or via the method's own `where` clause) was never merged into
    // `struct_bounds` -- only the struct's and the impl block's own bounds
    // were. `generic_map` already carries the method's generics (seeded at
    // the top of this function), so `collect_fun_type_var_bounds` -- the
    // same helper `infer_fun_decl` uses for free functions -- picks them up
    // correctly by name; merge them in the same union fashion as above.
    for (tv, bounds) in collect_fun_type_var_bounds(method, &generic_map) {
        struct_bounds.entry(tv).or_default().extend(bounds);
    }

    // Include struct TypeVars in self type so call-site unification resolves correctly.
    // For a primitive target (`impl Display for i64`) the self type must be the
    // concrete primitive, since call sites produce `Concrete(Type::I64)` and the
    // unifier has no Named↔Concrete bridge (METEL-181).
    let self_ty = if let Some(element_tv) = struct_tvars_ordered
        .first()
        .copied()
        .filter(|_| array_target_generic_name.is_some())
    {
        InferType::Array(Box::new(InferType::Var(element_tv)))
    } else if let Some(prim) = primitive_type_from_name(target_name) {
        InferType::Concrete(prim)
    } else if struct_tvars_ordered.is_empty() {
        InferType::Named(target_name.to_string(), vec![])
    } else {
        InferType::Named(
            target_name.to_string(),
            struct_tvars_ordered
                .iter()
                .map(|&tv| InferType::Var(tv))
                .collect(),
        )
    };

    // #740/#774 (revised): `Self` is not a name special-cased per call site -- it is
    // this method's own type parameter, always instantiated to `self_ty`. Binding it
    // into `generic_map`/`struct_bounds` the same way an ordinary bound generic
    // (`T: Container`) already is lets every existing generic-param-aware path
    // (the `T::AssocType` abstract case just below, `fresh_assoc_projection_var`,
    // aspect-bound checking) resolve `Self::AssocType` for free, with no bespoke
    // "if n == Self" branch of its own -- and, unlike that branch (which only ever
    // covered this function's own param/return-type resolution), also reaches a
    // body-internal `let x: Self::Item = ...;` statement's annotation, resolved
    // through the ordinary `ann_to_infer` path, which already has its own
    // `ctx.type_params()`-based abstract-case check for exactly this shape.
    let self_type_var = ctx.fresh_type_var_raw();
    generic_map.insert("Self".to_string(), self_type_var);
    if let Some(aspect) = &ib.aspect_name {
        struct_bounds
            .entry(self_type_var)
            .or_default()
            .push(GenericBound::Aspect(aspect.clone()));
    }
    ctx.add_constraint(
        InferType::Var(self_type_var),
        self_ty.clone(),
        ib.span.clone(),
    );

    let te_to_infer = |te: &TypeExpr, ctx: &mut InferContext| -> Result<InferType, MetelError> {
        // RFC-0082 §2 abstract-case: T::AssocType where T is a generic param -- `Self`
        // included, now that it's bound into `generic_map` above like any other.
        if let TypeExpr::Projection {
            base,
            ref assoc_name,
            span: proj_span,
            ..
        } = te
        {
            if let TypeExpr::Named(ref n, _) = **base {
                if let Some(&base_tv) = generic_map.get(n.as_str()) {
                    let mut matching_aspects: Vec<String> = Vec::new();
                    if let Some(bounds) = struct_bounds.get(&base_tv) {
                        for aspect in bounds.iter().filter_map(GenericBound::aspect_name) {
                            if let Some(decls) = ctx.aspect_assoc_type_decls(aspect) {
                                if decls.iter().any(|d| d.name == *assoc_name) {
                                    matching_aspects.push(aspect.to_string());
                                }
                            }
                        }
                    }
                    if matching_aspects.len() > 1 {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0013,
                            format!(
                                "ambiguous associated type `{assoc_name}`: multiple aspects declare it: {}",
                                matching_aspects.join(", ")
                            ),
                            proj_span,
                        ));
                    }
                    if let Some(aspect) = matching_aspects.into_iter().next() {
                        return Ok(InferType::Var(
                            ctx.fresh_assoc_projection_var(base_tv, &aspect, assoc_name),
                        ));
                    }
                    return Ok(InferType::Named(format!("{n}::{assoc_name}"), vec![]));
                }
            }
        }
        Ok(if let Some(self_replacement) = &structural_self_type_expr {
            let lowered = substitute_structural_self(te, self_replacement);
            type_expr_to_infer_with_generics(&lowered, &generic_map)
        } else {
            // #774: `type_expr_to_infer_with_self`/`_with_generics_and_self` resolve
            // `Self` correctly but carry no `AssocResolveCtx` (so no registry access),
            // which `Self.{ field }` needs to look up the target struct's actual
            // fields -- unlike `Self::AssocType`, handled entirely above via the
            // abstract-case branch and `fresh_assoc_projection_var`, a record
            // projection's resolution genuinely lives in `conversions.rs` and needs
            // both pieces of context at once. Still needs `self_ty_name` explicitly:
            // `resolve_record_projection_type` looks up a struct's fields by name
            // directly, not through `generic_map`'s TypeVar indirection the way an
            // ordinary `Named` lookup now can for `Self`.
            let assoc_ctx = AssocResolveCtx {
                registry: ctx.registry(),
                current_module: ctx.current_module_path(),
                current_aspect: ib.aspect_name.as_deref(),
            };
            type_expr_to_infer_with_assoc_ctx(te, &generic_map, Some(target_name), &assoc_ctx)
        })
    };
    // #740 part B: swap the assoc-projection log in *before* resolving the
    // signature (params and return type), the same fix and for the same reason
    // as `infer_fun_decl`'s own swap above -- a `T::AssocType` return-type
    // annotation records its projection placeholder while `param_types`/`ret_ty`
    // are computed below, and that needs to land in this method's own isolated
    // log rather than whatever preceded it (or nothing, at the top level), or
    // `build_assoc_projection_map` never sees it and the scheme's
    // `assoc_projections` comes back empty regardless of what the body itself
    // does. Applies uniformly to native methods too (taken/restored below,
    // after the `if`) since a native method's signature is exactly as capable
    // of naming a projection as a non-native one's, even with no body to swap
    // around on its own.
    let (saved_assoc_memo, saved_assoc_log) = ctx.swap_assoc_projections();
    let param_types: Vec<InferType> = method
        .params
        .iter()
        .map(|p| {
            if p.name == "self" {
                Ok(self_ty.clone())
            } else if let Some(ann) = &p.type_ann {
                te_to_infer(ann, ctx)
            } else {
                Ok(ctx.fresh_var())
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    let ret_ty = method
        .return_type
        .as_ref()
        .map_or_else(|| Ok(InferType::unit()), |t| te_to_infer(t, ctx))?;

    // Native methods have no Metel body; their signature comes entirely from
    // annotations (METEL-181). Skip body inference but still register the
    // method scheme below so call sites resolve.
    if method.native.is_none() {
        ctx.push_scope();
        let saved_flow = ctx.flow_enter_body();
        for (p, pt) in method.params.iter().zip(param_types.iter()) {
            let is_mutable =
                p.mutable || matches!(p.receiver, Some(crate::ast::ReceiverKind::RefMut));
            ctx.bind_mono(&p.name, pt.clone(), is_mutable);
        }
        let saved_type_params = ctx.swap_type_params(generic_map);
        let saved_tp_bounds = ctx.swap_type_param_bounds(struct_bounds);
        let saved_row_field_vars = ctx.swap_row_field_vars();
        let saved_ret = ctx.push_return_type(ret_ty.clone());
        let body_ty = infer_block(&method.body, ctx, fun_generalizations)?;
        constrain_with_read_copy(ctx, body_ty, ret_ty.clone(), method.body.span.clone());
        ctx.pop_return_type(saved_ret);
        ctx.restore_row_field_vars(saved_row_field_vars);
        ctx.swap_type_param_bounds(saved_tp_bounds);
        ctx.swap_type_params(saved_type_params);
        ctx.flow_exit_body(saved_flow);
        ctx.pop_scope();
    }
    let body_assoc_log = ctx.take_recorded_assoc_projections();
    ctx.restore_assoc_projections(saved_assoc_memo, saved_assoc_log);

    let solved = ctx.solve()?;
    let partial_subst = ctx.default_literal_vars(&solved);
    let fun_ty = InferType::fun(param_types, ret_ty);
    let resolved_fun_ty = partial_subst.apply(&fun_ty);

    // Map each struct type-param TypeVar through the solution: body inference
    // (e.g. a `self.value` field access) may have unified the original param var
    // with a fresh representative, so `struct_tvars_ordered` can be stale. The
    // scheme is generalized from `resolved_fun_ty`, so its quantified vars and the
    // `struct_tvars` we hand to the call site must use the *resolved* representatives.
    let struct_tvars_resolved: Vec<TypeVar> = struct_tvars_ordered
        .iter()
        .map(|&tv| match partial_subst.apply(&InferType::Var(tv)) {
            InferType::Var(v) => v,
            _ => tv,
        })
        .collect();

    // If the resolved method type still has free TypeVars from the struct's generic params
    // *or the method's own* (#746 -- a method's own generic, e.g. `fun describe<U:
    // Aspect>`, must keep this method polymorphic even on an otherwise concrete target,
    // exactly as a free function with the same bound would stay polymorphic; missing
    // the method-own half here used to let `resolved_fun_ty` register as a plain
    // concrete `Type` in `method_env` whenever the struct itself had no generics,
    // silently dropping the method's own bound from call-site checking, then failing
    // with a confusing internal error when its body was later constructed at the
    // wrong (unconditional) time instead of per call site),
    // store it as a polymorphic scheme so Pass 2 can instantiate it per call site.
    let struct_tvars_free: std::collections::HashSet<TypeVar> =
        struct_tvars_resolved.iter().copied().collect();
    let method_tvars_resolved: Vec<TypeVar> = method_own_tvars
        .iter()
        .map(|&tv| match partial_subst.apply(&InferType::Var(tv)) {
            InferType::Var(v) => v,
            _ => tv,
        })
        .collect();
    let method_tvars_free: std::collections::HashSet<TypeVar> =
        method_tvars_resolved.iter().copied().collect();
    if (!struct_tvars_free.is_empty() || !method_tvars_free.is_empty())
        && free_vars(&resolved_fun_ty)
            .iter()
            .any(|v| struct_tvars_free.contains(v) || method_tvars_free.contains(v))
    {
        let mut scheme = generalize(resolved_fun_ty, &std::collections::HashSet::new());
        // RFC-0036 §2.2: attach impl-level bounds keyed by resolved tvars so
        // use-site checking can verify the concrete receiver satisfies them.
        let mut by_var: std::collections::HashMap<TypeVar, Vec<GenericBound>> = impl_bounds
            .iter()
            .enumerate()
            .filter_map(|(i, bounds)| {
                if bounds.is_empty() {
                    return None;
                }
                let resolved_tv = struct_tvars_resolved.get(i)?;
                Some((*resolved_tv, bounds.clone()))
            })
            .collect();
        let mut by_neg_var: std::collections::HashMap<TypeVar, Vec<GenericBound>> = impl_neg_bounds
            .iter()
            .enumerate()
            .filter_map(|(i, bounds)| {
                if bounds.is_empty() {
                    return None;
                }
                let resolved_tv = struct_tvars_resolved.get(i)?;
                Some((*resolved_tv, bounds.clone()))
            })
            .collect();
        // #746: also attach the method's *own* bounds (e.g. `U: Display2` on
        // `fun describe<U: Display2>`), keyed by U's *resolved* TypeVar --
        // otherwise a bound violated at the call site (`f.describe(bad_arg)`)
        // was never checked at all, only failing later, confusingly, when
        // the body was reconstructed at call time.
        for (tv, bounds) in &method_own_bounds {
            let resolved_tv = match partial_subst.apply(&InferType::Var(*tv)) {
                InferType::Var(v) => v,
                _ => *tv,
            };
            by_var
                .entry(resolved_tv)
                .or_default()
                .extend(bounds.clone());
        }
        for (tv, bounds) in &method_own_neg_bounds {
            let resolved_tv = match partial_subst.apply(&InferType::Var(*tv)) {
                InferType::Var(v) => v,
                _ => *tv,
            };
            by_neg_var
                .entry(resolved_tv)
                .or_default()
                .extend(bounds.clone());
        }
        scheme = scheme.with_bounds(&by_var).with_neg_bounds(&by_neg_var);
        let scheme = if body_assoc_log.is_empty() {
            scheme
        } else {
            let proj_map = build_assoc_projection_map(&body_assoc_log, &partial_subst, &scheme);
            scheme.with_assoc_projections(&proj_map)
        };
        if array_target_generic_name.is_some() {
            ctx.register_array_method_scheme(
                method.name.clone(),
                scheme.clone(),
                struct_tvars_resolved.clone(),
            );
            ctx.register_array_method_scheme_variant(
                method.name.clone(),
                scheme,
                struct_tvars_resolved,
                ib.aspect_name.clone(),
                method.span.clone(),
            );
        } else {
            ctx.register_method_scheme(
                target_name,
                method.name.clone(),
                scheme.clone(),
                struct_tvars_resolved.clone(),
            );
            ctx.register_method_scheme_variant(
                target_name,
                method.name.clone(),
                scheme,
                struct_tvars_resolved,
                ib.aspect_name.clone(),
                method.span.clone(),
            );
        }
    } else if array_target_generic_name.is_some() {
        ctx.register_array_method(method.name.clone(), resolved_fun_ty);
    } else {
        ctx.register_method(target_name, method.name.clone(), resolved_fun_ty);
    }
    Ok(())
}

pub(super) fn substitute_structural_self(te: &TypeExpr, replacement: &TypeExpr) -> TypeExpr {
    match te {
        TypeExpr::Named(name, args) if name == "Self" && args.is_empty() => replacement.clone(),
        TypeExpr::Named(name, args) => TypeExpr::Named(
            name.clone(),
            args.iter()
                .map(|arg| substitute_structural_self(arg, replacement))
                .collect(),
        ),
        TypeExpr::Unit => TypeExpr::Unit,
        TypeExpr::Tuple(items) => TypeExpr::Tuple(
            items
                .iter()
                .map(|item| substitute_structural_self(item, replacement))
                .collect(),
        ),
        TypeExpr::Record(fields) => TypeExpr::Record(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), substitute_structural_self(ty, replacement)))
                .collect(),
        ),
        TypeExpr::Array(inner) => TypeExpr::Array(Box::new(substitute_structural_self(
            inner.as_ref(),
            replacement,
        ))),
        TypeExpr::SizedArray(inner, len) => TypeExpr::SizedArray(
            Box::new(substitute_structural_self(inner.as_ref(), replacement)),
            *len,
        ),
        TypeExpr::Reference(inner) => TypeExpr::Reference(Box::new(substitute_structural_self(
            inner.as_ref(),
            replacement,
        ))),
        TypeExpr::MutReference(inner) => TypeExpr::MutReference(Box::new(
            substitute_structural_self(inner.as_ref(), replacement),
        )),
        TypeExpr::Fun {
            params,
            return_type: ret,
            call_multiplicity,
            call_mutation,
        } => TypeExpr::Fun {
            params: params
                .iter()
                .map(|param| substitute_structural_self(param, replacement))
                .collect(),
            return_type: ret
                .as_ref()
                .map(|ret_ty| Box::new(substitute_structural_self(ret_ty.as_ref(), replacement))),
            call_multiplicity: *call_multiplicity,
            call_mutation: *call_mutation,
        },
        TypeExpr::ImplAspect {
            bound,
            source_spell,
            span,
        } => TypeExpr::ImplAspect {
            bound: Box::new(substitute_structural_self(bound.as_ref(), replacement)),
            source_spell: source_spell.clone(),
            span: span.clone(),
        },
        TypeExpr::Projection {
            base,
            assoc_name,
            span,
        } => TypeExpr::Projection {
            base: Box::new(substitute_structural_self(base.as_ref(), replacement)),
            assoc_name: assoc_name.clone(),
            span: span.clone(),
        },
        TypeExpr::RecordProjection { path, fields, span } => TypeExpr::RecordProjection {
            path: path.clone(),
            fields: fields.clone(),
            span: span.clone(),
        },
        TypeExpr::DynAspect { bound, span } => TypeExpr::DynAspect {
            bound: Box::new(substitute_structural_self(bound.as_ref(), replacement)),
            span: span.clone(),
        },
    }
}

pub(super) fn infer_default_aspect_method(
    method: &AspectMethod,
    target_name: &str,
    aspect_name: &str,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<(), MetelError> {
    let generic_map: HashMap<String, TypeVar> = method
        .generics
        .iter()
        .map(|g| (g.name.clone(), ctx.fresh_type_var_raw()))
        .collect();

    // RFC-0082 §1.2: a bare associated-type name in the aspect's own default
    // method body (e.g. `Item` in `fun get_twice(self) -> Item { ... }`) must
    // resolve to this impl's concrete binding, same as register_default_aspect_method
    // does for the pre-registered signature -- this is the SEPARATE conversion that
    // actually type-checks the default body itself against its declared return type.
    let te_to_infer = |te: &TypeExpr, ctx: &InferContext| -> InferType {
        if let TypeExpr::Named(n, args) = te {
            if args.is_empty()
                && ctx
                    .registry()
                    .aspect_assoc_type_decls(aspect_name)
                    .is_some_and(|decls| decls.iter().any(|d| d.name == *n))
            {
                if let Some(concrete) = ctx.registry().impl_assoc_type(
                    ctx.current_module_path(),
                    target_name,
                    aspect_name,
                    n,
                ) {
                    return type_to_infer(concrete);
                }
            }
        }
        if generic_map.is_empty() {
            type_expr_to_infer_with_self(te, target_name)
        } else {
            type_expr_to_infer_with_generics_and_self(te, &generic_map, target_name)
        }
    };

    // For a primitive target the `self` type must be the concrete primitive, so
    // an inherited default method unifies with call sites that produce
    // `Concrete(Type::I64)` (METEL-149 / METEL-181). User structs stay `Named`.
    let self_ty = match primitive_type_from_name(target_name) {
        Some(prim) => InferType::Concrete(prim),
        None => InferType::Named(target_name.to_string(), vec![]),
    };
    let param_types: Vec<InferType> = method
        .params
        .iter()
        .map(|p| {
            if p.name == "self" {
                self_ty.clone()
            } else if let Some(ann) = &p.type_ann {
                te_to_infer(ann, ctx)
            } else {
                ctx.fresh_var()
            }
        })
        .collect();
    let ret_ty = method
        .return_type
        .as_ref()
        .map_or_else(InferType::unit, |ann| te_to_infer(ann, ctx));
    let body = method
        .default_body
        .as_ref()
        .ok_or_else(|| MetelError::internal("missing aspect default body"))?;

    ctx.push_scope();
    let saved_flow = ctx.flow_enter_body();
    for (p, pt) in method.params.iter().zip(param_types.iter()) {
        let is_mutable = p.mutable || matches!(p.receiver, Some(crate::ast::ReceiverKind::RefMut));
        ctx.bind_mono(&p.name, pt.clone(), is_mutable);
    }
    let saved_type_params = ctx.swap_type_params(generic_map);
    let saved_ret = ctx.push_return_type(ret_ty.clone());
    let body_ty = infer_block(body, ctx, fun_generalizations)?;
    constrain_with_read_copy(ctx, body_ty, ret_ty.clone(), body.span.clone());
    ctx.pop_return_type(saved_ret);
    ctx.swap_type_params(saved_type_params);
    ctx.flow_exit_body(saved_flow);
    ctx.pop_scope();

    let solved = ctx.solve()?;
    let partial_subst = ctx.default_literal_vars(&solved);
    let fun_ty = InferType::fun(param_types, ret_ty);
    let resolved_fun_ty = partial_subst.apply(&fun_ty);
    ctx.register_method(target_name, method.name.clone(), resolved_fun_ty);
    Ok(())
}
