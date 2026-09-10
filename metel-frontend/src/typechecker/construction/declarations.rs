use super::{
    construct_block, construct_expr, construct_stmt, fun_body_diverges, infer_type_to_type,
    maybe_dyn_coerce, maybe_fn_move_coerce, maybe_read_copy, maybe_singleton_coerce,
    resolved_to_type, type_expr_to_infer_with_assoc_ctx, AspectMethod, AssocResolveCtx,
    ConstructCtx, Decl, Expr, FunBody, FunDecl, HashMap, ImplBlock, InferType, MetelError,
    Substitution, Type, TypeErrorCode, TypeExpr, TypeScheme, TypeVar, TypedAspectDecl, TypedDecl,
    TypedEnumDecl, TypedExpr, TypedFunDecl, TypedImplBlock, TypedLetDecl, TypedMutDecl,
    TypedStructDecl,
};

/// A `TypedFunDecl` for an impl-block method: everything but `body` is copied
/// straight off the source `FunDecl` (methods carry no top-level identity).
fn method_fun_decl(
    method: &FunDecl,
    param_ids: Vec<Option<crate::identity::LocalId>>,
    body: FunBody,
) -> TypedFunDecl {
    TypedFunDecl {
        name: method.name.clone(),
        generics: method.generics.clone(),
        params: method.params.clone(),
        param_ids,
        return_type: method.return_type.clone(),
        body,
        symbol_id: None,
        def_id: None,
        span: method.span.clone(),
    }
}

#[allow(clippy::too_many_lines)]
pub(super) fn construct_decl(decl: &Decl, ctx: &mut ConstructCtx) -> Result<TypedDecl, MetelError> {
    match decl {
        Decl::Let(ld) => {
            // Let-polymorphism: if a closure is in scheme_env with quantified vars,
            // store it as GenericClosure. The name stays absent from ctx.env so call
            // sites use scheme_env instantiation in construct_call.
            if let Expr::Closure {
                captures,
                call_multiplicity,
                call_mutation,
                params,
                return_type,
                body,
                span: cls_span,
            } = &ld.value
            {
                if let Some(scheme) = ctx.scheme_env.get(ld.name.as_str()) {
                    if !scheme.quantified_vars.is_empty() {
                        return Ok(TypedDecl::Let(TypedLetDecl {
                            name: ld.name.clone(),
                            type_ann: ld.type_ann.clone(),
                            value: TypedExpr::GenericClosure {
                                name: Some(ld.name.clone()),
                                captures: captures.clone(),
                                capture_ids: ctx.capture_local_ids(captures),
                                call_multiplicity: *call_multiplicity,
                                call_mutation: *call_mutation,
                                params: params.clone(),
                                param_ids: ctx.param_local_ids(params),
                                return_type: return_type.clone(),
                                body: body.clone(),
                                ty: Type::Unit,
                                span: cls_span.clone(),
                            },
                            def_id: None,
                            local_id: ctx.local_binding_at(&ld.span),
                            span: ld.span.clone(),
                        }));
                    }
                }
            }
            // metel-core#736 / RFC-0138: a bare reference to an already-declared
            // generic function (`let alias = identity;`) needs the same treatment
            // as the closure-literal case above -- the widened inference-side gate
            // (`infer_decl`'s `Decl::Let` arm) re-generalizes `alias` into
            // `scheme_env` under its own name whenever this shape matches, so the
            // check below is exactly the closure case's own check, just sourcing
            // `params`/`return_type`/`body` from the referenced function's own
            // declaration (via `ctx.fn_table`, hoisted in `construct_program`/
            // `construct_block`) instead of an inline literal.
            if let Expr::Ident(name, ident_span) = &ld.value {
                if let Some(scheme) = ctx.scheme_env.get(ld.name.as_str()) {
                    if !scheme.quantified_vars.is_empty() {
                        if let Some((params, return_type, body)) = ctx.lookup_fn_decl(name) {
                            let (params, return_type, body) =
                                (params.clone(), return_type.clone(), body.clone());
                            return Ok(TypedDecl::Let(TypedLetDecl {
                                name: ld.name.clone(),
                                type_ann: ld.type_ann.clone(),
                                value: TypedExpr::GenericClosure {
                                    name: Some(ld.name.clone()),
                                    captures: vec![],
                                    capture_ids: vec![],
                                    call_multiplicity: crate::types::CallMultiplicity::Many,
                                    call_mutation: crate::types::CallMutation::Reading,
                                    param_ids: ctx.param_local_ids(&params),
                                    params,
                                    return_type,
                                    body,
                                    ty: Type::Unit,
                                    span: ident_span.clone(),
                                },
                                def_id: None,
                                local_id: ctx.local_binding_at(&ld.span),
                                span: ld.span.clone(),
                            }));
                        }
                    }
                }
            }
            let expected_ty = ld
                .type_ann
                .as_ref()
                .map(|ann| resolved_to_type(&ctx.type_expr_to_infer_ctx(ann), ctx.subst, &ld.span))
                .transpose()?;
            let value = construct_expr(&ld.value, expected_ty.as_ref(), ctx)?;
            let value = match &expected_ty {
                Some(t) => {
                    let value =
                        maybe_read_copy(t, value, &ld.span, ctx.registry, ctx.current_module)?;
                    let value = maybe_singleton_coerce(t, value, &ld.span, ctx.registry)?;
                    let value = maybe_dyn_coerce(t, value, &ld.span, ctx)?;
                    maybe_fn_move_coerce(t, value)
                }
                None => value,
            };
            ctx.note_consumed(&value);
            let ty = expected_ty.unwrap_or_else(|| value.ty().clone());
            ctx.bind(&ld.name, ty);
            Ok(TypedDecl::Let(TypedLetDecl {
                name: ld.name.clone(),
                type_ann: ld.type_ann.clone(),
                value,
                def_id: None,
                local_id: ctx.local_binding_at(&ld.span),
                span: ld.span.clone(),
            }))
        }
        Decl::Mut(md) => {
            let expected_ty = md
                .type_ann
                .as_ref()
                .map(|ann| resolved_to_type(&ctx.type_expr_to_infer_ctx(ann), ctx.subst, &md.span))
                .transpose()?;
            let value = construct_expr(&md.value, expected_ty.as_ref(), ctx)?;
            let value = match &expected_ty {
                Some(t) => {
                    let value =
                        maybe_read_copy(t, value, &md.span, ctx.registry, ctx.current_module)?;
                    let value = maybe_singleton_coerce(t, value, &md.span, ctx.registry)?;
                    let value = maybe_dyn_coerce(t, value, &md.span, ctx)?;
                    maybe_fn_move_coerce(t, value)
                }
                None => value,
            };
            ctx.note_consumed(&value);
            let ty = expected_ty.unwrap_or_else(|| value.ty().clone());
            ctx.bind_mut(&md.name, ty);
            Ok(TypedDecl::Mut(TypedMutDecl {
                name: md.name.clone(),
                type_ann: md.type_ann.clone(),
                value,
                def_id: None,
                local_id: ctx.local_binding_at(&md.span),
                span: md.span.clone(),
            }))
        }
        Decl::Fun(fd) => construct_fun_decl(fd, ctx),
        Decl::Struct(sd) => Ok(TypedDecl::Struct(TypedStructDecl {
            name: sd.name.clone(),
            generics: sd.generics.clone(),
            fields: sd.fields.clone(),
            span: sd.span.clone(),
        })),
        Decl::Enum(ed) => Ok(TypedDecl::Enum(TypedEnumDecl {
            name: ed.name.clone(),
            generics: ed.generics.clone(),
            variants: ed.variants.clone(),
            span: ed.span.clone(),
        })),
        Decl::Impl(ib) => construct_impl_decl(ib, ctx),
        Decl::Aspect(td) => Ok(TypedDecl::Aspect(TypedAspectDecl {
            name: td.name.clone(),
            generics: td.generics.clone(),
            methods: td.methods.clone(),
            span: td.span.clone(),
        })),
        Decl::TypeAlias(_) => {
            unreachable!("RFC-0160 type aliases are expanded before typechecking")
        }
        Decl::Stmt(stmt) => Ok(TypedDecl::Stmt(Box::new(construct_stmt(stmt, ctx)?))),
    }
}

#[allow(clippy::too_many_lines)]
pub(super) fn construct_fun_decl(
    fun: &FunDecl,
    ctx: &mut ConstructCtx,
) -> Result<TypedDecl, MetelError> {
    // Native functions carry no Metel body; lower the host binding to a NativeKey
    // and emit a Native body for the evaluator to dispatch (METEL-182).
    if let Some(binding) = &fun.native {
        let key = crate::native_keys::NativeKey::from_path(&binding.key_path).ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0003,
                format!(
                    "unknown native binding `@{}`; no host implementation is registered for it",
                    binding.key_path.join(".")
                ),
                &binding.span,
            )
        })?;
        // Overloaded native definitions (std::core's assert pair) carry their
        // overload SymbolId like any overloaded decl.
        let symbol_id =
            super::super::overload::entry_for_decl(ctx.overloads, fun).map(|e| e.symbol_id);
        return Ok(TypedDecl::Fun(TypedFunDecl {
            name: fun.name.clone(),
            generics: fun.generics.clone(),
            params: fun.params.clone(),
            param_ids: ctx.param_local_ids(&fun.params),
            return_type: fun.return_type.clone(),
            body: FunBody::Native(key),
            symbol_id,
            def_id: None,
            span: fun.span.clone(),
        }));
    }

    // Overloaded definitions (METEL-180) never enter the name-keyed scheme env;
    // their concrete signature comes straight from the overload entry, and the
    // typed decl carries the entry's SymbolId for the evaluator's registry.
    let overload_entry = super::super::overload::entry_for_decl(ctx.overloads, fun).cloned();
    let scheme = match &overload_entry {
        Some(entry) => TypeScheme {
            quantified_vars: vec![],
            param_names: vec![],
            bounds: vec![],
            neg_bounds: vec![],
            record_kinds: vec![],
            assoc_projections: vec![],
            assoc_eq_constraints: vec![],
            opaque_returns: vec![],
            ty: InferType::fun(
                entry
                    .params
                    .iter()
                    .map(|t| InferType::Concrete(t.clone()))
                    .collect(),
                InferType::Concrete(entry.ret.clone()),
            ),
        },
        None => ctx
            .scheme_env
            .get(fun.name.as_str())
            .ok_or_else(|| MetelError::internal(format!("missing type for fn `{}`", fun.name)))?
            .clone(),
    };

    let body = if scheme.quantified_vars.is_empty() {
        let (param_types, ret_ty) = match ctx.subst.apply(&scheme.ty) {
            InferType::Fun(params, ret, ..) => {
                let pts = params
                    .iter()
                    .map(|p| infer_type_to_type(p, &fun.span))
                    .collect::<Result<Vec<_>, _>>()?;
                let rt = infer_type_to_type(&ret, &fun.span).ok();
                (pts, rt)
            }
            _ => {
                return Err(MetelError::internal(format!(
                    "expected Fun type for `{}`",
                    fun.name
                )))
            }
        };
        ctx.push_scope();
        let saved_flow = ctx.flow_enter_body();
        for (param, ty) in fun.params.iter().zip(param_types.iter()) {
            ctx.bind(&param.name, ty.clone());
        }
        let saved_return = ctx.push_return_type(ret_ty.clone());
        let typed_block = construct_block(&fun.body, ret_ty.as_ref(), ctx)?;
        ctx.pop_return_type(saved_return);
        ctx.flow_exit_body(saved_flow);
        ctx.pop_scope();
        // RFC-0078 §6: a function declared `-> !` must diverge on every path.
        if matches!(ret_ty, Some(Type::Never)) && !fun_body_diverges(&typed_block) {
            return Err(MetelError::type_error(
                TypeErrorCode::T0016,
                format!(
                    "function `{}` is declared `-> !` but does not diverge on all paths",
                    fun.name
                ),
                &fun.span,
            ));
        }
        FunBody::Typed(typed_block)
    } else if scheme.quantified_vars.iter().all(|qvar| {
        scheme.opaque_returns.iter().any(|opaque| {
            if let Some((_, _concrete_ty)) = opaque {
                // Check if this quantified var is bound to a concrete type in opaque_returns
                // We need to find if there's an opaque entry that covers this quantified var position
                if let Some(idx) = scheme.quantified_vars.iter().position(|v| v == qvar) {
                    scheme.opaque_returns.get(idx).is_some()
                } else {
                    false
                }
            } else {
                false
            }
        })
    }) {
        // All quantified vars are accounted for by opaque_returns - eager build
        let mut subst = Substitution::new();
        for (i, qvar) in scheme.quantified_vars.iter().enumerate() {
            if let Some(Some((_, concrete_ty))) = scheme.opaque_returns.get(i) {
                subst.bind(*qvar, InferType::Concrete(concrete_ty.clone()));
            }
        }
        let substituted_ty = subst.apply(&scheme.ty);
        let (param_types, ret_ty) = match substituted_ty {
            InferType::Fun(params, ret, ..) => {
                let pts = params
                    .iter()
                    .map(|p| infer_type_to_type(p, &fun.span))
                    .collect::<Result<Vec<_>, _>>()?;
                let rt = infer_type_to_type(&ret, &fun.span).ok();
                (pts, rt)
            }
            _ => {
                return Err(MetelError::internal(format!(
                    "expected Fun type for `{}`",
                    fun.name
                )))
            }
        };
        ctx.push_scope();
        let saved_flow = ctx.flow_enter_body();
        for (param, ty) in fun.params.iter().zip(param_types.iter()) {
            ctx.bind(&param.name, ty.clone());
        }
        let saved_return = ctx.push_return_type(ret_ty.clone());
        let typed_block = construct_block(&fun.body, ret_ty.as_ref(), ctx)?;
        ctx.pop_return_type(saved_return);
        ctx.flow_exit_body(saved_flow);
        ctx.pop_scope();
        // RFC-0078 §6: a function declared `-> !` must diverge on every path.
        if matches!(ret_ty, Some(Type::Never)) && !fun_body_diverges(&typed_block) {
            return Err(MetelError::type_error(
                TypeErrorCode::T0016,
                format!(
                    "function `{}` is declared `-> !` but does not diverge on all paths",
                    fun.name
                ),
                &fun.span,
            ));
        }
        FunBody::Typed(typed_block)
    } else {
        FunBody::Generic(fun.body.clone())
    };

    Ok(TypedDecl::Fun(TypedFunDecl {
        name: fun.name.clone(),
        generics: fun.generics.clone(),
        params: fun.params.clone(),
        param_ids: ctx.param_local_ids(&fun.params),
        return_type: fun.return_type.clone(),
        body,
        symbol_id: overload_entry.map(|e| e.symbol_id),
        def_id: None,
        span: fun.span.clone(),
    }))
}

/// Reject a `Drop` impl that supplies a destructor body, while still allowing a
/// type to *declare* itself `Drop`.
///
/// RFC-0071 §9c gates #290 (the `Drop` aspect) on #261 (destructor invocation):
/// between them, a `drop` body compiles and never runs — "a feature that looks
/// functional and silently does nothing". This guard is tracked by #292; it
/// must remain until #261 lands, so that state cannot ship (#345).
///
/// The rejection is narrower than "reject `Drop` impls", deliberately. Declaring
/// `Drop` has type-level effects that are implemented and correct *today*, and
/// none of them involve the destructor running: `Copy`/`Drop` exclusion,
/// `T: !Drop` bounds, the ban on `Drop` for anonymous records, and the move
/// checker's refusal to partially move a `Drop` value. An empty `fun drop(&var
/// self) {}` claims nothing that is not delivered. A body with statements in it does.
pub(super) fn reject_inert_destructor(
    ib: &ImplBlock,
    ctx: &ConstructCtx,
) -> Result<(), MetelError> {
    if ib.polarity != crate::ast::Polarity::Positive {
        return Ok(());
    }
    // Match the stdlib aspect by its declaring module, not by name, so a user
    // module's own unrelated `Drop` aspect is unaffected — the same discipline
    // `coherence.rs` uses for the `Copy`/`Drop` exclusion.
    let Some(aspect_name) = ib.aspect_name.as_deref() else {
        return Ok(());
    };
    if aspect_name != "Drop" {
        return Ok(());
    }
    let is_std_core_drop = ctx
        .registry
        .aspect_declaring_module_in(ctx.current_module, aspect_name)
        .is_some_and(|module| module.as_slice() == ["std".to_string(), "core".to_string()]);
    if !is_std_core_drop {
        return Ok(());
    }

    for method in &ib.methods {
        if method.name != "drop" {
            continue;
        }
        let body_is_empty = method.body.stmts.is_empty() && method.body.tail.is_none();
        if body_is_empty {
            continue;
        }
        return Err(MetelError::type_error(
            TypeErrorCode::T0001,
            "a `drop` body cannot run yet: destructor invocation is not implemented \
             (metel-core#261), so this cleanup would silently never happen. Leave the \
             body empty to declare the type `Drop` for its type-level effects — \
             `Copy` exclusion, `!Drop` bounds, and the partial-move ban — or move the \
             cleanup into an ordinary method the caller invokes"
                .to_string(),
            &method.span,
        ));
    }
    Ok(())
}

pub(super) fn construct_impl_decl(
    ib: &ImplBlock,
    ctx: &mut ConstructCtx,
) -> Result<TypedDecl, MetelError> {
    reject_inert_destructor(ib, ctx)?;
    // An impl block that declares its own generics (RFC-0036 conditional impls,
    // RFC-0061 structural blanket impls: `impl<T: Bound> Aspect for Type<T>` /
    // `impl<T: Display> Display for T[]`) can't have its methods eagerly constructed
    // against a concrete `self` type here — same reason generic-struct methods
    // already defer to `FunBody::Generic` below. Real bound-satisfaction checking at
    // each instantiation is issue #241/#245's job, not this one's; this only needs to
    // not crash on construction.
    // Structural targets (`T[]`, tuples, `fun` types, anonymous records) have no
    // nominal name to key registry lookups on, so they key on the empty string
    // and their methods take the deferred path below. This used to be reachable
    // only when the impl also declared generics; a structural target *without*
    // them fell through to an internal error (metel-core#581).
    super::super::reject_unregisterable_impl_target(ib)?;
    let defers_bodies = super::super::impl_defers_method_bodies(ib);
    let target_name = super::super::impl_target_head(&ib.target_type)
        .map(ToString::to_string)
        .unwrap_or_default();
    let mut methods = ib
        .methods
        .iter()
        .map(|m| construct_impl_method(m, &target_name, defers_bodies, ctx))
        .collect::<Result<Vec<_>, _>>()?;
    // Default aspect-method bodies are constructed eagerly against a concrete `self`
    // type today (see `construct_default_aspect_method`) — not sound to do against a
    // conditional/structural target without knowing the concrete instantiation.
    // Skipped for now when the impl has its own generics; issue #241/#245's job to
    // do this properly once bound-satisfaction checking exists.
    //
    // Also skipped for a negative impl (RFC-0081, issue #264): `impl !Aspect for
    // Type {}` declares non-implementation, so it must not inherit the aspect's
    // default method bodies — that would make the type appear to implement the
    // aspect via inherited defaults, the opposite of what a negative impl means.
    if !defers_bodies && ib.polarity == crate::ast::Polarity::Positive {
        methods.extend(construct_default_aspect_methods(ib, &target_name, ctx)?);
    }

    // Resolve aspect_id from the symbol table when available.
    let aspect_id = ib.aspect_name.as_deref().and_then(|aspect_name| {
        let declaring_module = ctx
            .registry
            .aspect_declaring_module_in(ctx.current_module, aspect_name)?;
        ctx.symbols?
            .get(&(declaring_module.clone(), aspect_name.to_string()))
            .copied()
    });

    Ok(TypedDecl::Impl(TypedImplBlock {
        polarity: ib.polarity,
        generics: ib.generics.clone(),
        aspect_name: ib.aspect_name.clone(),
        aspect_id,
        target_type_id: ctx.type_symbol_id(&target_name),
        aspect_type_args: ib.aspect_type_args.clone(),
        target_type: ib.target_type.clone(),
        methods,
        span: ib.span.clone(),
    }))
}

pub(super) fn construct_impl_method(
    method: &FunDecl,
    target_name: &str,
    impl_has_generics: bool,
    ctx: &mut ConstructCtx,
) -> Result<TypedFunDecl, MetelError> {
    // Native method: no Metel body; lower the host binding to a NativeKey
    // (METEL-181). Dispatched at runtime by the evaluator's impl-method path.
    if let Some(binding) = &method.native {
        let key = crate::native_keys::NativeKey::from_path(&binding.key_path).ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0003,
                format!(
                    "unknown native binding `@{}`; no host implementation is registered for it",
                    binding.key_path.join(".")
                ),
                &binding.span,
            )
        })?;
        return Ok(method_fun_decl(
            method,
            ctx.param_local_ids(&method.params),
            FunBody::Native(key),
        ));
    }

    // Methods on a generic struct OR generic enum have T-typed params that can't be
    // resolved to concrete types in Pass 2 without call-site type args. Store the body
    // as Generic (untyped) so the evaluator constructs it at runtime — same pattern as
    // top-level generic fns. (Using raw_struct_type_params would miss enums, whose
    // methods would then be eagerly constructed here and fail on e.g. `match self`.)
    // Also deferred whenever the *impl block itself* declares generics (RFC-0036/
    // RFC-0061) — `target_name` may not even name a real struct/enum in that case
    // (RFC-0061's structural targets), so `struct_generic_names_for` can't be relied
    // on to catch it. And deferred whenever the *method itself* declares its own
    // generics (RFC-0040 §7, issue #746) -- a method on an otherwise-concrete target
    // (`extend Foo { fun describe<U: Aspect>(...) }`) is just as unresolvable here
    // without call-site type args as an impl-level generic is; missing this case used
    // to eagerly resolve `U` as a literal, nonexistent named type instead of deferring.
    let is_generic_target = impl_has_generics
        || !method.generics.is_empty()
        || ctx
            .registry
            .struct_generic_names_for(ctx.current_module, target_name)
            .is_some_and(|names| !names.is_empty());
    if is_generic_target {
        return Ok(method_fun_decl(
            method,
            ctx.param_local_ids(&method.params),
            FunBody::Generic(method.body.clone()),
        ));
    }

    let self_ty = super::super::inference::primitive_type_from_name(target_name)
        .unwrap_or_else(|| Type::Named(target_name.to_string(), vec![]));
    // #774: `type_expr_to_infer_with_self` resolves `Self` but carries no
    // `AssocResolveCtx` (no registry access), which `Self.{ field }` needs to look
    // up the target struct's actual fields -- mirrors the same fix in inference.rs's
    // own `infer_impl_method`, this pass's Pass-1 counterpart.
    let empty_generics: HashMap<String, TypeVar> = HashMap::new();
    let assoc_ctx = AssocResolveCtx {
        registry: ctx.registry,
        current_module: ctx.current_module,
        current_aspect: None,
    };
    let te_to_infer = |te: &TypeExpr| {
        type_expr_to_infer_with_assoc_ctx(te, &empty_generics, Some(target_name), &assoc_ctx)
    };
    let param_types: Vec<Type> = method
        .params
        .iter()
        .map(|p| {
            if p.name == "self" {
                Ok(self_ty.clone())
            } else {
                p.type_ann.as_ref().map_or_else(
                    || {
                        Err(MetelError::type_error(
                            TypeErrorCode::T0002,
                            format!("parameter `{}` needs a type annotation", p.name),
                            &p.span,
                        ))
                    },
                    |ann| resolved_to_type(&te_to_infer(ann), ctx.subst, &p.span),
                )
            }
        })
        .collect::<Result<_, _>>()?;
    let ret_ty = method
        .return_type
        .as_ref()
        .map(|ann| resolved_to_type(&te_to_infer(ann), ctx.subst, &method.span))
        .transpose()?;
    ctx.push_scope();
    let saved_flow = ctx.flow_enter_body();
    for (p, ty) in method.params.iter().zip(param_types.iter()) {
        ctx.bind(&p.name, ty.clone());
    }
    let saved_return = ctx.push_return_type(ret_ty.clone());
    let saved_self = ctx.push_self_type_name(Some(target_name.to_string()));
    let typed_block = construct_block(&method.body, ret_ty.as_ref(), ctx)?;
    ctx.pop_self_type_name(saved_self);
    ctx.pop_return_type(saved_return);
    ctx.flow_exit_body(saved_flow);
    ctx.pop_scope();
    Ok(method_fun_decl(
        method,
        ctx.param_local_ids(&method.params),
        FunBody::Typed(typed_block),
    ))
}

// Synthesize typed method bodies for aspect methods not provided by this impl block.
// Bodies come from the aspect's default_body; Self is substituted with the concrete target type.
// The evaluator never needs to know about defaults — see ADR-0034.
pub(super) fn construct_default_aspect_methods(
    ib: &ImplBlock,
    target_name: &str,
    ctx: &mut ConstructCtx,
) -> Result<Vec<TypedFunDecl>, MetelError> {
    let Some(aspect_name) = &ib.aspect_name else {
        return Ok(vec![]);
    };
    let Some(methods) = ctx
        .registry
        .aspect_method_defs_in(ctx.current_module, aspect_name)
        .cloned()
    else {
        return Ok(vec![]);
    };
    let provided: std::collections::HashSet<&str> =
        ib.methods.iter().map(|m| m.name.as_str()).collect();

    methods
        .iter()
        .filter(|method| method.default_body.is_some() && !provided.contains(method.name.as_str()))
        .map(|method| construct_default_aspect_method(method, target_name, ctx))
        .collect()
}

pub(super) fn construct_default_aspect_method(
    method: &AspectMethod,
    target_name: &str,
    ctx: &mut ConstructCtx,
) -> Result<TypedFunDecl, MetelError> {
    let self_ty = super::super::inference::primitive_type_from_name(target_name)
        .unwrap_or_else(|| Type::Named(target_name.to_string(), vec![]));
    // #774: `type_expr_to_infer_with_self` resolves `Self` but carries no
    // `AssocResolveCtx` (no registry access), which `Self.{ field }` needs to look
    // up the target struct's actual fields -- mirrors the same fix in inference.rs's
    // own `infer_impl_method`, this pass's Pass-1 counterpart.
    let empty_generics: HashMap<String, TypeVar> = HashMap::new();
    let assoc_ctx = AssocResolveCtx {
        registry: ctx.registry,
        current_module: ctx.current_module,
        current_aspect: None,
    };
    let te_to_infer = |te: &TypeExpr| {
        type_expr_to_infer_with_assoc_ctx(te, &empty_generics, Some(target_name), &assoc_ctx)
    };
    let param_types: Vec<Type> = method
        .params
        .iter()
        .map(|p| {
            if p.name == "self" {
                Ok(self_ty.clone())
            } else {
                p.type_ann.as_ref().map_or_else(
                    || {
                        Err(MetelError::type_error(
                            TypeErrorCode::T0002,
                            format!("parameter `{}` needs a type annotation", p.name),
                            &p.span,
                        ))
                    },
                    |ann| resolved_to_type(&te_to_infer(ann), ctx.subst, &p.span),
                )
            }
        })
        .collect::<Result<_, _>>()?;
    let ret_ty = method
        .return_type
        .as_ref()
        .map(|ann| resolved_to_type(&te_to_infer(ann), ctx.subst, &method.span))
        .transpose()?;
    let body = method
        .default_body
        .as_ref()
        .ok_or_else(|| MetelError::internal("missing aspect default body"))?;
    ctx.push_scope();
    for (p, ty) in method.params.iter().zip(param_types.iter()) {
        ctx.bind(&p.name, ty.clone());
    }
    let saved_return = ctx.push_return_type(ret_ty.clone());
    let saved_self = ctx.push_self_type_name(Some(target_name.to_string()));
    let typed_block = construct_block(body, ret_ty.as_ref(), ctx)?;
    ctx.pop_self_type_name(saved_self);
    ctx.pop_return_type(saved_return);
    ctx.pop_scope();
    Ok(TypedFunDecl {
        name: method.name.clone(),
        generics: method.generics.clone(),
        param_ids: ctx.param_local_ids(&method.params),
        params: method.params.clone(),
        return_type: method.return_type.clone(),
        body: FunBody::Typed(typed_block),
        symbol_id: None,
        def_id: None,
        span: method.span.clone(),
    })
}
