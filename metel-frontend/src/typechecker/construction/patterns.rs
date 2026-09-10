use super::{
    check_type_does_not_satisfy_bound, check_type_satisfies_bounds, construct_block,
    construct_expr, infer_type_to_type, peel_type_references, type_to_infer, unify, ConstructCtx,
    EnumInfo, HashMap, InferType, Literal, MatchExpr, MetelError, Pattern, Span, Substitution,
    Type, TypeErrorCode, TypedBlock, TypedDecl, TypedExpr, TypedMatchArm, TypedMatchExpr,
    TypedStmt, VariantInfo,
};

pub(super) fn builtin_pattern_method_expr(
    receiver: TypedExpr,
    method: &str,
    args: Vec<TypedExpr>,
    span: &Span,
) -> Option<Result<TypedExpr, MetelError>> {
    if matches!(
        peel_type_references(receiver.ty()),
        Type::Array(_) | Type::SizedArray(_, _)
    ) && method == "len"
        && args.is_empty()
    {
        return Some(Ok(TypedExpr::MethodCall {
            receiver: Box::new(receiver),
            method: method.to_string(),
            args,
            ty: Type::I64,
            dispatch: crate::typed_ast::MethodDispatch::Dynamic,
            span: span.clone(),
        }));
    }

    None
}

/// Issue #229: `break` can now be a block's own tail expression (e.g.
/// `loop { if (c) { break 5 } }`, no longer requiring `break 5;` as a
/// statement), so the tail must be checked too, not just `block.stmts`.
pub(super) fn find_loop_break_type(block: &TypedBlock) -> Option<Type> {
    if let Some(tail) = &block.tail {
        if let Some(ty) = find_break_in_expr(tail) {
            return Some(ty);
        }
    }
    block.stmts.iter().find_map(find_break_in_decl)
}

pub(super) fn find_break_in_decl(decl: &TypedDecl) -> Option<Type> {
    match decl {
        TypedDecl::Stmt(stmt) => find_break_in_stmt(stmt),
        _ => None,
    }
}

pub(super) fn find_break_in_stmt(stmt: &TypedStmt) -> Option<Type> {
    match stmt {
        TypedStmt::Expr(expr) => find_break_in_expr(expr),
        // break inside a nested while/for/for-in exits that loop, not the outer loop
        TypedStmt::While(_) | TypedStmt::For(_) | TypedStmt::ForIn(_) => None,
    }
}

pub(super) fn find_break_in_expr(expr: &TypedExpr) -> Option<Type> {
    match expr {
        TypedExpr::Break(b) => Some(b.value.as_ref().map_or(Type::Unit, |v| v.ty().clone())),
        TypedExpr::If {
            then_branch,
            else_branch,
            ..
        } => find_loop_break_type(then_branch)
            .or_else(|| else_branch.as_ref().and_then(find_loop_break_type)),
        // A `break` written as a match-arm body -- same shape as an `if`
        // branch, previously never checked (a pre-existing gap, fixed here
        // since #229 unifies match-arm bodies through the same mechanism).
        TypedExpr::Match(m) => m.arms.iter().find_map(|a| find_loop_break_type(&a.body)),
        // Everything else: a nested loop's own `break` exits that inner loop,
        // not the outer one; a closure's `break` doesn't escape to the
        // enclosing loop either. Both fall out of the same `None` as any
        // other non-propagating expression kind.
        _ => None,
    }
}

pub(super) fn construct_match(
    m: &MatchExpr,
    expected_ty: Option<&Type>,
    ctx: &mut ConstructCtx,
) -> Result<TypedExpr, MetelError> {
    let scrutinee = construct_expr(&m.scrutinee, None, ctx)?;
    // RFC-0108: peel `&T`/`&mut T` layers so a reference-typed scrutinee matches
    // against `T`'s own patterns, using construction's own existing
    // `peel_type_references` (already used for method/field receivers). Only the
    // local copy used for pattern resolution and exhaustiveness is peeled — the
    // typed scrutinee expression's own recorded type (`scrutinee.ty()`) is untouched.
    let scrutinee_ty = peel_type_references(scrutinee.ty()).clone();
    // RFC-0107: bare variant patterns (`Red`, `Some { value }`) resolve against the
    // scrutinee's own enum. Compute the enum's variant list once from the (already
    // reference-peeled, RFC-0108) scrutinee type; `None` here means the scrutinee
    // isn't a known enum, so patterns are left exactly as written.
    let scrutinee_variants: Option<(String, Vec<(String, bool)>)> = match &scrutinee_ty {
        Type::Named(enum_name, _) => ctx.registry.enum_info(enum_name).map(|info| {
            (
                enum_name.clone(),
                info.variants
                    .iter()
                    .map(|v| (v.name.clone(), v.fields.is_empty()))
                    .collect(),
            )
        }),
        _ => None,
    };
    // RFC-0032 §4/§5, RFC-0034 §5: same idea, for a struct rather than an enum --
    // Pass 2's own counterpart of `infer_match`'s parallel resolution (inference.rs),
    // since construction re-derives everything from the AST rather than reusing
    // Pass 1's rewritten patterns.
    let scrutinee_struct_name: Option<String> = match &scrutinee_ty {
        Type::Named(name, _)
            if ctx
                .registry
                .struct_fields(ctx.current_module, name)
                .is_some() =>
        {
            Some(name.clone())
        }
        _ => None,
    };
    let mut typed_arms = vec![];
    // metel-core#958: fork each arm's row-narrowing move state from the state
    // before the `match` and join (union) afterward — Pass 2's counterpart of
    // `infer_match`'s per-arm fork/join, so the residual type this pass stamps
    // on later arms and on code after the `match` matches Pass 1.
    let entry_flow = ctx.flow.clone();
    let mut joined_flow = entry_flow.clone();
    let mut any_arm = false;
    for arm in &m.arms {
        let pattern = if let Some((enum_name, variants)) = &scrutinee_variants {
            resolve_bare_variant(&arm.pattern, enum_name, variants)
        } else if let Some(struct_name) = &scrutinee_struct_name {
            resolve_struct_pattern(&arm.pattern, struct_name)
        } else {
            arm.pattern.clone()
        };
        ctx.flow = entry_flow.clone();
        ctx.push_scope();
        construct_pattern_bindings(&pattern, &scrutinee_ty, ctx)?;
        let guard = match &arm.guard {
            Some(g) => Some(construct_expr(g, None, ctx)?),
            None => None,
        };
        let body = construct_block(&arm.body, expected_ty, ctx)?;
        typed_arms.push(TypedMatchArm {
            pattern,
            guard,
            body,
            span: arm.span.clone(),
        });
        ctx.pop_scope();
        joined_flow.union_from(&ctx.flow);
        any_arm = true;
    }
    if any_arm {
        ctx.flow = joined_flow;
    }
    check_match_exhaustiveness(
        &typed_arms,
        &scrutinee_ty,
        ctx.registry.raw_enum_env(),
        &m.span,
    )?;
    // RFC-0078 §3.4: if all arms diverge, the match's type is `!`. An empty match
    // (only legal on a `!` scrutinee, per the exhaustiveness check above) is
    // vacuously `!` too — it can never actually be entered.
    let expr_type = if typed_arms.is_empty() {
        Type::Never
    } else {
        merge_branch_types(
            &typed_arms
                .iter()
                .map(|a| block_result_type(&a.body))
                .collect::<Vec<_>>(),
        )
    };
    Ok(TypedExpr::Match(TypedMatchExpr {
        scrutinee: Box::new(scrutinee),
        arms: typed_arms,
        expr_type,
        span: m.span.clone(),
    }))
}

/// RFC-0078: a block's own type when used as an expression (`if`/`match` branch
/// body). The tail expression's type if there is one; else `!` if the block's
/// last statement is a `Never`-typed expression statement (`return`/`break`/
/// `continue`, or any other diverging expression like `panic(msg)`) — mirroring
/// pass 1's tail-less handling (`infer_block`, `src/typechecker/inference.rs`);
/// else `Unit` for an ordinary non-diverging statement-only block. Since issue
/// #229, `return`/`break`/`continue` are ordinary `Expr`s reached only through
/// `TypedStmt::Expr`/a tail expression — the type check is generic rather than
/// naming those variants specifically, which also means a bare `panic(msg);`
/// (semicolon, not tail position) is correctly recognized as diverging too.
pub(super) fn block_result_type(block: &TypedBlock) -> Type {
    if let Some(tail) = &block.tail {
        return tail.ty().clone();
    }
    match block.stmts.last() {
        Some(TypedDecl::Stmt(stmt)) => match &**stmt {
            TypedStmt::Expr(e) if *e.ty() == Type::Never => Type::Never,
            _ => Type::Unit,
        },
        _ => Type::Unit,
    }
}

/// RFC-0078 §6: does a function body genuinely diverge (never returns from the
/// function at all), as opposed to merely having "type `!`" as a block
/// expression? These differ precisely for `return`: `block_result_type` above
/// correctly treats a `return`-terminated block as `!`-typed for match/if
/// arm-merging purposes (code after it is unreachable, sound at any type) — but
/// a *function* ending in a reachable, ordinary `return 5` does not diverge; it
/// returns, which is exactly what `-> !` forbids. `return <expr>` only counts
/// as divergence here if `<expr>` itself never produces a value (e.g.
/// `return panic(msg)`) — checked wherever `Return` appears, since issue #229
/// lets it be either the block's tail expression or (wrapped in
/// `TypedStmt::Expr`) an ordinary statement.
pub(super) fn fun_body_diverges(block: &TypedBlock) -> bool {
    fn is_divergent_return(e: &TypedExpr) -> bool {
        match e {
            TypedExpr::Return(r) => r.value.as_ref().is_some_and(|v| *v.ty() == Type::Never),
            other => *other.ty() == Type::Never,
        }
    }
    if let Some(tail) = &block.tail {
        return is_divergent_return(tail);
    }
    match block.stmts.last() {
        Some(TypedDecl::Stmt(stmt)) => match &**stmt {
            TypedStmt::Expr(e) => is_divergent_return(e),
            _ => false,
        },
        _ => false,
    }
}

/// RFC-0078 §3.4: merge sibling branch/arm types — the first non-`!` type, or `!`
/// if every branch diverges. A diverging branch imposes no constraint of its own
/// (`! <: T` for all `T`), so it must never be picked over a concretely-typed
/// sibling regardless of source order.
pub(super) fn merge_branch_types(types: &[Type]) -> Type {
    types
        .iter()
        .find(|t| **t != Type::Never)
        .cloned()
        .unwrap_or(Type::Never)
}

/// Map `enum_info`'s type params to the scrutinee's concrete type args, the same
/// substitution `bind_enum_variant_fields` builds for pattern binding — needed here
/// to resolve a variant's field types for the current instantiation (e.g. whether
/// `Result<T, !>`'s `Err { error: E }` is uninhabited depends on what `E` actually is).
pub(super) fn enum_variant_type_param_remap(
    enum_info: &EnumInfo,
    type_args: &[Type],
) -> Substitution {
    let mut remap = Substitution::new();
    for (&tp, arg_ty) in enum_info.type_params.iter().zip(type_args.iter()) {
        remap.bind(tp, InferType::Concrete(arg_ty.clone()));
    }
    remap
}

/// RFC-0078 §3.2: a variant is uninhabited if any of its fields' (substituted)
/// type is `!` — no value of that variant can ever be constructed, since a struct
/// literal needs a value for every field and none exists of type `!`. A zero-field
/// variant is always inhabited (e.g. `Perhaps::None`).
pub(super) fn is_variant_uninhabited(
    variant: &VariantInfo,
    remap: &Substitution,
    span: &Span,
) -> bool {
    variant
        .fields
        .iter()
        .any(|f| infer_type_to_type(&remap.apply(&f.ty), span).is_ok_and(|t| t == Type::Never))
}

pub(super) fn check_match_exhaustiveness(
    arms: &[TypedMatchArm],
    scrutinee_ty: &Type,
    enum_env: &HashMap<String, EnumInfo>,
    span: &Span,
) -> Result<(), MetelError> {
    if arms
        .iter()
        .any(|a| a.guard.is_none() && is_catch_all_pattern(&a.pattern))
    {
        return Ok(());
    }
    let exhaustive = match scrutinee_ty {
        Type::Boolean => {
            let has_true = arms
                .iter()
                .any(|a| a.guard.is_none() && is_bool_literal_pattern(&a.pattern, true));
            let has_false = arms
                .iter()
                .any(|a| a.guard.is_none() && is_bool_literal_pattern(&a.pattern, false));
            has_true && has_false
        }
        // RFC-0078 §3.2: a variant whose payload is uninhabited (some field's type
        // is `!`) can never be constructed, so it doesn't need a covering arm to be
        // exhaustive. This subsumes `Result<T, !>` (§4.1) as the general rule's
        // special case, rather than hardcoding `Result`/`Perhaps` separately —
        // both are ordinary entries in `enum_env` like any user enum.
        Type::Named(name, type_args) => {
            if let Some(enum_info) = enum_env.get(name.as_str()) {
                let remap = enum_variant_type_param_remap(enum_info, type_args);
                enum_info.variants.iter().all(|v| {
                    is_variant_uninhabited(v, &remap, span)
                        || arms.iter().any(|a| {
                            a.guard.is_none() && pattern_covers_variant(&a.pattern, name, &v.name)
                        })
                })
            } else {
                false
            }
        }
        // Never is uninhabited — a match on it is vacuously exhaustive.
        Type::Never => true,
        // SizedArray [T; N]: exhaustive if there is an arm with an exact N-element array
        // pattern (each element itself exhaustive) or a rest pattern.
        Type::SizedArray(_, n) => arms.iter().any(|a| {
            a.guard.is_none()
                && match &a.pattern {
                    Pattern::Array {
                        elems,
                        rest: Some(_),
                        ..
                    } => elems.iter().all(is_catch_all_pattern),
                    Pattern::Array {
                        elems, rest: None, ..
                    } => elems.len() as u64 == *n && elems.iter().all(is_catch_all_pattern),
                    _ => false,
                }
        }),
        // Int, Float, Str, Tuple, Array, Fun — value-infinite; only a catch-all suffices.
        _ => false,
    };
    if !exhaustive {
        return Err(MetelError::type_error(
            TypeErrorCode::T0008,
            "non-exhaustive match: not all cases are covered".to_string(),
            span,
        ));
    }
    Ok(())
}

pub(super) fn is_catch_all_pattern(pattern: &Pattern) -> bool {
    match pattern {
        // A struct pattern, like `Record`, is irrefutable by construction: field
        // sub-patterns here are always plain bindings (no `field: subpattern` form),
        // and `infer_struct_pattern` already requires either every field named or a
        // trailing `..` (RFC-0032 §5) before this point is ever reached -- so an
        // unguarded arm with one always covers the entire struct type, regardless of
        // which fields it names.
        Pattern::Wildcard(_)
        | Pattern::Binding(_, _)
        | Pattern::Record { .. }
        | Pattern::Struct { .. } => true,
        // A tuple pattern is irrefutable when every element is also irrefutable.
        Pattern::Tuple(pats, _) => pats.iter().all(is_catch_all_pattern),
        // An array pattern with a rest binding is irrefutable if all explicit elems are.
        Pattern::Array {
            elems,
            rest: Some(_),
            ..
        } => elems.iter().all(is_catch_all_pattern),
        _ => false,
    }
}

pub(super) fn is_bool_literal_pattern(pattern: &Pattern, expected: bool) -> bool {
    matches!(pattern, Pattern::Literal(Literal::Boolean(b), _) if *b == expected)
}

/// Returns true if `pattern` (unguarded) covers variant `variant_name` of enum `enum_name`.
pub(super) fn pattern_covers_variant(
    pattern: &Pattern,
    enum_name: &str,
    variant_name: &str,
) -> bool {
    match pattern {
        Pattern::EnumVariant { path, .. } => {
            path.first().map(String::as_str) == Some(enum_name)
                && path.get(1).map(String::as_str) == Some(variant_name)
        }
        _ => false,
    }
}

/// RFC-0107: rewrite a bare variant match-arm pattern into its fully-qualified form
/// when it resolves against the scrutinee's enum. `variants` is `(name, is_fieldless)`
/// for each variant of the scrutinee enum `enum_name`. A bare no-field variant is
/// parsed as a `Binding` (`Red`); a bare fieldful variant is parsed as a one-segment
/// `EnumVariant` (`Some { value }`). Anything else — including a `Binding` that names
/// no variant, which stays an ordinary binding — is returned unchanged. Resolution is
/// top-level only: nested bare variants inside a tuple/array pattern are out of scope
/// (they would resolve against a nested field type, not the scrutinee enum). Once
/// rewritten, every downstream consumer sees an ordinary two-segment `EnumVariant`,
/// so exhaustiveness, binding, and runtime matching need no changes.
pub(in crate::typechecker) fn resolve_bare_variant(
    pattern: &Pattern,
    enum_name: &str,
    variants: &[(String, bool)],
) -> Pattern {
    match pattern {
        Pattern::Binding(name, span)
            if variants
                .iter()
                .any(|(vn, fieldless)| vn == name && *fieldless) =>
        {
            Pattern::EnumVariant {
                path: vec![enum_name.to_string(), name.clone()],
                fields: vec![],
                rest: false,
                span: span.clone(),
            }
        }
        Pattern::EnumVariant {
            path,
            fields,
            rest,
            span,
        } if path.len() == 1 && variants.iter().any(|(vn, _)| vn == &path[0]) => {
            Pattern::EnumVariant {
                path: vec![enum_name.to_string(), path[0].clone()],
                fields: fields.clone(),
                rest: *rest,
                span: span.clone(),
            }
        }
        _ => pattern.clone(),
    }
}

/// RFC-0032 §4/§5, RFC-0034 §5: rewrite a one-segment `EnumVariant` pattern into a
/// `Struct` pattern when it names `struct_name`, the scrutinee's own struct -- the
/// struct-pattern counterpart of `resolve_bare_variant` above. Shares that function's
/// grammar ambiguity (`Point { x, y }` parses as a one-segment `EnumVariant` regardless
/// of whether `Point` is an enum or a struct) and its resolution strategy (let the
/// scrutinee's type decide, once it's known). Once rewritten, every downstream
/// consumer sees a `Pattern::Struct`, so field binding, visibility checking, and
/// runtime matching need no further disambiguation.
pub(in crate::typechecker) fn resolve_struct_pattern(
    pattern: &Pattern,
    struct_name: &str,
) -> Pattern {
    match pattern {
        Pattern::EnumVariant {
            path,
            fields,
            rest,
            span,
        } if path.len() == 1 && path[0] == struct_name => Pattern::Struct {
            name: struct_name.to_string(),
            fields: fields.clone(),
            rest: *rest,
            span: span.clone(),
        },
        _ => pattern.clone(),
    }
}

pub(super) fn construct_pattern_bindings(
    pattern: &Pattern,
    scrutinee_ty: &Type,
    ctx: &mut ConstructCtx,
) -> Result<(), MetelError> {
    match pattern {
        Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
        Pattern::Binding(name, _) => {
            ctx.bind(name, scrutinee_ty.clone());
        }
        Pattern::Tuple(pats, _) => {
            let elems = match scrutinee_ty {
                Type::Tuple(ts) => ts.clone(),
                _ => return Err(MetelError::internal("tuple pattern on non-tuple")),
            };
            for (pat, elem_ty) in pats.iter().zip(elems.iter()) {
                construct_pattern_bindings(pat, elem_ty, ctx)?;
            }
        }
        Pattern::EnumVariant {
            path,
            fields,
            rest: _,
            span,
        } => {
            let [enum_name, variant_name] = path.as_slice() else {
                return Err(MetelError::internal("invalid pattern path"));
            };
            let _ = span;
            bind_enum_variant_fields(enum_name, variant_name, fields, scrutinee_ty, ctx)?;
        }
        Pattern::Struct { name, fields, .. } => {
            bind_struct_pattern_fields(name, fields, scrutinee_ty, ctx)?;
        }
        Pattern::Record { fields, .. } => {
            let Type::Record(record_fields) = scrutinee_ty else {
                return Err(MetelError::internal("record pattern on non-record type"));
            };
            for field in fields {
                let field_ty = record_fields
                    .iter()
                    .find(|(name, _)| name == field)
                    .map(|(_, ty)| ty.clone())
                    .ok_or_else(|| {
                        MetelError::internal(format!("missing record field `{field}`"))
                    })?;
                ctx.bind(field, field_ty);
            }
        }
        Pattern::Array {
            elems,
            rest,
            span: _,
        } => {
            let elem_ty = match scrutinee_ty {
                Type::Array(t) | Type::SizedArray(t, _) => *t.clone(),
                _ => return Err(MetelError::internal("array pattern on non-array type")),
            };
            if let Some(rest_name) = rest {
                ctx.bind(rest_name, Type::Array(Box::new(elem_ty.clone())));
            }
            for pat in elems {
                construct_pattern_bindings(pat, &elem_ty, ctx)?;
            }
        }
    }
    Ok(())
}

pub(super) fn extract_type_args_from_type(ty: &Type) -> Vec<Type> {
    match ty {
        Type::Named(_, args) => args.clone(),
        _ => vec![],
    }
}

// Exhaustive handling of every enum-literal construction case (generic args,
// variant shapes, inference fallbacks); splitting it up would scatter one
// coherent dispatch table across many small functions with no real gain in
// clarity.
#[allow(clippy::too_many_lines)]
pub(super) fn construct_enum_literal_ty(
    enum_name: &str,
    variant_name: &str,
    typed_fields: &[(String, TypedExpr)],
    expected_ty: Option<&Type>,
    span: &Span,
    ctx: &mut ConstructCtx,
) -> Result<Type, MetelError> {
    // Resolve concrete type arguments using the same instantiate-then-unify
    // pattern as instantiate_scheme_for_call.
    let enum_info = ctx.registry.enum_info(enum_name).ok_or_else(|| {
        MetelError::type_error(
            TypeErrorCode::T0003,
            format!("unknown enum `{enum_name}`"),
            span,
        )
    })?;
    let variant = enum_info
        .variants
        .iter()
        .find(|v| v.name == variant_name)
        .ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0003,
                format!("no variant `{variant_name}` on enum `{enum_name}`"),
                span,
            )
        })?;

    // Assign a fresh type variable to each formal type parameter and
    // build an instantiation substitution for this particular usage site.
    let mut init_subst = Substitution::new();
    let fresh_vars: Vec<InferType> = enum_info
        .type_params
        .iter()
        .map(|&tp| {
            let fresh = InferType::Var(ctx.gen.fresh());
            init_subst.bind(tp, fresh.clone());
            fresh
        })
        .collect();

    // Unify each instantiated field type against the actual expression type
    // to solve for the fresh variables.
    let mut local_subst = Substitution::new();
    for (field_name, typed_expr) in typed_fields {
        if let Some(field_entry) = variant
            .fields
            .iter()
            .find(|entry| &entry.name == field_name)
        {
            let instantiated = init_subst.apply(&field_entry.ty);
            let actual = type_to_infer(typed_expr.ty());
            if let Ok(s) = unify(
                &local_subst.apply(&instantiated),
                &local_subst.apply(&actual),
            ) {
                local_subst = local_subst.compose(&s);
            }
        }
    }

    // Apply the local substitution to recover concrete type arguments.
    // If a type param remains unresolved (fieldless variants like `Perhaps::None`),
    // fall back to the annotation's args.
    // type_to_infer normalises Perhaps/Result into Named for uniform handling.
    let hint_args: Vec<Type> = expected_ty
        .map(|ty| {
            if let InferType::Named(n, args) = type_to_infer(ty) {
                if n == enum_name {
                    args.iter()
                        .map(|a| infer_type_to_type(a, span))
                        .collect::<Result<Vec<_>, _>>()
                        .unwrap_or_default()
                } else {
                    vec![]
                }
            } else {
                vec![]
            }
        })
        .unwrap_or_default();
    let concrete_args: Vec<Type> = fresh_vars
        .iter()
        .enumerate()
        .map(|(i, fv)| {
            let resolved = local_subst.apply(fv);
            if matches!(resolved, InferType::Var(_)) {
                hint_args.get(i).cloned().ok_or_else(|| {
                    MetelError::type_error(
                        TypeErrorCode::T0002,
                        "cannot infer type; add a type annotation",
                        span,
                    )
                })
            } else {
                infer_type_to_type(&resolved, span)
            }
        })
        .collect::<Result<_, _>>()?;

    // T0012: check each resolved type arg satisfies the enum's declared bounds.
    let generic_types_by_name: HashMap<String, Type> = ctx
        .registry
        .struct_generic_names_for(ctx.current_module, enum_name)
        .into_iter()
        .flatten()
        .cloned()
        .zip(concrete_args.iter().cloned())
        .collect();
    let record_kinds = ctx
        .get_type_param_record_kinds(enum_name)
        .cloned()
        .unwrap_or_else(|| vec![false; concrete_args.len()]);
    if let Some(param_bounds) = ctx
        .registry
        .type_param_bounds_for(ctx.current_module, enum_name)
    {
        for (i, bounds) in param_bounds.iter().enumerate() {
            let record_kind = record_kinds.get(i).copied().unwrap_or(false);
            if bounds.is_empty() && !record_kind {
                continue;
            }
            let Some(concrete_arg) = concrete_args.get(i) else {
                continue;
            };
            check_type_satisfies_bounds(
                concrete_arg,
                bounds,
                record_kind,
                enum_name,
                span,
                ctx.registry,
                ctx.current_module,
                &generic_types_by_name,
            )?;
        }
    }
    // T0012 negative bounds: check each resolved type arg does NOT implement
    // the declared negative bounds (RFC-0072, issue #243).
    if let Some(neg_param_bounds) = ctx
        .registry
        .neg_type_param_bounds_for(ctx.current_module, enum_name)
    {
        for (i, neg_bounds) in neg_param_bounds.iter().enumerate() {
            let record_kind = record_kinds.get(i).copied().unwrap_or(false);
            if neg_bounds.is_empty() && !record_kind {
                continue;
            }
            let Some(concrete_arg) = concrete_args.get(i) else {
                continue;
            };
            check_type_does_not_satisfy_bound(
                concrete_arg,
                neg_bounds,
                record_kind,
                enum_name,
                span,
                ctx.registry,
                ctx.current_module,
                &generic_types_by_name,
            )?;
        }
    }

    let infer_args: Vec<InferType> = concrete_args.iter().map(type_to_infer).collect();
    infer_type_to_type(&InferType::Named(enum_name.to_string(), infer_args), span)
}

pub(super) fn bind_enum_variant_fields(
    enum_name: &str,
    variant_name: &str,
    fields: &[String],
    scrutinee_ty: &Type,
    ctx: &mut ConstructCtx,
) -> Result<(), MetelError> {
    let enum_info = ctx
        .registry
        .enum_info(enum_name)
        .ok_or_else(|| MetelError::internal(format!("unknown enum `{enum_name}`")))?
        .clone();
    let variant = enum_info
        .variants
        .iter()
        .find(|v| v.name == variant_name)
        .ok_or_else(|| MetelError::internal(format!("unknown variant `{variant_name}`")))?
        .clone();
    let type_args = extract_type_args_from_type(scrutinee_ty);
    let mut remap = Substitution::new();
    for (&tp, arg_ty) in enum_info.type_params.iter().zip(type_args.iter()) {
        remap.bind(tp, InferType::Concrete(arg_ty.clone()));
    }
    for field_name in fields {
        let (template_ty, field_span) = variant
            .fields
            .iter()
            .find(|entry| entry.name == *field_name)
            .map(|entry| (entry.ty.clone(), entry.span.clone()))
            .ok_or_else(|| {
                MetelError::internal(format!(
                    "no field `{field_name}` on variant `{variant_name}`"
                ))
            })?;
        let concrete = infer_type_to_type(&remap.apply(&template_ty), &field_span)?;
        ctx.bind(field_name, concrete);
    }
    Ok(())
}

/// RFC-0032 §4/§5, RFC-0034 §5: Pass 2 counterpart of `infer_struct_pattern` --
/// field-visibility and exhaustiveness were already checked in Pass 1 against the
/// scrutinee's unsubstituted type; this binds each named field to its concrete
/// (generic-substituted) type for the arm body, the same shape as
/// `bind_enum_variant_fields` above.
pub(super) fn bind_struct_pattern_fields(
    struct_name: &str,
    fields: &[String],
    scrutinee_ty: &Type,
    ctx: &mut ConstructCtx,
) -> Result<(), MetelError> {
    let struct_fields = ctx
        .registry
        .struct_fields(ctx.current_module, struct_name)
        .ok_or_else(|| MetelError::internal(format!("unknown struct `{struct_name}`")))?
        .clone();
    let type_params = ctx
        .registry
        .struct_type_params_for(ctx.current_module, struct_name)
        .cloned()
        .unwrap_or_default();
    let type_args = extract_type_args_from_type(scrutinee_ty);
    let mut remap = Substitution::new();
    for (&tp, arg_ty) in type_params.iter().zip(type_args.iter()) {
        remap.bind(tp, InferType::Concrete(arg_ty.clone()));
    }
    for field_name in fields {
        let (template_ty, field_span) = struct_fields
            .iter()
            .find(|entry| entry.name == *field_name)
            .map(|entry| (entry.ty.clone(), entry.span.clone()))
            .ok_or_else(|| {
                MetelError::internal(format!("no field `{field_name}` on `{struct_name}`"))
            })?;
        let concrete = infer_type_to_type(&remap.apply(&template_ty), &field_span)?;
        ctx.bind(field_name, concrete);
    }
    Ok(())
}
