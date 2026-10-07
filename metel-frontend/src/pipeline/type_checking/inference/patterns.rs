use super::{
    Expr, FunGeneralization, GenericBound, InferContext, InferType, MatchExpr, MetelError, Pattern,
    Span, Type, TypeErrorCode, TypeVar, infer_block, infer_enum_variant_pattern, infer_expr,
    infer_literal, infer_struct_pattern, type_expr_to_infer_with_generics,
};

pub(super) fn infer_match(
    m: &MatchExpr,
    ctx: &mut InferContext,
    fun_generalizations: &mut Vec<FunGeneralization>,
) -> Result<InferType, MetelError> {
    let raw_scrutinee_ty = infer_expr(&m.scrutinee, ctx, fun_generalizations)?;
    // RFC-0108: a `&T`/`&mut T` scrutinee matches against `T`'s own patterns —
    // peel reference layers before pattern inference, the same way method-call
    // receiver resolution already does. Applying the current substitution first
    // resolves a scrutinee var to its reference shape where solve order allows
    // (matching `Expr::Index`'s own peel), then peels every layer.
    let scrutinee_ty = peel_all_references(&ctx.solve()?.apply(&raw_scrutinee_ty));
    // RFC-0107: resolve bare variant patterns against the scrutinee's enum in Pass 1
    // too, so a one-segment fieldful pattern (`Some { value }`) doesn't hit
    // `infer_pattern`'s two-segment path assertion, and a bare no-field variant
    // (`Red`) is typed as the variant rather than a spurious binding.
    let scrutinee_named_ty = match &scrutinee_ty {
        InferType::Named(name, ..) | InferType::Concrete(Type::Named(name, ..)) => {
            Some(name.clone())
        }
        _ => None,
    };
    let scrutinee_variants: Option<(String, Vec<(String, bool)>)> =
        scrutinee_named_ty.clone().and_then(|name| {
            ctx.get_enum(&name).map(|info| {
                (
                    name.clone(),
                    info.variants
                        .iter()
                        .map(|v| (v.name.clone(), v.fields.is_empty()))
                        .collect(),
                )
            })
        });
    // RFC-0032 §4/§5, RFC-0034 §5: same idea, for a struct rather than an enum -- a
    // name can't be both, so this and `scrutinee_variants` above are mutually
    // exclusive by construction.
    let scrutinee_struct_name: Option<String> =
        scrutinee_named_ty.filter(|name| ctx.get_struct_fields(name).is_some());
    let result_var = ctx.fresh_var();
    // metel-core#958: each arm's row-narrowing move state forks from the state
    // before the `match`, and the arms join afterward — so a later arm never
    // sees an earlier arm's partial move, and a move in any arm still narrows
    // the binding for the code after the `match` (the join is the union).
    let entry_flow = ctx.flow_ref().clone();
    let mut joined_flow = entry_flow.clone();
    let mut any_arm = false;
    for arm in &m.arms {
        let pattern = if let Some((enum_name, variants)) = &scrutinee_variants {
            super::super::construction::resolve_bare_variant(&arm.pattern, enum_name, variants)
        } else if let Some(struct_name) = &scrutinee_struct_name {
            super::super::construction::resolve_struct_pattern(&arm.pattern, struct_name)
        } else {
            arm.pattern.clone()
        };
        *ctx.flow_mut() = entry_flow.clone();
        ctx.push_scope();
        infer_pattern(&pattern, &scrutinee_ty, false, ctx)?;
        if let Some(guard) = &arm.guard {
            let g = infer_expr(guard, ctx, fun_generalizations)?;
            ctx.add_constraint(g, InferType::bool(), arm.span.clone());
        }
        let arm_ty = infer_block(&arm.body, ctx, fun_generalizations)?;
        ctx.add_constraint(arm_ty, result_var.clone(), arm.span.clone());
        ctx.pop_scope();
        joined_flow.union_from(ctx.flow_ref());
        any_arm = true;
    }
    if any_arm {
        *ctx.flow_mut() = joined_flow;
    }
    Ok(result_var)
}

#[allow(clippy::too_many_lines)]
// limit: ["LIMIT-TYPE-INFERENCE-003"]
pub(super) fn infer_pattern(
    pattern: &Pattern,
    scrutinee_ty: &InferType,
    mutable: bool,
    ctx: &mut InferContext,
) -> Result<(), MetelError> {
    let span = pattern_span(pattern);
    match pattern {
        Pattern::Wildcard(_) => {}
        Pattern::Literal(lit, _) => {
            let lit_ty = infer_literal(lit, ctx);
            ctx.add_constraint(scrutinee_ty.clone(), lit_ty, span.clone());
        }
        Pattern::Binding(name, _) => {
            ctx.bind_mono(name, scrutinee_ty.clone(), false);
        }
        Pattern::Tuple(pats, _) => {
            let elem_vars: Vec<InferType> = pats.iter().map(|_| ctx.fresh_var()).collect();
            ctx.add_constraint(
                scrutinee_ty.clone(),
                InferType::Tuple(elem_vars.clone()),
                span.clone(),
            );
            for (pat, elem_ty) in pats.iter().zip(elem_vars.iter()) {
                infer_pattern(pat, elem_ty, false, ctx)?;
            }
        }
        Pattern::EnumVariant {
            path,
            fields,
            field_spans: _,
            rest: _,
            span: pat_span,
        } => {
            let [enum_name, variant_name] = path.as_slice() else {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0003,
                    format!("unresolved pattern path `{}`", path.join("::")),
                    pat_span,
                ));
            };
            infer_enum_variant_pattern(
                enum_name,
                variant_name,
                fields,
                scrutinee_ty,
                pat_span,
                ctx,
            )?;
        }
        Pattern::Struct {
            name,
            fields,
            field_spans: _,
            rest,
            span: pat_span,
        } => {
            infer_struct_pattern(name, fields, *rest, scrutinee_ty, pat_span, ctx)?;
        }
        Pattern::Record {
            fields,
            ignored_fields,
            field_spans: _,
            rest,
            rest_binding,
            span: pat_span,
        } => {
            if rest_binding.is_some()
                && matches!(
                    scrutinee_ty,
                    InferType::Reference(_) | InferType::MutReference(_)
                )
            {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0012,
                    "record remainder patterns require an owned scrutinee; borrowing the remainder is not supported",
                    pat_span,
                ));
            }
            let mut named_fields: Vec<String> =
                fields.iter().chain(ignored_fields).cloned().collect();
            // Record rows are canonicalized by label; preserve that invariant when
            // bound and discarded pattern fields are stored in separate lists.
            named_fields.sort();
            // A remainder binding needs a decomposition, but field presence is a
            // separate requirement: diagnose an unproven selected field first.
            // Otherwise an unconstrained row reports only that its remainder is
            // indeterminate, hiding the actionable missing-presence error.
            let peeled = peel_all_references(&ctx.solve()?.apply(scrutinee_ty));
            if rest_binding.is_some() {
                let row_tail = match &peeled {
                    InferType::Var(tv) => Some((*tv, Vec::<String>::new())),
                    InferType::RowExtend { fields, tail } => match tail.as_ref() {
                        InferType::Var(tv) => {
                            Some((*tv, fields.iter().map(|(label, _)| label.clone()).collect()))
                        }
                        _ => None,
                    },
                    _ => None,
                };
                if let Some((tv, already_known)) = row_tail {
                    for field_name in &named_fields {
                        if already_known.iter().any(|label| label == field_name) {
                            continue;
                        }
                        match resolve_row_bound_field(ctx, tv, field_name, pat_span) {
                            Some(Ok(_)) => {}
                            Some(Err(_)) | None => {
                                return Err(MetelError::type_error(
                                    TypeErrorCode::T0012,
                                    format!("field `{field_name}` is not known to be present"),
                                    pat_span,
                                ));
                            }
                        }
                    }
                }
            }
            let remainder_ty = rest_binding
                .as_ref()
                .map(|_| infer_record_remainder(&named_fields, scrutinee_ty, pat_span, ctx))
                .transpose()?;
            // #646: an abstract, row-bounded generic type parameter (`<record T:
            // { x: f64, .. }>`) has no concrete field count for `unify`'s exact-match
            // `InferType::Record` arm to check against -- resolve it the same way
            // `resolve_row_bound_field` already does for field access, instead of
            // falling into that unify path (which would either reject a legitimate
            // row-bound match or, worse, silently demand fields the bound never
            // promised).
            let row_bounds = if let InferType::Var(tv) = &peeled {
                ctx.bounds_for_type_var(*tv).map(|bounds| {
                    bounds
                        .into_iter()
                        .filter(|b| matches!(b, GenericBound::Row(_)))
                        .collect::<Vec<_>>()
                })
            } else {
                None
            }
            .filter(|rows| !rows.is_empty());

            if let Some(row_bounds) = row_bounds {
                let InferType::Var(tv) = &peeled else {
                    unreachable!("row_bounds is only Some when peeled is a Var")
                };
                let is_open = row_bounds
                    .iter()
                    .any(|b| matches!(b, GenericBound::Row(row) if row.open));
                if *rest {
                    // Non-binding rest: permits fields the pattern doesn't name,
                    // including ones the bound itself never lists (an open bound's
                    // "possibly more" is exactly this — unnamed and undiscoverable).
                } else if is_open {
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0001,
                        "a record pattern can't exhaustively match an open row bound -- \
                         its full field set isn't known here; add a trailing `..`",
                        pat_span,
                    ));
                } else {
                    let bound_fields: Vec<&str> = row_bounds
                        .iter()
                        .filter_map(|b| match b {
                            GenericBound::Row(row) => Some(row),
                            GenericBound::Aspect(_) | GenericBound::AllFields { .. } => None,
                        })
                        .flat_map(|row| row.fields.iter().map(|f| f.label.as_str()))
                        .collect();
                    let missing: Vec<&str> = bound_fields
                        .iter()
                        .filter(|name| !named_fields.iter().any(|f| f == *name))
                        .copied()
                        .collect();
                    if !missing.is_empty() {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0001,
                            format!(
                                "record pattern does not name field(s) {} of the row-bounded \
                                 type parameter -- name them or add `..`",
                                missing.join(", ")
                            ),
                            pat_span,
                        ));
                    }
                }
                for field_name in fields {
                    match resolve_row_bound_field(ctx, *tv, field_name, pat_span) {
                        Some(Ok(field_ty)) => ctx.bind_mono(field_name, field_ty, mutable),
                        Some(Err(error)) => return Err(error),
                        None => unreachable!("row bound already confirmed present above"),
                    }
                }
                for field_name in ignored_fields {
                    match resolve_row_bound_field(ctx, *tv, field_name, pat_span) {
                        Some(Ok(_)) => {}
                        Some(Err(_)) => {
                            return Err(MetelError::type_error(
                                TypeErrorCode::T0012,
                                format!("field `{field_name}` is not known to be present"),
                                pat_span,
                            ));
                        }
                        None => unreachable!("row bound already confirmed present above"),
                    }
                }
                if let (Some((rest_name, _)), Some(rest_ty)) = (rest_binding, remainder_ty) {
                    ctx.bind_mono(rest_name, rest_ty, mutable);
                }
            } else if rest_binding.is_some() {
                let record_fields = match &peeled {
                    InferType::Record(record_fields) => record_fields.clone(),
                    InferType::Named(name, args, _) => {
                        nominal_record_fields(name, args, pat_span, ctx)?
                    }
                    _ => {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0012,
                            "record remainder pattern requires a known record decomposition",
                            pat_span,
                        ));
                    }
                };
                for field_name in fields {
                    let Some((_, field_ty)) =
                        record_fields.iter().find(|(name, _)| name == field_name)
                    else {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0012,
                            format!("field `{field_name}` is not known to be present"),
                            pat_span,
                        ));
                    };
                    ctx.bind_mono(field_name, field_ty.clone(), mutable);
                }
                for field_name in ignored_fields {
                    if !record_fields.iter().any(|(name, _)| name == field_name) {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0012,
                            format!("field `{field_name}` is not known to be present"),
                            pat_span,
                        ));
                    }
                }
                if let (Some((rest_name, _)), Some(rest_ty)) = (rest_binding, remainder_ty) {
                    ctx.bind_mono(rest_name, rest_ty, mutable);
                }
            } else if *rest {
                let record_fields = match &peeled {
                    InferType::Record(record_fields) => record_fields.clone(),
                    InferType::Named(name, args, _) => {
                        nominal_record_fields(name, args, pat_span, ctx)?
                    }
                    _ => {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0012,
                            "record pattern remainder requires a known record row",
                            pat_span,
                        ));
                    }
                };
                for field_name in fields {
                    let Some((_, field_ty)) =
                        record_fields.iter().find(|(name, _)| name == field_name)
                    else {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0012,
                            format!("field `{field_name}` is not known to be present"),
                            pat_span,
                        ));
                    };
                    ctx.bind_mono(field_name, field_ty.clone(), mutable);
                }
                for field_name in ignored_fields {
                    if !record_fields.iter().any(|(name, _)| name == field_name) {
                        return Err(MetelError::type_error(
                            TypeErrorCode::T0012,
                            format!("field `{field_name}` is not known to be present"),
                            pat_span,
                        ));
                    }
                }
            } else {
                let field_vars: Vec<(String, InferType)> = named_fields
                    .iter()
                    .map(|name| (name.clone(), ctx.fresh_var()))
                    .collect();
                ctx.add_constraint(
                    scrutinee_ty.clone(),
                    InferType::Record(field_vars.clone()),
                    pat_span.clone(),
                );
                for (name, ty) in field_vars {
                    if fields.contains(&name) {
                        ctx.bind_mono(&name, ty, mutable);
                    }
                }
            }
        }
        Pattern::Array {
            elems,
            rest,
            span: pat_span,
        } => {
            let elem_var = ctx.fresh_var();
            if rest.is_some() {
                // Rest pattern: scrutinee must be an Array or SizedArray, bind rest as Array
                ctx.add_constraint(
                    scrutinee_ty.clone(),
                    InferType::Array(Box::new(elem_var.clone())),
                    pat_span.clone(),
                );
                if let Some((rest_name, _)) = rest {
                    ctx.bind_mono(
                        rest_name,
                        InferType::Array(Box::new(elem_var.clone())),
                        false,
                    );
                }
            } else {
                // Exact pattern: scrutinee must be [T; N] where N = elems.len()
                let n = elems.len() as u64;
                // Keep an already-known length mismatch for construction's
                // exhaustiveness check (T0008), rather than turning it into
                // an earlier unification mismatch (T0001). This preserves the
                // diagnostic for exact-count patterns while literals now retain
                // their intrinsic `[T; N]` type during inference.
                let resolved = ctx
                    .solve()
                    .map_or_else(|_| scrutinee_ty.clone(), |subst| subst.apply(scrutinee_ty));
                if !matches!(resolved, InferType::SizedArray(_, actual) if actual != n) {
                    ctx.add_constraint(
                        scrutinee_ty.clone(),
                        InferType::SizedArray(Box::new(elem_var.clone()), n),
                        pat_span.clone(),
                    );
                }
            }
            for pat in elems {
                infer_pattern(pat, &elem_var, false, ctx)?;
            }
        }
    }
    Ok(())
}

fn infer_record_remainder(
    fields: &[String],
    scrutinee_ty: &InferType,
    span: &Span,
    ctx: &mut InferContext,
) -> Result<InferType, MetelError> {
    let solved = ctx.solve()?.apply(scrutinee_ty);
    let facts = collect_remainder_facts(&solved, span, ctx)?;
    build_remainder_type(fields, &solved, &facts, span, ctx)
}

struct CollectedRemainderFacts {
    fields: Vec<(String, InferType)>,
    tail: Option<InferType>,
    saw_decomposition: bool,
}

fn collect_remainder_facts(
    solved: &InferType,
    span: &Span,
    ctx: &mut InferContext,
) -> Result<CollectedRemainderFacts, MetelError> {
    let mut known_fields = Vec::new();
    let mut tail = None;
    let mut saw_decomposition = false;
    let mut current = match solved {
        InferType::Named(name, args, _) => {
            InferType::Record(nominal_record_fields(name, args, span, ctx)?)
        }
        other => other.clone(),
    };
    let mut visited = std::collections::HashSet::new();
    loop {
        match current {
            InferType::Record(mut row_fields) => {
                known_fields.append(&mut row_fields);
                break;
            }
            InferType::RowExtend {
                mut fields,
                tail: next,
            } => {
                known_fields.append(&mut fields);
                match *next {
                    InferType::Var(tv) => {
                        if !visited.insert(tv) {
                            tail = Some(InferType::Var(tv));
                            break;
                        }
                        if let Some((mut decomposed, next_tail)) =
                            ctx.row_decomposition_for_type_var(tv)
                        {
                            saw_decomposition = true;
                            known_fields.append(&mut decomposed);
                            if let Some(next_tv) = next_tail {
                                current = InferType::Var(next_tv);
                                continue;
                            }
                            return Err(MetelError::type_error(
                                TypeErrorCode::T0012,
                                "the row facts do not determine the remainder type; name the open tail in a row equation",
                                span,
                            ));
                        }
                        tail = Some(InferType::Var(tv));
                        break;
                    }
                    other => {
                        current = other;
                    }
                }
            }
            InferType::Var(tv) => {
                if !visited.insert(tv) {
                    tail = Some(InferType::Var(tv));
                    break;
                }
                if let Some((mut decomposed, next_tail)) = ctx.row_decomposition_for_type_var(tv) {
                    saw_decomposition = true;
                    known_fields.append(&mut decomposed);
                    if let Some(next_tv) = next_tail {
                        current = InferType::Var(next_tv);
                        continue;
                    }
                    return Err(MetelError::type_error(
                        TypeErrorCode::T0012,
                        "the row facts do not determine the remainder type; name the open tail in a row equation",
                        span,
                    ));
                }
                known_fields.extend(collect_closed_row_bound_fields(tv, span, ctx)?);
                break;
            }
            other => {
                return Err(MetelError::type_error(
                    TypeErrorCode::T0012,
                    format!("record remainder pattern requires a record, got `{other}`"),
                    span,
                ));
            }
        }
    }
    Ok(CollectedRemainderFacts {
        fields: known_fields,
        tail,
        saw_decomposition,
    })
}

fn collect_closed_row_bound_fields(
    tv: TypeVar,
    span: &Span,
    ctx: &mut InferContext,
) -> Result<Vec<(String, InferType)>, MetelError> {
    let rows = ctx
        .bounds_for_type_var(tv)
        .unwrap_or_default()
        .into_iter()
        .filter_map(|bound| match bound {
            GenericBound::Row(row) => Some(row),
            GenericBound::Aspect(_) | GenericBound::AllFields { .. } => None,
        })
        .collect::<Vec<_>>();
    if rows.iter().any(|row| row.open) {
        return Err(MetelError::type_error(
            TypeErrorCode::T0012,
            "the field is known to exist, but the remainder type cannot be determined; add a row decomposition",
            span,
        ));
    }
    let mut fields = Vec::new();
    for field in rows.iter().flat_map(|row| &row.fields) {
        let ty = match resolve_row_bound_field(ctx, tv, &field.label, span) {
            Some(Ok(ty)) => ty,
            _ => InferType::Var(ctx.fresh_row_field_var(tv, &field.label)),
        };
        if !fields.iter().any(|(name, _)| name == &field.label) {
            fields.push((field.label.clone(), ty));
        }
    }
    Ok(fields)
}

fn build_remainder_type(
    fields: &[String],
    solved: &InferType,
    facts: &CollectedRemainderFacts,
    span: &Span,
    ctx: &mut InferContext,
) -> Result<InferType, MetelError> {
    let mut remaining = facts
        .fields
        .iter()
        .filter(|(name, _)| !fields.contains(name))
        .cloned()
        .collect::<Vec<_>>();
    for name in fields {
        if !known_fields_has_field(&remaining, name)
            && !facts.fields.iter().any(|(known, _)| known == name)
        {
            let is_entitled = match &solved {
                InferType::Var(tv) => resolve_row_bound_field(ctx, *tv, name, span).is_some(),
                InferType::RowExtend { tail, .. } => match &**tail {
                    InferType::Var(tv) => resolve_row_bound_field(ctx, *tv, name, span).is_some(),
                    _ => false,
                },
                _ => false,
            };
            let message = if is_entitled {
                format!(
                    "field `{name}` is known to exist, but the remainder type cannot be determined; add a row decomposition"
                )
            } else {
                format!("field `{name}` is not known to be present in this record")
            };
            return Err(MetelError::type_error(TypeErrorCode::T0012, message, span));
        }
    }
    remaining.sort_by(|(left, _), (right, _)| left.cmp(right));
    Ok(match &facts.tail {
        Some(tail) if remaining.is_empty() && !facts.saw_decomposition => InferType::RowExtend {
            fields: vec![],
            tail: Box::new(tail.clone()),
        },
        Some(tail) => InferType::RowExtend {
            fields: remaining,
            tail: Box::new(tail.clone()),
        },
        None => InferType::Record(remaining),
    })
}

pub(super) fn nominal_record_fields(
    name: &str,
    args: &[InferType],
    span: &Span,
    ctx: &InferContext,
) -> Result<Vec<(String, InferType)>, MetelError> {
    use crate::pipeline::type_checking::type_engine::VisibleTypeKind;

    if ctx
        .registry()
        .visible_type_kind(ctx.current_module_path(), name)
        != Some(VisibleTypeKind::Record)
    {
        return Err(MetelError::type_error(
            TypeErrorCode::T0012,
            format!(
                "`{name}` is not a nominal `record`; only anonymous records and `record`s can be decomposed"
            ),
            span,
        ));
    }
    let fields = ctx.get_struct_fields(name).ok_or_else(|| {
        MetelError::type_error(
            TypeErrorCode::T0012,
            format!("cannot determine fields of nominal record `{name}`"),
            span,
        )
    })?;
    if fields
        .iter()
        .any(|field| field.visibility != crate::data::ast::Visibility::Public)
    {
        return Err(MetelError::type_error(
            TypeErrorCode::T0012,
            format!("cannot decompose nominal record `{name}` because not all fields are public"),
            span,
        ));
    }
    let params = ctx
        .get_struct_type_params(name)
        .cloned()
        .unwrap_or_default();
    let mut subst = super::Substitution::new();
    for (param, arg) in params.iter().zip(args) {
        subst.bind(*param, arg.clone());
    }
    let assumptions = ctx.current_aspect_assumptions();
    let ty = InferType::Named(
        name.to_string(),
        args.to_vec(),
        crate::data::types::NominalId::NONE,
    );
    if ctx.registry().infer_type_satisfies_aspect(
        ctx.current_module_path(),
        &ty,
        "Drop",
        &assumptions,
    ) {
        return Err(MetelError::type_error(
            TypeErrorCode::T0012,
            format!("cannot decompose nominal record `{name}` because it implements `Drop`"),
            span,
        ));
    }
    Ok(fields
        .iter()
        .map(|field| (field.name.clone(), subst.apply(&field.ty)))
        .collect())
}

fn known_fields_has_field(fields: &[(String, InferType)], name: &str) -> bool {
    fields.iter().any(|(known, _)| known == name)
}

pub(super) fn pattern_span(pattern: &Pattern) -> &Span {
    match pattern {
        Pattern::Wildcard(s)
        | Pattern::Binding(_, s)
        | Pattern::Literal(_, s)
        | Pattern::Tuple(_, s)
        | Pattern::EnumVariant { span: s, .. }
        | Pattern::Struct { span: s, .. }
        | Pattern::Record { span: s, .. }
        | Pattern::Array { span: s, .. } => s,
    }
}

pub(super) fn named_type_name(ty: &InferType) -> Option<String> {
    match ty {
        InferType::Named(name, ..) => Some(name.clone()),
        InferType::Reference(inner) | InferType::MutReference(inner) => named_type_name(inner),
        InferType::Concrete(c) => primitive_type_name(c),
        _ => None,
    }
}

pub(super) fn record_projection_base_expr(path: &[String], span: &Span) -> Expr {
    if path.len() == 1 {
        Expr::Ident(path[0].clone(), span.clone())
    } else {
        // Synthesised for inference; no per-segment spans (module-segment
        // go-to-definition reads the parser's own `Expr::Path`, metel-core#1070).
        Expr::Path(path.to_vec(), Vec::new(), span.clone())
    }
}

/// Peels every reference layer of a chain (RFC-0067a §3's auto-deref chain
/// guarantee applies to method dispatch the same as field access — mirrors
/// `named_type_name`'s own recursion, which already handles arbitrary depth).
pub(super) fn peel_all_references(ty: &InferType) -> InferType {
    match ty {
        InferType::Reference(inner) | InferType::MutReference(inner) => peel_all_references(inner),
        other => other.clone(),
    }
}

/// Resolve `field` against `tv`'s row bound(s), for an abstract, row-bounded generic
/// type parameter (`<record T: { x: f64, .. }>`) — the read and write sides of field
/// access share this exact lookup, mirroring how `MethodCall`'s slow path resolves a
/// method against an aspect bound instead of a concrete receiver type.
///
/// Returns `None` when `tv` has no row bound at all, so the caller falls through to
/// the nominal-struct path unchanged. Returns `Some(Ok(_))` when the field is listed
/// (typed or untyped), and `Some(Err(_))` when a row bound exists but doesn't list
/// `field` — a dedicated error instead of the generic, misleading "add a type
/// annotation" T0002 the nominal-struct fallback would otherwise produce, since no
/// annotation fixes a missing row-bound field.
pub(super) fn resolve_row_bound_field(
    ctx: &mut InferContext,
    tv: TypeVar,
    field: &str,
    span: &Span,
) -> Option<Result<InferType, MetelError>> {
    if ctx.row_excludes_field(tv, field) {
        return Some(Err(MetelError::type_error(
            TypeErrorCode::T0003,
            format!("no field `{field}` on the derived row remainder"),
            span,
        )));
    }
    // RFC-0121 installment 2: `Handle.{ fd, ..R }` desugars into its own
    // parallel side-table (`fun_projection_tail_constraints`), never into the
    // ordinary bounds table `bounds_for_type_var` below reads -- see that
    // table's own doc comment for why. Check it first and independently, so
    // field access on a `Handle.{ fd, ..R }`-typed parameter works the same
    // way an ordinary row-bounded generic parameter's does.
    if let Some((brand, row)) = ctx.projection_tail_constraint_for_type_var(tv) {
        return Some(if row.fields.iter().any(|f| f.label == *field) {
            Ok(InferType::Var(ctx.fresh_row_field_var(tv, field)))
        } else {
            Err(MetelError::type_error(
                TypeErrorCode::T0003,
                format!(
                    "no field `{field}` on `{brand}.{{ {} }}`",
                    row.fields
                        .iter()
                        .map(|f| f.label.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                span,
            ))
        });
    }
    let bounds = ctx.bounds_for_type_var(tv)?;
    for bound in &bounds {
        if let GenericBound::Row(row) = bound
            && let Some(row_field) = row.fields.iter().find(|f| f.label == *field)
        {
            return Some(Ok(match &row_field.ty {
                Some(type_expr) => type_expr_to_infer_with_generics(type_expr, ctx.type_params()),
                None => InferType::Var(ctx.fresh_row_field_var(tv, field)),
            }));
        }
    }
    if bounds.iter().any(|b| matches!(b, GenericBound::Row(_))) {
        let is_open = bounds
            .iter()
            .any(|b| matches!(b, GenericBound::Row(row) if row.open));
        let mut msg = format!(
            "no field `{field}` on type parameter (bounds: {})",
            bounds
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(" + ")
        );
        if is_open {
            msg.push_str(
                "\n       hint: an open row bound only makes its explicitly listed fields \
                 accessible; a caller's extra fields aren't reachable from inside the \
                 function yet",
            );
        }
        return Some(Err(MetelError::type_error(TypeErrorCode::T0003, msg, span)));
    }
    None
}

/// Whether a `&mut self` method call through this receiver type has write access
/// *somewhere* along the chain — true the moment a `MutReference` layer is found,
/// regardless of how many shared `Reference` layers wrap it from the outside (a
/// shared reference to a `&mut T` still carries that inner `&mut T`'s own write
/// capability; reading it out doesn't downgrade it). All-`Reference` chains with
/// no `MutReference` anywhere have no write access at all.
/// Whether the receiver is reached *through a shared reference* — a reference
/// chain, none of whose layers grants mutable access.
///
/// Distinct from `!chain_provides_mut_access`, which is also true of an owned
/// receiver. An owned receiver may still be mutated when its binding is `var`,
/// so it must fall through to the binding check rather than be rejected here.
pub(super) fn is_shared_reference_chain(ty: &InferType) -> bool {
    matches!(ty, InferType::Reference(_)) && !chain_provides_mut_access(ty)
}

pub(super) fn chain_provides_mut_access(ty: &InferType) -> bool {
    match ty {
        InferType::MutReference(_) => true,
        InferType::Reference(inner) => chain_provides_mut_access(inner),
        _ => false,
    }
}

/// Canonical registry name for a primitive [`Type`], or `None` for non-primitive
/// types (tuples, arrays, functions, …). This is the single source of truth for
/// mapping a concrete primitive to the string key used in method and aspect-impl
/// registries.
pub(in crate::pipeline::type_checking) fn primitive_type_name(ty: &Type) -> Option<String> {
    let name = match ty {
        Type::Str => "String",
        Type::Boolean => "boolean",
        Type::Char => "Char",
        Type::I8 => "i8",
        Type::I16 => "i16",
        Type::I32 => "i32",
        Type::I64 => "i64",
        Type::U8 => "u8",
        Type::U16 => "u16",
        Type::U32 => "u32",
        Type::U64 => "u64",
        Type::F32 => "f32",
        Type::F64 => "f64",
        _ => return None,
    };
    Some(name.to_string())
}

/// Inverse of [`primitive_type_name`]: the concrete primitive [`Type`] for a
/// registry name, or `None` if the name is not a primitive. Used so that an
/// `impl` whose target is a primitive (e.g. `impl Display for i64`) builds its
/// `self` type as `Concrete(I64)` — matching what call sites produce — rather
/// than `Named("i64", [])`, which the unifier cannot bridge.
pub(in crate::pipeline::type_checking) fn primitive_type_from_name(name: &str) -> Option<Type> {
    let ty = match name {
        "String" => Type::Str,
        "boolean" => Type::Boolean,
        "Char" => Type::Char,
        "i8" => Type::I8,
        "i16" => Type::I16,
        "i32" => Type::I32,
        "i64" => Type::I64,
        "u8" => Type::U8,
        "u16" => Type::U16,
        "u32" => Type::U32,
        "u64" => Type::U64,
        "f32" => Type::F32,
        "f64" => Type::F64,
        _ => return None,
    };
    Some(ty)
}

pub(super) fn builtin_pattern_method_type(
    recv_ty: &InferType,
    method: &str,
    arg_tys: &[InferType],
    span: &Span,
) -> Option<Result<InferType, MetelError>> {
    let recv_ty = peel_all_references(recv_ty);
    let _ = span;
    if matches!(recv_ty, InferType::Array(_) | InferType::SizedArray(_, _))
        && method == "len"
        && arg_tys.is_empty()
    {
        return Some(Ok(InferType::int()));
    }

    None
}
