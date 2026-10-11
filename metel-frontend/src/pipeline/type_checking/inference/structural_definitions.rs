//! Definition checking for structural targets, independent of runtime receivers.

use super::{
    FunDecl, FunGeneralization, GenericBound, GenericParam, HashMap, ImplBlock, InferContext,
    InferType, MetelError, TypeVar, ann_to_infer, collect_fun_type_var_bounds,
    collect_negative_fun_type_var_bounds, constrain_with_read_copy, generalize, infer_block,
};
use crate::data::ast::ReceiverKind;
use crate::pipeline::type_checking::type_engine::{Substitution, TypeScheme};
use std::collections::HashSet;

struct Definition {
    declaration: FunDecl,
    names: HashMap<String, TypeVar>,
    positive: HashMap<TypeVar, Vec<GenericBound>>,
    negative: HashMap<TypeVar, Vec<GenericBound>>,
}

pub(super) fn infer_record_definition(
    method: &FunDecl,
    implementation: &ImplBlock,
    ctx: &mut InferContext,
    generalizations: &mut Vec<FunGeneralization>,
) -> Result<(), MetelError> {
    if method.native.is_some() {
        return Ok(());
    }
    let enclosing = super::structural_binders::enclosing_definition(method, implementation);
    let definition = record_definition(method, &enclosing, ctx);
    let saved_names = ctx.swap_type_params(definition.names.clone());
    let saved_positive = ctx.swap_type_param_bounds(definition.positive.clone());
    let saved_negative = ctx.swap_negative_type_param_bounds(definition.negative.clone());
    let (saved_memo, saved_projections) = ctx.swap_assoc_projections();
    let rows = row_decompositions(&definition, &enclosing, ctx);
    let saved_rows = ctx.swap_row_decompositions(rows);
    let saved_exclusions = ctx.swap_row_exclusions(super::collect_fun_row_exclusions(
        &definition.declaration,
        &definition.names,
    ));
    let saved_fields = ctx.swap_row_field_vars();
    let checkpoint = ctx.rigidity_tracking_checkpoint();
    ctx.track_rigidity_parameters(definition.names.values().copied());
    let parameters = parameter_types(method, &definition.names, ctx);
    let result = method
        .return_type
        .as_ref()
        .map_or_else(InferType::unit, |annotation| ann_to_infer(annotation, ctx));
    ctx.push_scope();
    let saved_flow = ctx.flow_enter_body();
    for (parameter, ty) in method.params.iter().zip(&parameters) {
        ctx.bind_mono(
            &parameter.name,
            ty.clone(),
            parameter.mutable || matches!(parameter.receiver, Some(ReceiverKind::RefMut)),
        );
    }
    let saved_return = ctx.push_return_type(result.clone());
    let body_type = infer_block(&method.body, ctx, generalizations)?;
    let result_span = method
        .body
        .tail
        .as_ref()
        .map_or(&method.body.span, |tail| tail.span());
    constrain_with_read_copy(ctx, body_type, result.clone(), result_span.clone());
    ctx.pop_return_type(saved_return);
    ctx.flow_exit_body(saved_flow);
    ctx.pop_scope();
    let projections = ctx.take_recorded_assoc_projections();
    ctx.restore_assoc_projections(saved_memo, saved_projections);
    ctx.swap_row_decompositions(saved_rows);
    ctx.swap_row_exclusions(saved_exclusions);
    ctx.restore_row_field_vars(saved_fields);
    ctx.swap_type_params(saved_names);
    ctx.swap_type_param_bounds(saved_positive);
    ctx.swap_negative_type_param_bounds(saved_negative);
    let solved = ctx.solve()?;
    let partial = ctx.default_literal_vars(&solved);
    let mut seen = HashSet::new();
    let rigid: Vec<_> = definition
        .declaration
        .generics
        .iter()
        .filter_map(|generic| {
            let variable = *definition.names.get(&generic.name)?;
            let source_name = implementation
                .generics
                .iter()
                .zip(&enclosing.generics)
                .find(|(_, renamed)| renamed.name == generic.name)
                .map_or(generic.name.as_str(), |(original, _)| {
                    original.name.as_str()
                });
            seen.insert(variable).then_some((source_name, variable))
        })
        .collect();
    super::declarations::check_declared_parameters_rigid(
        &method.span,
        &rigid,
        &|ty| partial.apply(ty),
        &|variable| ctx.rigidity_origin(variable).cloned(),
    )?;
    ctx.restore_rigidity_tracking(checkpoint);
    let substitution = partial.to_substitution();
    let signature = substitution.apply(&InferType::fun(parameters, result));
    let scheme = retain_signature(&definition, signature, &substitution);
    let scheme = super::declarations::retain_body_projections(scheme, &projections, &substitution);
    ctx.record_definition_template(method.span.clone(), scheme, definition.declaration.generics);
    Ok(())
}

fn record_definition(
    method: &FunDecl,
    implementation: &ImplBlock,
    ctx: &mut InferContext,
) -> Definition {
    let mut declaration = method.clone();
    if let Some(enclosing) = &implementation.where_clause {
        let clause = declaration
            .where_clause
            .get_or_insert_with(|| enclosing.clone());
        if method.where_clause.is_some() {
            clause.constraints.extend(enclosing.constraints.clone());
            clause.row_equations.extend(enclosing.row_equations.clone());
            clause.field_wise.extend(enclosing.field_wise.clone());
        }
    }
    for generic in &implementation.generics {
        if !declaration
            .generics
            .iter()
            .any(|own| own.name == generic.name)
        {
            declaration.generics.push(generic.clone());
        }
    }
    declaration.generics.insert(
        0,
        GenericParam {
            name: "Self".to_string(),
            is_record: true,
            is_row: false,
            bounds: vec![],
        },
    );
    let names: HashMap<_, _> = declaration
        .generics
        .iter()
        .map(|generic| (generic.name.clone(), ctx.fresh_type_var_raw()))
        .collect();
    let self_variable = names["Self"];
    // The receiver may be nominal: even a pure tail describes its fields, not
    // its identity or nominal aspect membership.
    let mut positive = collect_fun_type_var_bounds(&declaration, &names);
    let mut negative = collect_negative_fun_type_var_bounds(&declaration, &names);
    if let crate::data::ast::TypeExpr::OpenRecord(fields, tail) = &implementation.target_type
        && let Some(variable) = tail.var.as_ref().and_then(|name| names.get(name))
        && !method
            .generics
            .iter()
            .any(|generic| Some(&generic.name) == tail.var.as_ref())
    {
        let exclusions: Vec<_> = negative
            .get(variable)
            .into_iter()
            .flatten()
            .filter_map(|bound| {
                let GenericBound::Row(row) = bound else {
                    return None;
                };
                let mut row = row.clone();
                row.fields
                    .retain(|field| !fields.iter().any(|(label, _)| label == &field.label));
                (!row.fields.is_empty()).then_some(GenericBound::Row(row))
            })
            .collect();
        negative
            .entry(self_variable)
            .or_default()
            .extend(exclusions);
    }
    let row = super::super::registry::record_target_row(implementation)
        .expect("record definition requires a structural target");
    let self_grants = positive.entry(self_variable).or_default();
    self_grants.push(GenericBound::Row(row));
    self_grants.extend(super::super::registry::record_target_all_fields(
        implementation,
    ));
    if let Some(aspect) = &implementation.aspect_name {
        self_grants.push(GenericBound::Aspect(aspect.clone()));
    }
    Definition {
        declaration,
        names,
        positive,
        negative,
    }
}

fn row_decompositions(
    definition: &Definition,
    implementation: &ImplBlock,
    ctx: &mut InferContext,
) -> crate::pipeline::type_checking::type_engine::RowDecompositions {
    let mut rows = HashMap::new();
    for equation in definition
        .declaration
        .where_clause
        .iter()
        .flat_map(|clause| &clause.row_equations)
    {
        let Some(&source) = definition.names.get(&equation.var) else {
            continue;
        };
        let tail = equation
            .tail
            .var
            .as_ref()
            .and_then(|name| definition.names.get(name))
            .copied();
        let fields = equation
            .fields
            .iter()
            .map(|(label, ty)| (label.clone(), ann_to_infer(ty, ctx)))
            .collect();
        rows.insert(source, (fields, tail));
    }
    if let crate::data::ast::TypeExpr::OpenRecord(fields, tail) = &implementation.target_type
        && let Some(tail) = tail
            .var
            .as_ref()
            .and_then(|name| definition.names.get(name))
            .copied()
    {
        let fields = fields
            .iter()
            .map(|(label, ty)| (label.clone(), ann_to_infer(ty, ctx)))
            .collect();
        // This decomposition describes the receiver's fields, not a type equality
        // between the receiver's nominal identity and its row.
        rows.insert(definition.names["Self"], (fields, Some(tail)));
    }
    rows
}

fn parameter_types(
    method: &FunDecl,
    names: &HashMap<String, TypeVar>,
    ctx: &mut InferContext,
) -> Vec<InferType> {
    method
        .params
        .iter()
        .map(|parameter| {
            if let Some(receiver) = &parameter.receiver {
                let self_type = InferType::Var(names["Self"]);
                match receiver {
                    ReceiverKind::Value => self_type,
                    ReceiverKind::Ref => InferType::Reference(Box::new(self_type)),
                    ReceiverKind::RefMut => InferType::MutReference(Box::new(self_type)),
                }
            } else if let Some(annotation) = &parameter.type_ann {
                ann_to_infer(annotation, ctx)
            } else {
                ctx.fresh_var()
            }
        })
        .collect()
}

fn retain_signature(
    definition: &Definition,
    signature: InferType,
    substitution: &Substitution,
) -> TypeScheme {
    let mut scheme = super::declarations::definition_body_scheme(
        &generalize(signature, &HashSet::new()),
        &definition.names,
        &definition.declaration.generics,
        &definition.positive,
        substitution,
    );
    let negative = definition
        .negative
        .iter()
        .filter_map(
            |(variable, grants)| match substitution.apply(&InferType::Var(*variable)) {
                InferType::Var(variable) => Some((variable, grants.clone())),
                _ => None,
            },
        )
        .collect();
    let kinds = definition
        .declaration
        .generics
        .iter()
        .filter(|generic| generic.is_record || generic.is_row)
        .filter_map(|generic| definition.names.get(&generic.name))
        .filter_map(
            |variable| match substitution.apply(&InferType::Var(*variable)) {
                InferType::Var(variable) => Some((variable, true)),
                _ => None,
            },
        )
        .collect();
    scheme = scheme
        .with_neg_bounds(&negative)
        .with_record_kinds(&kinds)
        .with_row_remainders(&row_relations(definition, substitution));
    scheme
}

fn row_relations(
    definition: &Definition,
    substitution: &Substitution,
) -> HashMap<TypeVar, Vec<(TypeVar, Vec<String>)>> {
    let mut relations: HashMap<TypeVar, Vec<(TypeVar, Vec<String>)>> = HashMap::new();
    for equation in definition
        .declaration
        .where_clause
        .iter()
        .flat_map(|clause| &clause.row_equations)
    {
        let Some((&source, &tail)) = definition.names.get(&equation.var).zip(
            equation
                .tail
                .var
                .as_ref()
                .and_then(|name| definition.names.get(name)),
        ) else {
            continue;
        };
        if let (InferType::Var(source), InferType::Var(tail)) = (
            substitution.apply(&InferType::Var(source)),
            substitution.apply(&InferType::Var(tail)),
        ) {
            relations.entry(tail).or_default().push((
                source,
                equation
                    .fields
                    .iter()
                    .map(|(label, _)| label.clone())
                    .collect(),
            ));
        }
    }
    relations
}
