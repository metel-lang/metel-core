use std::collections::{BTreeSet, HashMap, HashSet};

use crate::data::ast::GenericParam;
use crate::data::types::Type;
use crate::pipeline::type_checking::type_engine::{GenericBound, InferType, TypeScheme, TypeVar};

use super::{generic_placeholder_name, infer_to_type, type_expr_to_infer};

pub(super) fn row_samples(
    scheme: &TypeScheme,
    generics: &[GenericParam],
    named_samples: &HashMap<String, InferType>,
) -> Option<HashMap<TypeVar, Type>> {
    let mut rows: HashSet<usize> = scheme
        .param_names
        .iter()
        .enumerate()
        .filter(|(_, name)| {
            generics
                .iter()
                .any(|generic| generic.is_row && generic.name == **name)
        })
        .map(|(index, _)| index)
        .collect();
    for (target, equations) in scheme.row_remainders.iter().enumerate() {
        for (source, _) in equations {
            rows.extend([target, *source]);
        }
    }
    // An open-row parameter has an anonymous record-kinded value variable,
    // distinct from its declared tail. Borrowed rows are not in
    // `open_row_params` (that table governs by-value narrowing), but still
    // need their structural field entitlements during reconstruction. An
    // impl on a structural row records the same value variable as `Self`.
    rows.extend(
        scheme
            .quantified_vars
            .iter()
            .enumerate()
            .filter_map(|(index, _)| {
                let name = scheme.param_names.get(index).map_or("", String::as_str);
                (scheme.record_kinds.get(index) == Some(&true) && matches!(name, "" | "Self"))
                    .then_some(index)
            }),
    );
    rows.extend(
        scheme
            .open_row_params
            .iter()
            .enumerate()
            .filter(|(_, open)| **open)
            .map(|(index, _)| index),
    );
    let mut result = HashMap::new();
    for index in &rows {
        let group = row_group(scheme, *index);
        let tail = symbolic_tail(scheme, &group, named_samples)?;
        let fields = row_fields(scheme, *index, named_samples)?;
        let sample = match tail {
            Type::Record(_) => Type::Record(fields),
            tail => Type::with_row_tail(fields, Some(Box::new(tail))),
        };
        result.insert(*scheme.quantified_vars.get(*index)?, sample);
    }
    complete_remainders(scheme, &mut result)?;
    Some(result)
}

fn complete_remainders(scheme: &TypeScheme, samples: &mut HashMap<TypeVar, Type>) -> Option<()> {
    loop {
        let before = samples.clone();
        for (target, equations) in scheme.row_remainders.iter().enumerate() {
            let target_var = *scheme.quantified_vars.get(target)?;
            for (source, removed) in equations {
                let source_sample = samples.get(scheme.quantified_vars.get(*source)?)?;
                let source_fields = match source_sample {
                    Type::Record(fields) | Type::OpenRecord { fields, .. } => fields.clone(),
                    Type::SymbolicRow { .. } => Vec::new(),
                    _ => return None,
                };
                let target_sample = samples.get(&target_var)?;
                let mut fields: std::collections::BTreeMap<_, _> = match target_sample {
                    Type::Record(fields) | Type::OpenRecord { fields, .. } => {
                        fields.iter().cloned().collect()
                    }
                    Type::SymbolicRow { .. } => std::collections::BTreeMap::new(),
                    _ => return None,
                };
                let mut source_head: std::collections::BTreeMap<_, _> =
                    source_fields.iter().cloned().collect();
                for (label, ty) in &fields {
                    if removed.contains(label) {
                        return None;
                    }
                    if source_head
                        .get(label)
                        .is_some_and(|previous| previous != ty)
                    {
                        return None;
                    }
                    source_head.insert(label.clone(), ty.clone());
                }
                let source_tail = source_sample.row_tail().cloned().map(Box::new);
                for (label, ty) in source_fields {
                    if !removed.contains(&label) {
                        if fields.get(&label).is_some_and(|previous| previous != &ty) {
                            return None;
                        }
                        fields.insert(label, ty);
                    }
                }
                let sample = Type::with_row_tail(fields.into_iter().collect(), source_tail.clone());
                samples.insert(target_var, sample);
                samples.insert(
                    *scheme.quantified_vars.get(*source)?,
                    Type::with_row_tail(source_head.into_iter().collect(), source_tail),
                );
            }
        }
        if *samples == before {
            return Some(());
        }
    }
}

fn row_group(scheme: &TypeScheme, index: usize) -> BTreeSet<usize> {
    let mut group = BTreeSet::from([index]);
    loop {
        let before = group.len();
        for (target, equations) in scheme.row_remainders.iter().enumerate() {
            for (source, _) in equations {
                if group.contains(&target) || group.contains(source) {
                    group.extend([target, *source]);
                }
            }
        }
        if before == group.len() {
            return group;
        }
    }
}

fn symbolic_tail(
    scheme: &TypeScheme,
    group: &BTreeSet<usize>,
    named_samples: &HashMap<String, InferType>,
) -> Option<Type> {
    if group.iter().any(|index| {
        scheme
            .bounds
            .get(*index)
            .into_iter()
            .flatten()
            .any(|bound| matches!(bound, GenericBound::Row(row) if !row.open))
    }) {
        return Some(Type::Record(Vec::new()));
    }
    let mut aspects = BTreeSet::new();
    let mut excluded = BTreeSet::new();
    let mut forbidden_fields = Vec::new();
    for index in group {
        let bounds = scheme.bounds.get(*index).map_or(&[][..], Vec::as_slice);
        let heads: HashSet<_> = bounds
            .iter()
            .filter_map(|bound| match bound {
                GenericBound::Row(row) => Some(row.fields.iter().map(|field| field.label.clone())),
                _ => None,
            })
            .flatten()
            .collect();
        excluded.extend(heads.iter().cloned());
        for bound in bounds {
            if let GenericBound::AllFields {
                aspects: granted,
                except,
            } = bound
                && except.iter().all(|label| heads.contains(label))
            {
                aspects.extend(granted.iter().cloned());
            }
        }
        for bound in scheme.neg_bounds.get(*index).into_iter().flatten() {
            if let GenericBound::Row(row) = bound {
                for field in &row.fields {
                    let ty = match &field.ty {
                        Some(annotation) => Some(infer_to_type(
                            &crate::pipeline::type_checking::substitute_named_generics(
                                &type_expr_to_infer(annotation),
                                named_samples,
                            ),
                        )?),
                        None => None,
                    };
                    let fact = (field.label.clone(), ty);
                    if !forbidden_fields.contains(&fact) {
                        forbidden_fields.push(fact);
                    }
                }
                excluded.extend(
                    row.fields
                        .iter()
                        .filter(|field| field.ty.is_none())
                        .map(|field| field.label.clone()),
                );
            }
        }
        for (_, removed) in scheme.row_remainders.get(*index).into_iter().flatten() {
            excluded.extend(removed.iter().cloned());
        }
    }
    Some(Type::SymbolicRow {
        name: generic_placeholder_name(
            scheme.quantified_vars[*group.first().expect("row group has its own index")],
        ),
        field_aspects: aspects.into_iter().collect(),
        excluded_labels: excluded.into_iter().collect(),
        forbidden_fields,
    })
}

fn row_fields(
    scheme: &TypeScheme,
    index: usize,
    named_samples: &HashMap<String, InferType>,
) -> Option<Vec<(String, Type)>> {
    let mut fields = std::collections::BTreeMap::new();
    for bound in scheme.bounds.get(index).into_iter().flatten() {
        if let GenericBound::Row(row) = bound {
            for field in &row.fields {
                let ty = field.ty.as_ref().map_or_else(
                    || {
                        Some(Type::Named(
                            format!(
                                "{}__field_{}",
                                generic_placeholder_name(scheme.quantified_vars[index]),
                                field.label
                            ),
                            Vec::new(),
                            crate::data::types::NominalId::NONE,
                        ))
                    },
                    |annotation| {
                        infer_to_type(&crate::pipeline::type_checking::substitute_named_generics(
                            &type_expr_to_infer(annotation),
                            named_samples,
                        ))
                    },
                )?;
                fields.insert(field.label.clone(), ty);
            }
        }
    }
    Some(fields.into_iter().collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::ast::TypeExpr;
    use crate::pipeline::type_checking::type_engine::{
        RowConditionCheck, RowConstraint, RowConstraintField, TypeDefinitionRegistry,
    };

    fn row(label: &str) -> GenericBound {
        GenericBound::Row(RowConstraint {
            fields: vec![RowConstraintField {
                label: label.into(),
                ty: Some(TypeExpr::Named("String".into(), Vec::new())),
            }],
            open: true,
        })
    }

    #[test]
    fn remainder_known_fields_are_retained_in_both_directions() {
        let mut scheme = TypeScheme::mono(InferType::unit());
        scheme.quantified_vars = vec![TypeVar(1), TypeVar(2)];
        scheme.param_names = vec!["R".into(), "Rest".into()];
        scheme.bounds = vec![vec![row("token")], vec![row("extra")]];
        scheme.row_remainders = vec![vec![], vec![(0, vec!["token".into()])]];
        let samples = row_samples(&scheme, &[], &HashMap::new()).expect("row samples");
        let Type::OpenRecord { fields, tail } = &samples[&TypeVar(1)] else {
            panic!("source row must retain its head and unknown tail");
        };
        assert_eq!(
            fields,
            &vec![("extra".into(), Type::Str), ("token".into(), Type::Str)]
        );
        let Type::OpenRecord {
            fields,
            tail: rest_tail,
        } = &samples[&TypeVar(2)]
        else {
            panic!("remainder must retain its required field");
        };
        assert_eq!(fields, &vec![("extra".into(), Type::Str)]);
        assert_eq!(tail, rest_tail);
    }

    #[test]
    fn unknown_tail_does_not_prove_a_required_field_absent_or_row_closed() {
        let registry = TypeDefinitionRegistry::new();
        let tail = Type::SymbolicRow {
            name: "opaque".into(),
            field_aspects: vec![],
            excluded_labels: vec!["known".into()],
            forbidden_fields: vec![],
        };
        let arg = InferType::RowExtend {
            fields: vec![("known".into(), InferType::str())],
            tail: Box::new(InferType::Concrete(tail)),
        };
        let GenericBound::Row(required) = row("unknown") else {
            unreachable!()
        };
        assert_eq!(
            registry.row_condition_check(&[], &arg, &required, false),
            RowConditionCheck::Unknown
        );
        let GenericBound::Row(mut exact) = row("known") else {
            unreachable!()
        };
        exact.open = false;
        assert_eq!(
            registry.row_condition_check(&[], &arg, &exact, false),
            RowConditionCheck::Unknown
        );
    }
}
