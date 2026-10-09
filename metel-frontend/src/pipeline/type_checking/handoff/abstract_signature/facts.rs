use super::{AbstractParameterId, AbstractSignature, SignatureFreezer, freeze_signature};
use crate::data::abstract_body::{
    AbstractAspect, AbstractAssociatedEquality, AbstractAssociatedProjection, AbstractBound,
    AbstractParameterFacts, AbstractRowRemainder,
};
use crate::data::ast::{FunDecl, Polarity, TypeExpr};
use crate::data::error::MetelError;
use crate::identity::BindingId;
use crate::pipeline::type_checking::conversions::{
    AssocResolveCtx, type_expr_to_infer_with_assoc_ctx,
};
use crate::pipeline::type_checking::type_engine::{
    AspectTypeArguments, GenericBound, InferType, TypeDefinitionRegistry, TypeScheme,
};
use std::collections::HashMap;

struct FactFreezer<'a> {
    types: SignatureFreezer<'a>,
    registry: &'a TypeDefinitionRegistry,
    module: &'a [String],
    aspect_arguments: Option<&'a (AspectTypeArguments, AspectTypeArguments)>,
    scheme: &'a TypeScheme,
}

pub(in crate::pipeline::type_checking) fn freeze_declaration_signature(
    scheme: &TypeScheme,
    binder: BindingId,
    declaration: &FunDecl,
    registry: &TypeDefinitionRegistry,
    module: &[String],
    aspect_arguments: Option<&(AspectTypeArguments, AspectTypeArguments)>,
) -> Result<AbstractSignature, MetelError> {
    let source_order: Vec<_> = declaration
        .generics
        .iter()
        .map(|generic| generic.name.as_str())
        .collect();
    let mut signature = freeze_signature(scheme, binder, &source_order, &declaration.span)?;
    let ordered = super::ordered_variables(scheme, &source_order);
    let variables: HashMap<_, _> = ordered
        .iter()
        .copied()
        .zip(signature.parameters.iter().map(|parameter| parameter.id))
        .collect();
    let types = SignatureFreezer {
        variables,
        names: signature
            .parameters
            .iter()
            .filter_map(|parameter| parameter.name.as_deref().map(|name| (name, parameter.id)))
            .collect(),
        span: &declaration.span,
    };
    let freezer = FactFreezer {
        types,
        registry,
        module,
        aspect_arguments,
        scheme,
    };
    let facts = ordered
        .iter()
        .map(|variable| {
            let index = scheme
                .quantified_vars
                .iter()
                .position(|candidate| candidate == variable)
                .expect("quantified variable retained");
            freezer.parameter(index)
        })
        .collect::<Result<_, _>>();
    // Missing retained facts cannot become empty grants or newly reject a valid
    // program during this staged migration. Consumers require a complete set.
    signature.facts = facts.ok();
    Ok(signature)
}

impl FactFreezer<'_> {
    fn parameter_id(&self, index: usize) -> Result<AbstractParameterId, MetelError> {
        self.scheme
            .quantified_vars
            .get(index)
            .and_then(|variable| self.types.variables.get(variable))
            .copied()
            .ok_or_else(|| MetelError::internal("abstract fact refers to an absent parameter"))
    }

    fn aspect(
        &self,
        name: &str,
        index: usize,
        polarity: Polarity,
    ) -> Result<AbstractAspect, MetelError> {
        let identity = self
            .registry
            .resolve_type_id(self.module, name)
            .ok_or_else(|| {
                MetelError::internal(format!("abstract fact has unresolved aspect `{name}`"))
            })?;
        let variable = self.scheme.quantified_vars[index];
        let arguments = self
            .aspect_arguments
            .and_then(|(positive, negative)| {
                let table = if polarity == Polarity::Positive {
                    positive
                } else {
                    negative
                };
                table.get(&(variable, name.to_string()))
            })
            .map(|args| {
                args.iter()
                    .map(|arg| self.fact_type(arg))
                    .collect::<Result<Vec<_>, _>>()
            })
            .transpose()?
            .unwrap_or_default();
        if self
            .registry
            .aspect_generics_in(self.module, name)
            .is_some_and(|params| params.len() != arguments.len())
        {
            return Err(MetelError::internal(
                "abstract aspect arguments are not fully retained",
            ));
        }
        Ok(AbstractAspect {
            identity,
            name: name.to_string(),
            arguments,
        })
    }

    fn annotation(
        &self,
        annotation: &TypeExpr,
    ) -> Result<crate::data::abstract_body::AbstractType, MetelError> {
        let generics = self
            .scheme
            .param_names
            .iter()
            .cloned()
            .zip(self.scheme.quantified_vars.iter().copied())
            .collect();
        let context = AssocResolveCtx {
            registry: self.registry,
            current_module: self.module,
            current_aspect: None,
        };
        self.fact_type(&type_expr_to_infer_with_assoc_ctx(
            annotation, &generics, None, &context,
        ))
    }

    fn fact_type(
        &self,
        ty: &InferType,
    ) -> Result<crate::data::abstract_body::AbstractType, MetelError> {
        if self.has_unresolved_projection(ty) {
            return Err(MetelError::internal(
                "abstract associated projection is not fully retained",
            ));
        }
        let ty = self.types.freeze(ty)?;
        if has_unresolved_nominal(&ty) {
            return Err(MetelError::internal(
                "abstract nominal fact has no retained identity",
            ));
        }
        Ok(ty)
    }

    fn has_unresolved_projection(&self, ty: &InferType) -> bool {
        match ty {
            InferType::Named(name, args, identity) => {
                (identity.0.is_none()
                    && name
                        .split_once("::")
                        .is_some_and(|(base, _)| self.types.names.contains_key(base)))
                    || args.iter().any(|ty| self.has_unresolved_projection(ty))
            }
            InferType::Fun(params, result, ..) => {
                params.iter().any(|ty| self.has_unresolved_projection(ty))
                    || self.has_unresolved_projection(result)
            }
            InferType::Tuple(items) => items.iter().any(|ty| self.has_unresolved_projection(ty)),
            InferType::Record(fields) | InferType::Residual { fields, .. } => fields
                .iter()
                .any(|(_, ty)| self.has_unresolved_projection(ty)),
            InferType::RowExtend { fields, tail } => {
                fields
                    .iter()
                    .any(|(_, ty)| self.has_unresolved_projection(ty))
                    || self.has_unresolved_projection(tail)
            }
            InferType::Array(inner)
            | InferType::SizedArray(inner, _)
            | InferType::Reference(inner)
            | InferType::MutReference(inner) => self.has_unresolved_projection(inner),
            InferType::Dyn { type_args, .. } => type_args
                .iter()
                .any(|ty| self.has_unresolved_projection(ty)),
            InferType::Var(_) | InferType::Concrete(_) | InferType::Never => false,
        }
    }

    fn bound(
        &self,
        bound: &GenericBound,
        index: usize,
        polarity: Polarity,
    ) -> Result<AbstractBound, MetelError> {
        Ok(match bound {
            GenericBound::Aspect(name) => {
                AbstractBound::Aspect(self.aspect(name, index, polarity)?)
            }
            GenericBound::Row(row) => AbstractBound::Row {
                fields: row
                    .fields
                    .iter()
                    .map(|field| {
                        Ok((
                            field.label.clone(),
                            field
                                .ty
                                .as_ref()
                                .map(|ty| self.annotation(ty))
                                .transpose()?,
                        ))
                    })
                    .collect::<Result<_, MetelError>>()?,
                open: row.open,
            },
            GenericBound::AllFields { aspects, except } => AbstractBound::AllFields {
                aspects: aspects
                    .iter()
                    .map(|aspect| self.aspect(aspect, index, polarity))
                    .collect::<Result<_, _>>()?,
                except: except.clone(),
            },
        })
    }

    fn parameter(&self, index: usize) -> Result<AbstractParameterFacts, MetelError> {
        let bounds = |table: &[Vec<GenericBound>], polarity| {
            table
                .get(index)
                .into_iter()
                .flatten()
                .map(|bound| self.bound(bound, index, polarity))
                .collect::<Result<_, _>>()
        };
        let associated_equalities = self
            .scheme
            .assoc_eq_constraints
            .get(index)
            .into_iter()
            .flatten()
            .map(|(aspect, name, ty)| {
                Ok(AbstractAssociatedEquality {
                    aspect: self.aspect(aspect, index, Polarity::Positive)?,
                    name: name.clone(),
                    ty: self.types.freeze(ty)?,
                })
            })
            .collect::<Result<_, MetelError>>()?;
        let projection = self
            .scheme
            .assoc_projections
            .get(index)
            .and_then(Option::as_ref)
            .map(|(base, aspect, name, _)| {
                Ok(AbstractAssociatedProjection {
                    base: self.parameter_id(*base)?,
                    aspect: self.aspect(aspect, *base, Polarity::Positive)?,
                    name: name.clone(),
                })
            })
            .transpose()?;
        let opaque_return = self
            .scheme
            .opaque_returns
            .get(index)
            .and_then(Option::as_ref)
            .map(|(aspect, ty)| {
                self.aspect(aspect, index, Polarity::Positive)
                    .map(|aspect| (aspect, ty.clone()))
            })
            .transpose()?;
        let remainders = self
            .scheme
            .row_remainders
            .get(index)
            .into_iter()
            .flatten()
            .map(|(source, removed)| {
                self.parameter_id(*source)
                    .map(|source| AbstractRowRemainder {
                        source,
                        removed: removed.clone(),
                    })
            })
            .collect::<Result<_, _>>()?;
        Ok(AbstractParameterFacts {
            parameter: self.parameter_id(index)?,
            record_kind: self
                .scheme
                .record_kinds
                .get(index)
                .copied()
                .unwrap_or(false),
            open_row_parameter: self
                .scheme
                .open_row_params
                .get(index)
                .copied()
                .unwrap_or(false),
            positive: bounds(&self.scheme.bounds, Polarity::Positive)?,
            negative: bounds(&self.scheme.neg_bounds, Polarity::Negative)?,
            associated_equalities,
            projection,
            opaque_return,
            remainders,
        })
    }
}

fn has_unresolved_nominal(ty: &crate::data::abstract_body::AbstractType) -> bool {
    use crate::data::abstract_body::AbstractType;
    match ty {
        AbstractType::Named {
            identity,
            arguments,
            ..
        } => identity.0.is_none() || arguments.iter().any(has_unresolved_nominal),
        AbstractType::Function {
            parameters, result, ..
        } => parameters.iter().any(has_unresolved_nominal) || has_unresolved_nominal(result),
        AbstractType::Tuple(items) => items.iter().any(has_unresolved_nominal),
        AbstractType::Record(fields) | AbstractType::Residual { fields, .. } => {
            fields.iter().any(|(_, ty)| has_unresolved_nominal(ty))
        }
        AbstractType::OpenRecord { fields, tail } => {
            fields.iter().any(|(_, ty)| has_unresolved_nominal(ty)) || has_unresolved_nominal(tail)
        }
        AbstractType::Array(inner)
        | AbstractType::SizedArray(inner, _)
        | AbstractType::Reference(inner)
        | AbstractType::MutReference(inner) => has_unresolved_nominal(inner),
        AbstractType::Dyn { .. } => true,
        AbstractType::Concrete(_) | AbstractType::Parameter(_) | AbstractType::Never => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::ast::Span;
    use crate::data::types::{NominalId, Type};
    use crate::identity::SymbolId;

    #[test]
    fn unresolved_associated_fact_is_not_an_abstract_nominal() {
        let parameter = AbstractParameterId {
            binder: BindingId::Global(SymbolId(1)),
            index: 0,
        };
        let span = Span::new(1, 1, "associated_fact.mtl");
        let scheme = TypeScheme::mono(InferType::Concrete(Type::Unit));
        let registry = TypeDefinitionRegistry::new();
        let freezer = FactFreezer {
            types: SignatureFreezer {
                variables: HashMap::new(),
                names: HashMap::from([("T", parameter)]),
                span: &span,
            },
            registry: &registry,
            module: &[],
            scheme: &scheme,
            aspect_arguments: None,
        };
        let unresolved = InferType::Array(Box::new(InferType::Named(
            "T::Item".to_string(),
            vec![],
            NominalId::NONE,
        )));
        assert!(freezer.fact_type(&unresolved).is_err());
        assert!(
            freezer
                .fact_type(&InferType::Named(
                    "Token".to_string(),
                    vec![],
                    NominalId::NONE
                ))
                .is_err()
        );
        assert_eq!(
            freezer.fact_type(&InferType::Concrete(Type::I64)).unwrap(),
            crate::data::abstract_body::AbstractType::Concrete(Type::I64)
        );
    }
}
