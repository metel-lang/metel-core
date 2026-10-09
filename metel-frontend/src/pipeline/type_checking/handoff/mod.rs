use std::collections::HashMap;

use crate::data::ast::Span;
use crate::data::error::MetelError;
use crate::data::types::Type;
use crate::pipeline::type_checking::type_engine::{
    AspectTypeArguments, DefinitionMethodFact, InferContext, InferType, Substitution, free_vars,
};

use super::conversions::infer_type_to_type;

mod abstract_signature;
pub(super) use abstract_signature::freeze_declaration_signature;
pub(super) use abstract_signature::prepare_abstract_body;

/// Immutable facts decided by inference and consumed while building the typed AST.
///
/// Concrete facts are converted here; legitimate definition parameters are frozen
/// into binder-local identities before entering durable abstract bodies. Neither
/// route permits construction to resolve decisions that Pass 1 already made.
pub(super) struct ResolvedInferenceFacts {
    closure_return_types: HashMap<Span, Type>,
    /// Solved definition types awaiting binder-local freezing. This table is a
    /// temporary join, not exposed to analyses or stored in the durable artifact.
    definition_expression_types: HashMap<Span, InferType>,
    definition_call_types: HashMap<Span, InferType>,
    definition_nominal_fields: HashMap<Span, crate::identity::FieldId>,
    definition_method_facts: HashMap<Span, DefinitionMethodFact>,
    definition_aspect_arguments: HashMap<Span, (AspectTypeArguments, AspectTypeArguments)>,
}

impl ResolvedInferenceFacts {
    pub(super) fn empty() -> Self {
        Self {
            closure_return_types: HashMap::new(),
            definition_expression_types: HashMap::new(),
            definition_call_types: HashMap::new(),
            definition_nominal_fields: HashMap::new(),
            definition_method_facts: HashMap::new(),
            definition_aspect_arguments: HashMap::new(),
        }
    }

    pub(super) fn resolve(ctx: &InferContext, subst: &Substitution) -> Result<Self, MetelError> {
        let closure_return_types = ctx
            .closure_return_types()
            .iter()
            .filter_map(|(span, ty)| {
                let resolved = subst.apply(ty);
                // A generalized closure can intentionally retain type variables and is
                // reconstructed per call site. It has no one concrete fact to hand off.
                free_vars(&resolved).is_empty().then(|| {
                    infer_type_to_type(&resolved, span).map(|concrete| (span.clone(), concrete))
                })
            })
            .collect::<Result<_, _>>()?;

        Ok(Self {
            closure_return_types,
            definition_nominal_fields: ctx.definition_nominal_fields().clone(),
            definition_method_facts: ctx
                .definition_method_facts()
                .iter()
                .map(|(span, fact)| {
                    (
                        span.clone(),
                        DefinitionMethodFact {
                            contract: subst.apply(&fact.contract),
                            receiver: fact.receiver.clone(),
                            aspect: fact.aspect,
                        },
                    )
                })
                .collect(),
            definition_aspect_arguments: ctx
                .definition_aspect_arguments()
                .iter()
                .map(|(span, (positive, negative))| {
                    let resolve = |arguments: &AspectTypeArguments| {
                        arguments
                            .iter()
                            .filter_map(|((variable, aspect), args)| {
                                let InferType::Var(variable) =
                                    subst.apply(&InferType::Var(*variable))
                                else {
                                    return None;
                                };
                                Some((
                                    (variable, aspect.clone()),
                                    args.iter().map(|arg| subst.apply(arg)).collect(),
                                ))
                            })
                            .collect()
                    };
                    (span.clone(), (resolve(positive), resolve(negative)))
                })
                .collect(),
            definition_expression_types: ctx
                .definition_expression_types()
                .iter()
                .map(|(span, ty)| (span.clone(), subst.apply(ty)))
                .collect(),
            definition_call_types: ctx
                .definition_call_types()
                .iter()
                .map(|(span, ty)| (span.clone(), subst.apply(ty)))
                .collect(),
        })
    }

    pub(super) fn closure_return_type(&self, span: &Span) -> Option<&Type> {
        self.closure_return_types.get(span)
    }

    pub(super) fn definition_expression_types(&self) -> &HashMap<Span, InferType> {
        &self.definition_expression_types
    }

    pub(super) fn definition_call_types(&self) -> &HashMap<Span, InferType> {
        &self.definition_call_types
    }

    pub(super) fn definition_nominal_fields(&self) -> &HashMap<Span, crate::identity::FieldId> {
        &self.definition_nominal_fields
    }

    pub(super) fn definition_method_facts(&self) -> &HashMap<Span, DefinitionMethodFact> {
        &self.definition_method_facts
    }

    pub(super) fn definition_aspect_arguments(
        &self,
        span: &Span,
    ) -> Option<&(AspectTypeArguments, AspectTypeArguments)> {
        self.definition_aspect_arguments.get(span)
    }
}

#[cfg(test)]
mod tests;
