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
#[derive(Clone)]
pub(super) struct ResolvedInferenceFacts {
    definition_snapshots: HashMap<Span, Box<Self>>,
    closure_return_types: HashMap<Span, Type>,
    /// Solved definition types awaiting binder-local freezing. This table is a
    /// temporary join, not exposed to analyses or stored in the durable artifact.
    definition_expression_types: HashMap<Span, InferType>,
    definition_call_types: HashMap<Span, InferType>,
    definition_paths: HashMap<Span, super::type_engine::DefinitionPathFact>,
    definition_array_lengths: std::collections::HashSet<Span>,
    definition_nominal_fields: HashMap<Span, crate::identity::FieldId>,
    definition_method_facts: HashMap<Span, DefinitionMethodFact>,
    definition_capture_types: HashMap<Span, InferType>,
    definition_implicit_captures: HashMap<Span, Vec<super::type_engine::DefinitionImplicitCapture>>,
    definition_binding_types: HashMap<Span, InferType>,
    definition_value_boundaries: HashMap<Span, Vec<(InferType, InferType)>>,
    definition_match_patterns: HashMap<Span, super::type_engine::DefinitionMatchPattern>,
    definition_record_shapes: HashMap<Span, InferType>,
    definition_templates: HashMap<
        Span,
        (
            super::type_engine::TypeScheme,
            Vec<crate::data::ast::GenericParam>,
        ),
    >,
    definition_diverging_loops: std::collections::HashSet<Span>,
    definition_aspect_arguments: HashMap<Span, (AspectTypeArguments, AspectTypeArguments)>,
}

impl ResolvedInferenceFacts {
    pub(super) fn empty() -> Self {
        Self {
            definition_snapshots: HashMap::new(),
            closure_return_types: HashMap::new(),
            definition_expression_types: HashMap::new(),
            definition_call_types: HashMap::new(),
            definition_paths: HashMap::new(),
            definition_array_lengths: std::collections::HashSet::new(),
            definition_nominal_fields: HashMap::new(),
            definition_method_facts: HashMap::new(),
            definition_capture_types: HashMap::new(),
            definition_implicit_captures: HashMap::new(),
            definition_binding_types: HashMap::new(),
            definition_value_boundaries: HashMap::new(),
            definition_match_patterns: HashMap::new(),
            definition_record_shapes: HashMap::new(),
            definition_templates: HashMap::new(),
            definition_diverging_loops: std::collections::HashSet::new(),
            definition_aspect_arguments: HashMap::new(),
        }
    }

    pub(super) fn resolve(ctx: &InferContext, subst: &Substitution) -> Result<Self, MetelError> {
        let mut facts = Self::resolve_current(ctx, subst)?;
        facts
            .definition_snapshots
            .clone_from(ctx.definition_snapshots());
        Ok(facts)
    }

    pub(super) fn for_definition(&self, span: &Span) -> &Self {
        self.definition_snapshots
            .get(span)
            .map_or(self, Box::as_ref)
    }

    pub(super) fn has_definition_snapshot(&self, span: &Span) -> bool {
        self.definition_snapshots.contains_key(span)
    }

    pub(super) fn resolve_current(
        ctx: &InferContext,
        subst: &Substitution,
    ) -> Result<Self, MetelError> {
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
            definition_snapshots: HashMap::new(),
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
                            origin: fact.origin.clone(),
                        },
                    )
                })
                .collect(),
            definition_capture_types: ctx
                .definition_capture_types()
                .iter()
                .map(|(span, ty)| (span.clone(), subst.apply(ty)))
                .collect(),
            definition_diverging_loops: ctx.definition_diverging_loops().clone(),
            definition_implicit_captures: ctx
                .definition_implicit_captures()
                .iter()
                .map(|(span, captures)| {
                    (
                        span.clone(),
                        captures
                            .iter()
                            .map(|capture| super::type_engine::DefinitionImplicitCapture {
                                name: capture.name.clone(),
                                span: capture.span.clone(),
                                ty: subst.apply(&capture.ty),
                            })
                            .collect(),
                    )
                })
                .collect(),
            definition_templates: ctx.definition_templates().clone(),
            definition_binding_types: ctx
                .definition_binding_types()
                .iter()
                .map(|(span, ty)| (span.clone(), subst.apply(ty)))
                .collect(),
            definition_match_patterns: Self::resolve_match_patterns(ctx, subst),
            definition_value_boundaries: ctx
                .definition_value_boundaries()
                .iter()
                .map(|(span, pairs)| {
                    (
                        span.clone(),
                        pairs
                            .iter()
                            .map(|(source, target)| (subst.apply(source), subst.apply(target)))
                            .collect(),
                    )
                })
                .collect(),
            definition_record_shapes: ctx
                .definition_record_shapes()
                .iter()
                .map(|(span, shape)| (span.clone(), subst.apply(shape)))
                .collect(),
            definition_aspect_arguments: Self::resolve_aspect_arguments(ctx, subst),
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
            definition_paths: Self::resolve_paths(ctx, subst),
            definition_array_lengths: ctx.definition_array_lengths().clone(),
        })
    }

    fn resolve_aspect_arguments(
        ctx: &InferContext,
        subst: &Substitution,
    ) -> HashMap<Span, (AspectTypeArguments, AspectTypeArguments)> {
        ctx.definition_aspect_arguments()
            .iter()
            .map(|(span, (positive, negative))| {
                let resolve = |arguments: &AspectTypeArguments| {
                    arguments
                        .iter()
                        .filter_map(|((variable, aspect), args)| {
                            let InferType::Var(variable) = subst.apply(&InferType::Var(*variable))
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
            .collect()
    }

    fn resolve_paths(
        ctx: &InferContext,
        subst: &Substitution,
    ) -> HashMap<Span, super::type_engine::DefinitionPathFact> {
        let mut paths = ctx.definition_paths().clone();
        for (span, name, variable) in ctx.variant_deferrals() {
            let InferType::Named(_, _, identity) = subst.apply(&InferType::Var(*variable)) else {
                continue;
            };
            let Some(variant) = identity
                .get()
                .and_then(|id| ctx.registry().enum_info_by_id(id))
                .and_then(|info| {
                    info.variants
                        .iter()
                        .find(|variant| variant.name == *name && variant.fields.is_empty())
                })
                .and_then(|variant| variant.id)
            else {
                continue;
            };
            paths.insert(
                span.clone(),
                super::type_engine::DefinitionPathFact::UnitVariant(variant),
            );
        }
        paths
    }

    fn resolve_match_patterns(
        ctx: &InferContext,
        subst: &Substitution,
    ) -> HashMap<Span, super::type_engine::DefinitionMatchPattern> {
        ctx.definition_match_patterns()
            .iter()
            .map(|(span, fact)| {
                let mut resolved = fact.clone();
                for (_, _, _, ty) in &mut resolved.bindings {
                    *ty = subst.apply(ty);
                }
                (span.clone(), resolved)
            })
            .collect()
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

    pub(super) fn definition_path(
        &self,
        span: &Span,
    ) -> Option<&super::type_engine::DefinitionPathFact> {
        self.definition_paths.get(span)
    }

    pub(super) fn definition_array_length(&self, span: &Span) -> bool {
        self.definition_array_lengths.contains(span)
    }

    pub(super) fn definition_nominal_fields(&self) -> &HashMap<Span, crate::identity::FieldId> {
        &self.definition_nominal_fields
    }

    pub(super) fn definition_method_facts(&self) -> &HashMap<Span, DefinitionMethodFact> {
        &self.definition_method_facts
    }

    pub(super) fn definition_capture_type(&self, span: &Span) -> Option<&InferType> {
        self.definition_capture_types.get(span)
    }

    pub(super) fn definition_implicit_captures(
        &self,
        span: &Span,
    ) -> Option<&[super::type_engine::DefinitionImplicitCapture]> {
        self.definition_implicit_captures
            .get(span)
            .map(Vec::as_slice)
    }

    pub(super) fn definition_binding_type(&self, span: &Span) -> Option<&InferType> {
        self.definition_binding_types.get(span)
    }

    pub(super) fn definition_value_boundaries(&self, span: &Span) -> &[(InferType, InferType)] {
        self.definition_value_boundaries
            .get(span)
            .map_or(&[], Vec::as_slice)
    }

    pub(super) fn definition_record_shape(&self, span: &Span) -> Option<&InferType> {
        self.definition_record_shapes.get(span)
    }

    pub(super) fn definition_match_pattern(
        &self,
        span: &Span,
    ) -> Option<&super::type_engine::DefinitionMatchPattern> {
        self.definition_match_patterns.get(span)
    }

    pub(super) fn definition_template(
        &self,
        span: &Span,
    ) -> Option<&(
        super::type_engine::TypeScheme,
        Vec<crate::data::ast::GenericParam>,
    )> {
        self.definition_templates.get(span)
    }

    pub(super) fn definition_loop_diverges(&self, span: &Span) -> bool {
        self.definition_diverging_loops.contains(span)
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
