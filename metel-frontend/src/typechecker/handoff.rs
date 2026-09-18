use std::collections::HashMap;

use crate::ast::Span;
use crate::error::MetelError;
use crate::typeinference::{InferContext, Substitution, free_vars};
use crate::types::Type;

use super::conversions::infer_type_to_type;

/// Immutable facts decided by inference and consumed while building the typed AST.
///
/// Keeping this boundary concrete prevents construction from depending on inference
/// variables or from independently resolving decisions that Pass 1 already made.
pub(super) struct ResolvedInferenceFacts {
    closure_return_types: HashMap<Span, Type>,
}

impl ResolvedInferenceFacts {
    pub(super) fn empty() -> Self {
        Self {
            closure_return_types: HashMap::new(),
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
        })
    }

    pub(super) fn closure_return_type(&self, span: &Span) -> Option<&Type> {
        self.closure_return_types.get(span)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typeinference::{InferType, TypeDefinitionRegistry, TypeVar, TypeVarGenerator};

    fn context_with_closure(span: Span, ty: InferType) -> InferContext {
        let mut ctx = InferContext::new(
            TypeDefinitionRegistry::default(),
            TypeVarGenerator::new(),
            &HashMap::new(),
            vec![],
        );
        ctx.record_closure_return_type(span, ty);
        ctx
    }

    #[test]
    fn resolves_closure_return_types_before_construction() {
        let span = Span::new(4, 12, "handoff.mtl");
        let var = TypeVar(7);
        let ctx = context_with_closure(span.clone(), InferType::Var(var));
        let mut subst = Substitution::new();
        subst.bind(var, InferType::int());

        let facts = ResolvedInferenceFacts::resolve(&ctx, &subst).unwrap();

        assert_eq!(facts.closure_return_type(&span), Some(&Type::I64));
    }

    #[test]
    fn omits_polymorphic_closure_facts_resolved_per_call_site() {
        let span = Span::new(4, 12, "handoff.mtl");
        let ctx = context_with_closure(span.clone(), InferType::Var(TypeVar(7)));

        let facts = ResolvedInferenceFacts::resolve(&ctx, &Substitution::new()).unwrap();

        assert_eq!(facts.closure_return_type(&span), None);
    }
}
