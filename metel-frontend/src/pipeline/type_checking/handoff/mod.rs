use std::collections::HashMap;

use crate::data::ast::Span;
use crate::data::error::MetelError;
use crate::data::types::Type;
use crate::pipeline::type_checking::typeinference::{InferContext, Substitution, free_vars};

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
mod tests;
