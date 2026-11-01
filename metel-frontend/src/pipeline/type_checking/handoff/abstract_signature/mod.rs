//! Solved signatures, declared facts and body operations frozen into abstract types.

use std::collections::HashMap;

use crate::data::abstract_body::{
    AbstractParameter, AbstractParameterId, AbstractSignature, AbstractType,
};
use crate::data::ast::Span;
use crate::data::error::MetelError;
use crate::identity::BindingId;
use crate::pipeline::type_checking::type_engine::{InferType, TypeScheme, TypeVar};

#[derive(Clone)]
pub(super) struct SignatureFreezer<'a> {
    variables: HashMap<TypeVar, AbstractParameterId>,
    names: HashMap<&'a str, AbstractParameterId>,
    span: &'a Span,
    /// Body-local type variables, when the freezer is freezing a body: a variable that is not one
    /// of the signature's own (the instantiation of a polymorphic local closure, say) is an
    /// unconstrained type of this body, not an internal error.
    locals: Option<LocalParameters>,
}

/// The variables of a body that its signature does not quantify, numbered after the signature's own
/// parameters. Shared by every freezer of the one body, including its closures'.
#[derive(Clone)]
pub(super) struct LocalParameters {
    binder: BindingId,
    first_index: usize,
    variables: std::rc::Rc<std::cell::RefCell<Vec<TypeVar>>>,
}

impl LocalParameters {
    pub(super) fn new(binder: BindingId, first_index: usize) -> Self {
        Self {
            binder,
            first_index,
            variables: std::rc::Rc::default(),
        }
    }

    fn parameter(&self, variable: TypeVar) -> AbstractParameterId {
        let mut variables = self.variables.borrow_mut();
        let position = variables
            .iter()
            .position(|known| *known == variable)
            .unwrap_or_else(|| {
                variables.push(variable);
                variables.len() - 1
            });
        AbstractParameterId {
            binder: self.binder,
            index: self.first_index + position,
        }
    }

    /// The ids of the variables met so far, in numbering order.
    pub(super) fn ids(&self) -> Vec<AbstractParameterId> {
        (0..self.variables.borrow().len())
            .map(|position| AbstractParameterId {
                binder: self.binder,
                index: self.first_index + position,
            })
            .collect()
    }
}

/// The scheme is already solved/generalized. Freezing must not substitute a caller's
/// concrete arguments, or an unused definition would acquire different semantics.
pub(in crate::pipeline::type_checking) fn freeze_signature(
    scheme: &TypeScheme,
    binder: BindingId,
    source_order: &[&str],
    span: &Span,
) -> Result<AbstractSignature, MetelError> {
    let variables = ordered_variables(scheme, source_order);
    let parameters: Vec<_> = variables
        .iter()
        .enumerate()
        .map(|(index, variable)| AbstractParameter {
            id: AbstractParameterId { binder, index },
            name: scheme
                .quantified_vars
                .iter()
                .position(|var| var == variable)
                .and_then(|position| scheme.param_names.get(position))
                .cloned(),
        })
        .collect();
    let freezer = SignatureFreezer {
        variables: variables
            .iter()
            .copied()
            .zip(parameters.iter().map(|parameter| parameter.id))
            .collect(),
        names: parameters
            .iter()
            .filter_map(|parameter| parameter.name.as_deref().map(|name| (name, parameter.id)))
            .collect(),
        span,
        locals: None,
    };
    let ty = freezer.freeze(&scheme.ty)?;
    Ok(AbstractSignature {
        binder,
        parameters,
        ty,
        facts: None,
    })
}

fn ordered_variables(scheme: &TypeScheme, source_order: &[&str]) -> Vec<TypeVar> {
    let mut ordered = Vec::new();
    for name in source_order {
        if let Some(position) = scheme
            .param_names
            .iter()
            .position(|candidate| candidate == name)
            && let Some(variable) = scheme.quantified_vars.get(position)
            && !ordered.contains(variable)
        {
            ordered.push(*variable);
        }
    }
    signature_variables(&scheme.ty, scheme, &mut ordered);
    // Variables absent from the signature have no structural signature origin.
    // Their body/fact origins must be supplied by the later abstract-body handoff.
    // Preserve their current metadata rather than pretending it proves completeness.
    let mut remaining: Vec<_> = scheme
        .quantified_vars
        .iter()
        .enumerate()
        .filter(|(_, variable)| !ordered.contains(variable))
        .collect();
    remaining.sort_by_key(|(index, _)| scheme.param_names.get(*index));
    ordered.extend(remaining.into_iter().map(|(_, variable)| *variable));
    ordered
}

fn signature_variables(ty: &InferType, scheme: &TypeScheme, ordered: &mut Vec<TypeVar>) {
    match ty {
        InferType::Var(variable) => {
            if scheme.quantified_vars.contains(variable) && !ordered.contains(variable) {
                ordered.push(*variable);
            }
        }
        InferType::Named(name, arguments, identity) => {
            if arguments.is_empty()
                && identity.0.is_none()
                && let Some(index) = scheme
                    .param_names
                    .iter()
                    .position(|candidate| candidate == name)
                && let Some(variable) = scheme.quantified_vars.get(index)
                && !ordered.contains(variable)
            {
                ordered.push(*variable);
            }
            for argument in arguments {
                signature_variables(argument, scheme, ordered);
            }
        }
        InferType::Fun(parameters, result, ..) => {
            for parameter in parameters {
                signature_variables(parameter, scheme, ordered);
            }
            signature_variables(result, scheme, ordered);
        }
        InferType::Tuple(items) => {
            for item in items {
                signature_variables(item, scheme, ordered);
            }
        }
        InferType::Record(fields) | InferType::Residual { fields, .. } => {
            for (_, ty) in fields {
                signature_variables(ty, scheme, ordered);
            }
        }
        InferType::RowExtend { fields, tail } => {
            for (_, ty) in fields {
                signature_variables(ty, scheme, ordered);
            }
            signature_variables(tail, scheme, ordered);
        }
        InferType::RowView(inner)
        | InferType::Array(inner)
        | InferType::SizedArray(inner, _)
        | InferType::Reference(inner)
        | InferType::MutReference(inner) => {
            signature_variables(inner, scheme, ordered);
        }
        InferType::Dyn { type_args, .. } => {
            for argument in type_args {
                signature_variables(argument, scheme, ordered);
            }
        }
        InferType::Concrete(_) | InferType::Never => {}
    }
}

impl SignatureFreezer<'_> {
    fn fields(
        &self,
        fields: &[(String, InferType)],
    ) -> Result<Vec<(String, AbstractType)>, MetelError> {
        fields
            .iter()
            .map(|(label, ty)| self.freeze(ty).map(|ty| (label.clone(), ty)))
            .collect()
    }

    fn items(&self, items: &[InferType]) -> Result<Vec<AbstractType>, MetelError> {
        items.iter().map(|ty| self.freeze(ty)).collect()
    }

    pub(super) fn freeze(&self, ty: &InferType) -> Result<AbstractType, MetelError> {
        Ok(match ty {
            InferType::Concrete(ty) => AbstractType::Concrete(ty.clone()),
            InferType::Var(var) => {
                AbstractType::Parameter(match (self.variables.get(var), &self.locals) {
                    (Some(id), _) => *id,
                    (None, Some(locals)) => locals.parameter(*var),
                    (None, None) => {
                        return Err(MetelError::internal(format!(
                            "abstract signature contains an unquantified variable at {}:{}:{}",
                            self.span.filename, self.span.line, self.span.col
                        )));
                    }
                })
            }
            InferType::Never => AbstractType::Never,
            InferType::Fun(parameters, result, call, usage, mutation) => AbstractType::Function {
                parameters: self.items(parameters)?,
                result: Box::new(self.freeze(result)?),
                call: *call,
                usage: *usage,
                mutation: *mutation,
            },
            InferType::Tuple(items) => AbstractType::Tuple(self.items(items)?),
            InferType::Record(fields) => AbstractType::Record(self.fields(fields)?),
            InferType::RowView(tail) => AbstractType::OpenRecord {
                fields: Vec::new(),
                tail: Box::new(self.freeze(tail)?),
            },
            InferType::RowExtend { fields, tail } if fields.is_empty() => self.freeze(tail)?,
            InferType::RowExtend { fields, tail } => AbstractType::OpenRecord {
                fields: self.fields(fields)?,
                tail: Box::new(self.freeze(match tail.as_ref() {
                    InferType::RowView(source) => source,
                    other => other,
                })?),
            },
            InferType::Array(inner) => AbstractType::Array(Box::new(self.freeze(inner)?)),
            InferType::SizedArray(inner, len) => {
                AbstractType::SizedArray(Box::new(self.freeze(inner)?), *len)
            }
            InferType::Reference(inner) => AbstractType::Reference(Box::new(self.freeze(inner)?)),
            InferType::MutReference(inner) => {
                AbstractType::MutReference(Box::new(self.freeze(inner)?))
            }
            InferType::Named(name, arguments, identity) => {
                if arguments.is_empty()
                    && identity.0.is_none()
                    && let Some(parameter) = self.names.get(name.as_str())
                {
                    AbstractType::Parameter(*parameter)
                } else {
                    AbstractType::Named {
                        name: name.clone(),
                        arguments: self.items(arguments)?,
                        identity: identity.clone(),
                    }
                }
            }
            InferType::Residual { brand, fields } => AbstractType::Residual {
                brand: brand.clone(),
                fields: self.fields(fields)?,
            },
            InferType::Dyn { aspect, type_args } => AbstractType::Dyn {
                aspect: aspect.clone(),
                arguments: self.items(type_args)?,
            },
        })
    }
}

#[cfg(test)]
mod tests;

mod facts;
pub(in crate::pipeline::type_checking) use facts::freeze_declaration_signature;

mod body;
pub(in crate::pipeline::type_checking) use body::prepare_abstract_body;

mod nested;
pub(in crate::pipeline::type_checking) use nested::nested_functions;
