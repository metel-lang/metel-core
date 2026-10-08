//! `Clone` for records, the built-in body of `extend<row R> { ..R }: Clone where
//! all R: Clone` in `std::core` (metel-core#1350).
//!
//! A host function is used until RFC-0174's compile-time row iteration can express
//! this operation in Metel itself. The typechecker has already verified the
//! all-fields Clone bound; the runtime only performs the recursive value copy.

use crate::data::ast::Span;
use crate::data::error::MetelError;

use super::call::{ReceiverBinding, call_method_function};
use super::{ReceiverTypeArgs, RuntimeRegistry, Signal, Value, type_of};

/// The label the `std::core` record Clone implementation is registered under.
pub(super) const RECORD_CLONE: &str = "std::core::record_clone";

pub(super) fn record_clone(
    args: &[Value],
    span: &Span,
    runtime: &RuntimeRegistry,
) -> Result<Value, MetelError> {
    let receiver = args
        .first()
        .ok_or_else(|| MetelError::internal("record clone: expected a receiver"))?;
    match receiver {
        Value::Record { fields, type_id } => Ok(Value::Record {
            fields: clone_fields(fields, span, runtime)?,
            type_id: *type_id,
        }),
        Value::Struct {
            name,
            type_id,
            fields,
        } => Ok(Value::Struct {
            name: name.clone(),
            type_id: *type_id,
            fields: clone_fields(fields, span, runtime)?,
        }),
        _ => Err(MetelError::internal(
            "record clone: receiver is not a record",
        )),
    }
}

fn clone_fields(
    fields: &std::collections::HashMap<String, Value>,
    span: &Span,
    runtime: &RuntimeRegistry,
) -> Result<std::collections::HashMap<String, Value>, MetelError> {
    fields
        .iter()
        .map(|(label, value)| {
            let method = clone_method(value, span, runtime).ok_or_else(|| {
                MetelError::internal(format!(
                    "record clone: field `{label}` has no Clone implementation"
                ))
            })?;
            let cloned = call_method_function(
                method.body,
                ReceiverBinding::Value(value.clone()),
                vec![],
                None,
                None,
                None,
                span,
                runtime,
            )?;
            let Signal::Value(cloned) = cloned else {
                return Err(MetelError::internal(format!(
                    "record clone: field `{label}` did not return a value"
                )));
            };
            Ok((label.clone(), cloned))
        })
        .collect()
}

fn clone_method(
    value: &Value,
    span: &Span,
    runtime: &RuntimeRegistry,
) -> Option<super::RuntimeMethod> {
    runtime
        .get_method_for_value(value, "clone", &ReceiverTypeArgs::default())
        .or_else(|| {
            let Value::Struct { fields, .. } = value else {
                return None;
            };
            let registry =
                crate::pipeline::type_checking::type_engine::TypeDefinitionRegistry::new();
            let mut row: Vec<(String, crate::data::types::Type)> = fields
                .iter()
                .map(|(label, field)| {
                    (
                        label.clone(),
                        type_of::value_to_type(field, &registry, span),
                    )
                })
                .collect();
            row.sort_by(|a, b| a.0.cmp(&b.0));
            runtime.get_record_aspect_method(
                None,
                "clone",
                &ReceiverTypeArgs {
                    names: vec![],
                    tys: vec![crate::data::types::Type::Record(row)],
                    prefer: None,
                },
            )
        })
}
