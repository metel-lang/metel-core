//! `Clone` for records, the built-in body of `extend<record R> { ..R }: Clone where
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
            // An anonymous record's fields are visited in lexicographic label order.
            fields: clone_fields(fields, None, span, runtime)?,
            type_id: *type_id,
        }),
        Value::Struct {
            name,
            type_id,
            fields,
        } => Ok(Value::Struct {
            name: name.clone(),
            type_id: *type_id,
            fields: clone_fields(
                fields,
                type_id.and_then(|id| runtime.clone_order_of(id, None)),
                span,
                runtime,
            )?,
        }),
        // `derives Clone` on an enum (RFC-0207): the clone keeps the active variant and clones its payload.
        Value::Enum {
            name,
            type_id,
            variant,
            variant_id,
            fields,
        } => Ok(Value::Enum {
            name: name.clone(),
            type_id: *type_id,
            variant: variant.clone(),
            variant_id: *variant_id,
            fields: clone_fields(
                fields,
                type_id.and_then(|id| runtime.clone_order_of(id, Some(variant))),
                span,
                runtime,
            )?,
        }),
        _ => Err(MetelError::internal(
            "record clone: receiver is not a record",
        )),
    }
}

/// Clone `fields` one at a time, in `order` (the declaration order of a derived `Clone`) and then in
/// label order for any label it does not name, so an inner `clone` with an effect always runs in the
/// same sequence (metel-core#1817).
fn clone_fields(
    fields: &std::collections::HashMap<String, Value>,
    order: Option<&[String]>,
    span: &Span,
    runtime: &RuntimeRegistry,
) -> Result<std::collections::HashMap<String, Value>, MetelError> {
    let mut visit: Vec<&String> = order.unwrap_or_default().iter().collect();
    let mut rest: Vec<&String> = fields.keys().filter(|k| !visit.contains(k)).collect();
    rest.sort();
    visit.extend(rest);
    visit
        .into_iter()
        .filter_map(|label| fields.get(label).map(|value| (label, value)))
        .map(|(label, value)| {
            // A shared reference is `Clone` for every referent: the clone is another reference.
            if matches!(value, Value::Reference(_) | Value::FieldReference { .. }) {
                return Ok((label.clone(), value.clone()));
            }
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

/// The `Clone` the compiler provides for a value of a kind with no impl block to write it in (RFC-0206
/// section 2): the unit value, a tuple (each part cloned in order, left to right) and a closure (a `Copy`
/// closure is its own clone). `None` for any other value.
pub(super) fn provided_clone(
    value: &Value,
    span: &Span,
    runtime: &RuntimeRegistry,
) -> Result<Option<Value>, MetelError> {
    match value {
        Value::Unit | Value::Callable(_) => Ok(Some(value.clone())),
        Value::Tuple(items) => {
            let mut cloned = Vec::with_capacity(items.len());
            for item in items {
                cloned.push(clone_value(item, span, runtime)?);
            }
            Ok(Some(Value::Tuple(cloned)))
        }
        _ => Ok(None),
    }
}

/// Clone one value: a shared reference is copied, a provided kind clones itself, anything else through its
/// own `clone` method.
fn clone_value(value: &Value, span: &Span, runtime: &RuntimeRegistry) -> Result<Value, MetelError> {
    if matches!(value, Value::Reference(_) | Value::FieldReference { .. }) {
        return Ok(value.clone());
    }
    if let Some(cloned) = provided_clone(value, span, runtime)? {
        return Ok(cloned);
    }
    let method = clone_method(value, span, runtime).ok_or_else(|| {
        MetelError::internal("provided clone: a part has no Clone implementation")
    })?;
    match call_method_function(
        method.body,
        ReceiverBinding::Value(value.clone()),
        vec![],
        None,
        None,
        None,
        span,
        runtime,
    )? {
        Signal::Value(cloned) => Ok(cloned),
        _ => Err(MetelError::internal(
            "provided clone: a part did not return a value",
        )),
    }
}
