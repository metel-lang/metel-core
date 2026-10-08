//! `Display` for a record, the built-in body of `extend<row R> { ..R }: Display where all R:
//! Display` in `std::core` (RFC-0123, metel-core#1338).
//!
//! A host function cannot walk a row generically in Metel itself, so this stands in for the
//! `comptime for` loop of RFC-0174: it formats the receiver's fields in label order at
//! runtime, rendering each through that field's own `to_string` (a primitive directly, a
//! nested record recursively, any other type through its registered `Display` impl). The
//! static `where all R: Display` check has already guaranteed every field has one.
//! `LIMIT-TYPES-003` records this as a limitation to be replaced when RFC-0174 lands.

use crate::data::ast::Span;
use crate::data::error::{InternalErrorCode, MetelError};

use super::call::{ReceiverBinding, call_method_function};
use super::display::value_to_display_string;
use super::{ReceiverTypeArgs, RuntimeRegistry, Signal, Value, deref_value};

/// The label the `std::core` record `Display` impl's native is registered under.
pub(super) const RECORD_TO_STRING: &str = "std::core::record_to_string";

// limit: ["LIMIT-TYPES-003"]
pub(super) fn record_to_string(
    args: &[Value],
    span: &Span,
    runtime: &RuntimeRegistry,
) -> Result<Value, MetelError> {
    let receiver = args
        .first()
        .ok_or_else(|| MetelError::internal("record to_string: expected a receiver"))?;
    display_string(receiver, span, runtime).map(Value::Str)
}

fn display_string(
    value: &Value,
    span: &Span,
    runtime: &RuntimeRegistry,
) -> Result<String, MetelError> {
    let value = deref_value(value, span)?.unwrap_or_else(|| value.clone());
    if let Some(text) = value_to_display_string(&value) {
        return Ok(text);
    }
    if let Value::Record { fields, .. } = &value {
        return fields_string(None, fields.iter(), span, runtime);
    }
    // any other type: its own `Display` impl, found by the value
    if let Some(method) =
        runtime.get_method_for_value(&value, "to_string", &ReceiverTypeArgs::default())
    {
        let signal = call_method_function(
            method.body,
            ReceiverBinding::Value(value.clone()),
            vec![],
            None,
            None,
            None,
            span,
            runtime,
        )?;
        if let Signal::Value(Value::Str(text)) = signal {
            return Ok(text);
        }
    }
    // a nominal `record` with no `Display` of its own is shown by its fields, like the blanket
    if let Value::Struct { name, fields, .. } = &value {
        return fields_string(Some(name), fields.iter(), span, runtime);
    }
    Err(MetelError::internal_with_code(
        InternalErrorCode::I0006,
        "record to_string: a field does not implement Display",
    ))
}

fn fields_string<'a>(
    name: Option<&str>,
    fields: impl Iterator<Item = (&'a String, &'a Value)>,
    span: &Span,
    runtime: &RuntimeRegistry,
) -> Result<String, MetelError> {
    let mut pairs: Vec<_> = fields.collect();
    pairs.sort_by_key(|(label, _)| label.as_str());
    let inner = pairs
        .into_iter()
        .map(|(label, field)| {
            Ok(format!(
                "{label}: {}",
                display_string(field, span, runtime)?
            ))
        })
        .collect::<Result<Vec<_>, MetelError>>()?
        .join(", ");
    let body = if inner.is_empty() {
        "{}".to_string()
    } else {
        format!("{{ {inner} }}")
    };
    Ok(match name {
        Some(name) => format!("{name} {body}"),
        None => body,
    })
}
