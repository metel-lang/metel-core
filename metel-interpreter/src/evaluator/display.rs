use super::Value;

pub(super) fn format_float(f: f64) -> String {
    if f.fract() == 0.0 && f.is_finite() {
        format!("{}", f as i64)
    } else {
        f.to_string()
    }
}

pub(super) fn value_to_display_string(v: &Value) -> Option<String> {
    match v {
        Value::I64(n) => Some(n.to_string()),
        Value::F64(f) => Some(format_float(*f)),
        Value::Char(c) => Some(c.to_string()),
        Value::Boolean(b) => Some(if *b { "true" } else { "false" }.to_string()),
        Value::Str(s) => Some(s.clone()),
        Value::I8(n) => Some(n.to_string()),
        Value::I16(n) => Some(n.to_string()),
        Value::I32(n) => Some(n.to_string()),
        Value::U8(n) => Some(n.to_string()),
        Value::U16(n) => Some(n.to_string()),
        Value::U32(n) => Some(n.to_string()),
        Value::U64(n) => Some(n.to_string()),
        Value::F32(f) => Some(f.to_string()),
        _ => None,
    }
}

#[allow(clippy::too_many_lines)]
pub(super) fn format_value(val: &Value) -> String {
    match val {
        Value::I64(n) => n.to_string(),
        Value::F64(f) => f.to_string(),
        Value::Char(c) => format!("'{c}'"),
        Value::Boolean(b) => b.to_string(),
        Value::Str(s) => format!("{s:?}"),
        Value::Unit => "()".to_string(),
        Value::I8(n) => n.to_string(),
        Value::I16(n) => n.to_string(),
        Value::I32(n) => n.to_string(),
        Value::U8(n) => n.to_string(),
        Value::U16(n) => n.to_string(),
        Value::U32(n) => n.to_string(),
        Value::U64(n) => n.to_string(),
        Value::F32(f) => f.to_string(),
        Value::Tuple(items) => {
            let inner = items
                .iter()
                .map(format_value)
                .collect::<Vec<_>>()
                .join(", ");
            format!("({inner})")
        }
        Value::Array(arr) => {
            let inner = arr
                .borrow()
                .iter()
                .map(format_value)
                .collect::<Vec<_>>()
                .join(", ");
            format!("[{inner}]")
        }
        Value::Record { fields } => {
            let mut pairs: Vec<_> = fields.iter().collect();
            pairs.sort_by_key(|(k, _)| k.as_str());
            let inner = pairs
                .iter()
                .map(|(k, v)| format!("{k}: {}", format_value(v)))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{{ {inner} }}")
        }
        Value::Struct { name, fields, .. } => {
            let mut pairs: Vec<_> = fields.iter().collect();
            pairs.sort_by_key(|(k, _)| k.as_str());
            let inner = pairs
                .iter()
                .map(|(k, v)| format!("{}: {}", k, format_value(v)))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{name} {{ {inner} }}")
        }
        // Perhaps and Result use familiar Rust-style display rather than the generic enum format.
        // These are the only two enum names singled out by display — all others use the generic arm.
        // See ADR-0028 for why Perhaps/Result are represented as Value::Enum despite special display.
        Value::Enum {
            name,
            variant,
            fields,
            ..
        } if name == "Perhaps" => match (variant.as_str(), fields.get("value")) {
            ("Some", Some(v)) => format!("Some({})", format_value(v)),
            _ => "None".to_string(),
        },
        Value::Enum {
            name,
            variant,
            fields,
            ..
        } if name == "Result" => match variant.as_str() {
            "Ok" => format!(
                "Ok({})",
                format_value(fields.get("value").unwrap_or(&Value::Unit))
            ),
            _ => format!(
                "Err({})",
                format_value(fields.get("error").unwrap_or(&Value::Unit))
            ),
        },
        Value::Enum {
            name,
            variant,
            fields,
            ..
        } => {
            if fields.is_empty() {
                format!("{name}::{variant}")
            } else {
                let mut pairs: Vec<_> = fields.iter().collect();
                pairs.sort_by_key(|(k, _)| k.as_str());
                let inner = pairs
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, format_value(v)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{name}::{variant}{{ {inner} }}")
            }
        }
        Value::Callable(super::RuntimeCallable::Closure(_)) => "<closure>".to_string(),
        Value::Callable(super::RuntimeCallable::Intrinsic { label, .. }) => {
            format!("<intrinsic:{label}>")
        }
        Value::Reference(rc) => format!("&{}", format_value(&rc.borrow())),
        Value::MutReference(rc) => format!("&var {}", format_value(&rc.borrow())),
        Value::FieldReference { .. } => "<& field-path>".to_string(),
        Value::MutFieldReference { .. } => "<&var field-path>".to_string(),
        // A `dyn Aspect` value displays as whatever it actually is underneath —
        // the erasure is a typechecking-time fiction, not a runtime one; the
        // wrapped concrete value is real and unambiguous.
        Value::DynAspect { data, .. } => format_value(&data.borrow()),
    }
}

#[cfg(test)]
mod tests;
