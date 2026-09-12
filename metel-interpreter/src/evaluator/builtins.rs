// clippy-allow: a handful of `native_*` functions here (native_clock,
// native_list_new, native_env_vars, native_process_args, ...) never actually
// fail, but all native functions share the fixed `NativeFn` signature
// (`-> Result<Value, MetelError>`) required for uniform dispatch through
// `NativeKey`, so their `Result` wrapping cannot be dropped per function.
// Narrowing or removing this module-level allow is tracked by metel-core#889.
#![allow(clippy::unnecessary_wraps)]

use crate::error::{MetelError, RuntimeErrorCode};

use super::display::{format_value, value_to_display_string};
use super::{
    NativeFn, RuntimeCallable, RuntimeMethod, RuntimeRegistry, RuntimeSignature,
    RuntimeTypePattern, RuntimeTypeRef, Value,
};

fn numeric_as_i128(v: &Value) -> Option<i128> {
    match v {
        Value::I8(n) => Some(i128::from(*n)),
        Value::I16(n) => Some(i128::from(*n)),
        Value::I32(n) => Some(i128::from(*n)),
        Value::I64(n) => Some(i128::from(*n)),
        Value::U8(n) => Some(i128::from(*n)),
        Value::U16(n) => Some(i128::from(*n)),
        Value::U32(n) => Some(i128::from(*n)),
        Value::U64(n) => Some(i128::from(*n)),
        Value::F32(f) => Some(*f as i128),
        Value::F64(f) => Some(*f as i128),
        _ => None,
    }
}

fn numeric_as_f64_val(v: &Value) -> Option<f64> {
    match v {
        Value::I8(n) => Some(f64::from(*n)),
        Value::I16(n) => Some(f64::from(*n)),
        Value::I32(n) => Some(f64::from(*n)),
        Value::I64(n) => Some(*n as f64),
        Value::U8(n) => Some(f64::from(*n)),
        Value::U16(n) => Some(f64::from(*n)),
        Value::U32(n) => Some(f64::from(*n)),
        Value::U64(n) => Some(*n as f64),
        Value::F32(f) => Some(f64::from(*f)),
        Value::F64(f) => Some(*f),
        _ => None,
    }
}

// ── Native host implementations (METEL-182) ────────────────────────────────
// Each stdlib `native(@…)` function dispatches to the matching host fn here,
// selected by its `NativeKey`. These mirror the legacy `register_core!`
// builtins and replace them once `std::core` is a real module (METEL-181).

use crate::native_keys::NativeKey;

fn native_print(args: &[Value], span: &crate::ast::Span) -> Result<Value, MetelError> {
    let v = args
        .first()
        .ok_or_else(|| MetelError::internal("print: expected one argument"))?;
    let s = value_to_display_string(v).ok_or_else(|| {
        MetelError::panic(
            RuntimeErrorCode::R0009,
            "print: value does not implement Display",
            span,
        )
    })?;
    print!("{s}");
    Ok(Value::Unit)
}

fn native_println(args: &[Value], span: &crate::ast::Span) -> Result<Value, MetelError> {
    let v = args
        .first()
        .ok_or_else(|| MetelError::internal("println: expected one argument"))?;
    let s = value_to_display_string(v).ok_or_else(|| {
        MetelError::panic(
            RuntimeErrorCode::R0009,
            "println: value does not implement Display",
            span,
        )
    })?;
    println!("{s}");
    Ok(Value::Unit)
}

fn native_dbg(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    match args.first() {
        Some(val) => {
            eprintln!("[dbg] {}", format_value(val));
            Ok(val.clone())
        }
        None => Err(MetelError::internal("dbg: expected one argument")),
    }
}

fn native_assert(args: &[Value], span: &crate::ast::Span) -> Result<Value, MetelError> {
    match args.first() {
        Some(Value::Boolean(true)) => Ok(Value::Unit),
        Some(Value::Boolean(false)) => Err(MetelError::panic(
            RuntimeErrorCode::R0012,
            "assertion failed",
            span,
        )),
        _ => Err(MetelError::internal("assert: expected boolean argument")),
    }
}

fn native_assert_msg(args: &[Value], span: &crate::ast::Span) -> Result<Value, MetelError> {
    match (args.first(), args.get(1)) {
        (Some(Value::Boolean(true)), _) => Ok(Value::Unit),
        (Some(Value::Boolean(false)), Some(Value::Str(msg))) => Err(MetelError::panic(
            RuntimeErrorCode::R0012,
            msg.clone(),
            span,
        )),
        (Some(Value::Boolean(false)), _) => Err(MetelError::panic(
            RuntimeErrorCode::R0012,
            "assertion failed",
            span,
        )),
        _ => Err(MetelError::internal(
            "assert_msg: expected (boolean, String) arguments",
        )),
    }
}

/// `Perhaps::yolo()`'s `None` arm. Always panics — there is no value to report,
/// unlike `yolo_err` below. Its declared return type `T` is resolved at each call
/// site from the enclosing function's declared return type (see
/// `construct_call`'s bare-identifier branch in `src/typechecker/construction.rs`,
/// which falls back to `instantiate_scheme_with_expected_ret` when arg-based
/// instantiation leaves a free type variable).
fn native_yolo_none(_args: &[Value], span: &crate::ast::Span) -> Result<Value, MetelError> {
    Err(MetelError::panic(
        RuntimeErrorCode::R0013,
        "called `.yolo()` on a `None` value",
        span,
    ))
}

/// `Result::yolo()`'s `Err` arm. Always panics, including the `Err` value's debug
/// representation via `format_value` — the same formatter `dbg` uses — so this
/// needs no `E: Display` bound on the caller (not even expressible today; `impl`
/// blocks have no per-method bounds syntax).
fn native_yolo_err(args: &[Value], span: &crate::ast::Span) -> Result<Value, MetelError> {
    match args.first() {
        Some(error) => Err(MetelError::panic(
            RuntimeErrorCode::R0013,
            format!(
                "called `.yolo()` on an `Err` value: {}",
                format_value(error)
            ),
            span,
        )),
        None => Err(MetelError::internal("yolo_err: expected one argument")),
    }
}

/// `std::core::panic(msg: String) -> !` (RFC-0078). Always panics with `msg`.
fn native_panic(args: &[Value], span: &crate::ast::Span) -> Result<Value, MetelError> {
    match args.first() {
        Some(Value::Str(msg)) => Err(MetelError::panic(
            RuntimeErrorCode::R0014,
            msg.clone(),
            span,
        )),
        _ => Err(MetelError::internal("panic: expected one String argument")),
    }
}

fn native_clock(_args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    use std::time::{SystemTime, UNIX_EPOCH};
    let ms = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as i64;
    Ok(Value::I64(ms))
}

fn native_string_len(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    match args.first() {
        Some(Value::Str(s)) => Ok(Value::I64(s.chars().count() as i64)),
        _ => Err(MetelError::internal("string_len: expected String argument")),
    }
}

// ── std::core String utilities (METEL-193) ─────────────────────────────────
// Index-based operations are in Unicode scalars (consistent with len) and total:
// out-of-range indices clamp or yield None. The receiver String arrives as the
// first argument (the method-call path inserts it ahead of the explicit args).

fn i64_at(args: &[Value], idx: usize, label: &str) -> Result<i64, MetelError> {
    match args.get(idx) {
        Some(Value::I64(n)) => Ok(*n),
        _ => Err(MetelError::internal(format!(
            "{label}: expected an i64 argument at position {idx}"
        ))),
    }
}

fn string_array_value(strings: Vec<String>) -> Value {
    use std::cell::RefCell;
    use std::rc::Rc;
    Value::Array(Rc::new(RefCell::new(
        strings.into_iter().map(Value::Str).collect(),
    )))
}

fn native_string_is_empty(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    Ok(Value::Boolean(
        str_at(args, 0, "string_is_empty")?.is_empty(),
    ))
}

fn native_string_to_upper(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    Ok(Value::Str(
        str_at(args, 0, "string_to_upper")?.to_uppercase(),
    ))
}

fn native_string_to_lower(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    Ok(Value::Str(
        str_at(args, 0, "string_to_lower")?.to_lowercase(),
    ))
}

fn native_string_trim(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    Ok(Value::Str(
        str_at(args, 0, "string_trim")?.trim().to_string(),
    ))
}

fn native_string_trim_start(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    Ok(Value::Str(
        str_at(args, 0, "string_trim_start")?
            .trim_start()
            .to_string(),
    ))
}

fn native_string_trim_end(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    Ok(Value::Str(
        str_at(args, 0, "string_trim_end")?.trim_end().to_string(),
    ))
}

fn native_string_contains(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let s = str_at(args, 0, "string_contains")?;
    let needle = str_at(args, 1, "string_contains")?;
    Ok(Value::Boolean(s.contains(&needle)))
}

fn native_string_starts_with(
    args: &[Value],
    _span: &crate::ast::Span,
) -> Result<Value, MetelError> {
    let s = str_at(args, 0, "string_starts_with")?;
    let prefix = str_at(args, 1, "string_starts_with")?;
    Ok(Value::Boolean(s.starts_with(&prefix)))
}

fn native_string_ends_with(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let s = str_at(args, 0, "string_ends_with")?;
    let suffix = str_at(args, 1, "string_ends_with")?;
    Ok(Value::Boolean(s.ends_with(&suffix)))
}

fn native_string_index_of(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let s = str_at(args, 0, "string_index_of")?;
    let needle = str_at(args, 1, "string_index_of")?;
    // Convert the byte offset of the match to a scalar (char) index.
    let found = s
        .find(&needle)
        .map(|byte_idx| Value::I64(s[..byte_idx].chars().count() as i64));
    Ok(perhaps_value(found))
}

fn native_string_split(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let s = str_at(args, 0, "string_split")?;
    let sep = str_at(args, 1, "string_split")?;
    let parts: Vec<String> = if sep.is_empty() {
        vec![s]
    } else {
        s.split(sep.as_str()).map(str::to_string).collect()
    };
    Ok(string_array_value(parts))
}

fn native_string_replace(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let s = str_at(args, 0, "string_replace")?;
    let from = str_at(args, 1, "string_replace")?;
    let to = str_at(args, 2, "string_replace")?;
    Ok(Value::Str(s.replace(from.as_str(), to.as_str())))
}

fn native_string_repeat(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let s = str_at(args, 0, "string_repeat")?;
    let n = i64_at(args, 1, "string_repeat")?;
    Ok(Value::Str(if n <= 0 {
        String::new()
    } else {
        s.repeat(n as usize)
    }))
}

fn native_string_join(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let parts: Vec<String> = match args.first() {
        Some(Value::Array(arr)) => arr
            .borrow()
            .iter()
            .map(|v| match v {
                Value::Str(s) => Ok(s.clone()),
                _ => Err(MetelError::internal(
                    "String::join: parts array must contain Strings",
                )),
            })
            .collect::<Result<_, _>>()?,
        _ => {
            return Err(MetelError::internal(
                "String::join: expected (String[], String)",
            ))
        }
    };
    let sep = str_at(args, 1, "String::join")?;
    Ok(Value::Str(parts.join(sep.as_str())))
}

fn native_string_chars(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    use std::cell::RefCell;
    use std::rc::Rc;
    let s = str_at(args, 0, "string_chars")?;
    let chars: Vec<Value> = s.chars().map(Value::Char).collect();
    Ok(Value::Array(Rc::new(RefCell::new(chars))))
}

fn native_string_char_at(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let s = str_at(args, 0, "string_char_at")?;
    let i = i64_at(args, 1, "string_char_at")?;
    let found = if i < 0 {
        None
    } else {
        s.chars().nth(i as usize).map(Value::Char)
    };
    Ok(perhaps_value(found))
}

fn native_string_substring(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let s = str_at(args, 0, "string_substring")?;
    let chars: Vec<char> = s.chars().collect();
    let len = chars.len() as i64;
    let start = i64_at(args, 1, "string_substring")?.clamp(0, len) as usize;
    let end = i64_at(args, 2, "string_substring")?.clamp(0, len) as usize;
    let sub: String = if start < end {
        chars[start..end].iter().collect()
    } else {
        String::new()
    };
    Ok(Value::Str(sub))
}

// `Display::to_string` for every displayable primitive: one host fn formats the
// receiver by its runtime value, so all 13 std::core impls share one NativeKey.
fn native_to_string(args: &[Value], span: &crate::ast::Span) -> Result<Value, MetelError> {
    match args.first() {
        Some(v) => value_to_display_string(v).map(Value::Str).ok_or_else(|| {
            MetelError::panic(
                RuntimeErrorCode::R0009,
                "to_string: value does not implement Display",
                span,
            )
        }),
        None => Err(MetelError::internal("to_string: expected a receiver")),
    }
}

// Numeric `From` conversions. The source type is encoded in the value itself,
// so one host fn per TARGET covers its whole From<…> impl family. Integer
// targets truncate through i128, float targets convert through f64 — the same
// semantics as the per-pair builtins these replace.
macro_rules! native_int_from {
    ($fn_name:ident, $label:literal, $out:expr) => {
        fn $fn_name(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
            match args.first().and_then(numeric_as_i128) {
                Some(n) => Ok($out(n)),
                None => Err(MetelError::internal(concat!(
                    $label,
                    "::from: expected a numeric argument"
                ))),
            }
        }
    };
}
macro_rules! native_float_from {
    ($fn_name:ident, $label:literal, $out:expr) => {
        fn $fn_name(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
            match args.first().and_then(numeric_as_f64_val) {
                Some(f) => Ok($out(f)),
                None => Err(MetelError::internal(concat!(
                    $label,
                    "::from: expected a numeric argument"
                ))),
            }
        }
    };
}
native_int_from!(native_i8_from, "i8", |n: i128| Value::I8(n as i8));
native_int_from!(native_i16_from, "i16", |n: i128| Value::I16(n as i16));
native_int_from!(native_i32_from, "i32", |n: i128| Value::I32(n as i32));
native_int_from!(native_i64_from, "i64", |n: i128| Value::I64(n as i64));
native_int_from!(native_u8_from, "u8", |n: i128| Value::U8(n as u8));
native_int_from!(native_u16_from, "u16", |n: i128| Value::U16(n as u16));
native_int_from!(native_u64_from, "u64", |n: i128| Value::U64(n as u64));
native_float_from!(native_f32_from, "f32", |f: f64| Value::F32(f as f32));
native_float_from!(native_f64_from, "f64", |f: f64| Value::F64(f));

// u32 additionally accepts a Char (its Unicode code point).
fn native_u32_from(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    match args.first() {
        Some(Value::Char(c)) => Ok(Value::U32(*c as u32)),
        Some(v) => match numeric_as_i128(v) {
            Some(n) => Ok(Value::U32(n as u32)),
            None => Err(MetelError::internal(
                "u32::from: expected a numeric or Char argument",
            )),
        },
        None => Err(MetelError::internal("u32::from: expected an argument")),
    }
}

fn native_char_from(args: &[Value], span: &crate::ast::Span) -> Result<Value, MetelError> {
    match args.first() {
        Some(Value::U32(n)) => char::from_u32(*n).map(Value::Char).ok_or_else(|| {
            MetelError::panic(
                RuntimeErrorCode::R0009,
                format!("u32 value {n} is not a valid Unicode scalar"),
                span,
            )
        }),
        _ => Err(MetelError::internal("Char::from: expected a u32 argument")),
    }
}

// ── List<T> host implementations ────────────────────────────────────────────
// List<T> is represented as Value::Struct { name: "List", fields: { "inner":
// Value::Array(rc) } }; the methods operate on the shared backing array.

fn list_value(backing: Vec<Value>) -> Value {
    use std::cell::RefCell;
    use std::rc::Rc;
    let mut fields = std::collections::HashMap::new();
    fields.insert(
        "inner".to_string(),
        Value::Array(Rc::new(RefCell::new(backing))),
    );
    Value::Struct {
        name: "List".to_string(),
        type_id: Some(crate::symbols::SYM_TYPE_LIST),
        fields,
    }
}

fn perhaps_value(v: Option<Value>) -> Value {
    match v {
        Some(val) => {
            let mut f = std::collections::HashMap::new();
            f.insert("value".to_string(), val);
            Value::Enum {
                name: "Perhaps".to_string(),
                type_id: Some(crate::symbols::SYM_TYPE_PERHAPS),
                variant: "Some".to_string(),
                // Well-known builtin, not user-declarable under this fixed
                // SymbolId, so the name-based match fallback (#1128) carries
                // no cross-module collision risk here.
                variant_id: None,
                fields: f,
            }
        }
        None => Value::Enum {
            name: "Perhaps".to_string(),
            type_id: Some(crate::symbols::SYM_TYPE_PERHAPS),
            variant: "None".to_string(),
            variant_id: None,
            fields: std::collections::HashMap::new(),
        },
    }
}

fn list_inner(
    args: &[Value],
    label: &str,
) -> Result<std::rc::Rc<std::cell::RefCell<Vec<Value>>>, MetelError> {
    match args.first() {
        Some(Value::Struct { name, fields, .. }) if name == "List" => match fields.get("inner") {
            Some(Value::Array(arr)) => Ok(arr.clone()),
            _ => Err(MetelError::internal(format!(
                "{label}: missing inner field"
            ))),
        },
        _ => Err(MetelError::internal(format!("{label}: expected List"))),
    }
}

fn native_list_new(_args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    Ok(list_value(vec![]))
}

fn native_list_from(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    match args.first() {
        Some(Value::Array(src)) => Ok(list_value(src.borrow().clone())),
        _ => Err(MetelError::internal("List::from: expected array argument")),
    }
}

fn native_list_push(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let inner = list_inner(args, "List::push")?;
    match args.get(1) {
        Some(val) => {
            inner.borrow_mut().push(val.clone());
            Ok(Value::Unit)
        }
        None => Err(MetelError::internal("List::push: expected (List, T)")),
    }
}

fn native_list_pop(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let inner = list_inner(args, "List::pop")?;
    let popped = inner.borrow_mut().pop();
    Ok(perhaps_value(popped))
}

fn native_list_len(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let inner = list_inner(args, "List::len")?;
    let len = inner.borrow().len() as i64;
    Ok(Value::I64(len))
}

fn native_list_get(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let inner = list_inner(args, "List::get")?;
    match args.get(1) {
        Some(Value::I64(idx)) => {
            let got = inner.borrow().get(*idx as usize).cloned();
            Ok(perhaps_value(got))
        }
        _ => Err(MetelError::internal("List::get: expected (List, i64)")),
    }
}

fn native_list_set(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let inner = list_inner(args, "List::set")?;
    match (args.get(1), args.get(2)) {
        (Some(Value::I64(idx)), Some(val)) => {
            let mut v = inner.borrow_mut();
            if *idx >= 0 && (*idx as usize) < v.len() {
                let old = std::mem::replace(&mut v[*idx as usize], val.clone());
                Ok(perhaps_value(Some(old)))
            } else {
                Ok(perhaps_value(None))
            }
        }
        _ => Err(MetelError::internal("List::set: expected (List, i64, T)")),
    }
}

fn native_list_as_slice(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let inner = list_inner(args, "List::as_slice")?;
    Ok(Value::Array(inner))
}

// ── std::env host implementations ──────────────────────────────────────────

fn native_env_var(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    match args.first() {
        Some(Value::Str(name)) => Ok(perhaps_value(std::env::var(name).ok().map(Value::Str))),
        _ => Err(MetelError::internal("std::env::get: expected (String)")),
    }
}

fn native_env_vars(_args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    use std::cell::RefCell;
    use std::rc::Rc;
    let entries: Vec<Value> = std::env::vars()
        .map(|(name, value)| {
            let mut fields = std::collections::HashMap::new();
            fields.insert("name".to_string(), Value::Str(name));
            fields.insert("value".to_string(), Value::Str(value));
            Value::Struct {
                name: "EnvVar".to_string(),
                // std::env-declared type; host construction has no resolver context,
                // so dispatch falls back to the name.
                type_id: None,
                fields,
            }
        })
        .collect();
    Ok(Value::Array(Rc::new(RefCell::new(entries))))
}

// ── std::fs host implementations ───────────────────────────────────────────

/// Build a `std::core` `OsError { message }` value.
fn os_error_value(message: String) -> Value {
    let mut fields = std::collections::HashMap::new();
    fields.insert("message".to_string(), Value::Str(message));
    Value::Struct {
        name: "OsError".to_string(),
        type_id: None,
        fields,
    }
}

/// Build a `std::core` `Result::Ok { value }` / `Result::Err { error }` value.
fn result_value(r: Result<Value, Value>) -> Value {
    let (variant, field, val) = match r {
        Ok(v) => ("Ok", "value", v),
        Err(e) => ("Err", "error", e),
    };
    let mut fields = std::collections::HashMap::new();
    fields.insert(field.to_string(), val);
    Value::Enum {
        name: "Result".to_string(),
        type_id: Some(crate::symbols::SYM_TYPE_RESULT),
        variant: variant.to_string(),
        // See `perhaps_value`'s matching comment (#1128).
        variant_id: None,
        fields,
    }
}

/// Map an `io::Result<T>` to a `Result<…, OsError>` value, converting the error
/// to an `OsError` carrying its display message.
fn io_result(r: std::io::Result<Value>) -> Value {
    result_value(r.map_err(|e| os_error_value(e.to_string())))
}

fn str_at(args: &[Value], idx: usize, label: &str) -> Result<String, MetelError> {
    match args.get(idx) {
        Some(Value::Str(s)) => Ok(s.clone()),
        _ => Err(MetelError::internal(format!(
            "{label}: expected a String argument at position {idx}"
        ))),
    }
}

fn native_fs_read_to_string(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let path = str_at(args, 0, "std::fs::read_to_string")?;
    Ok(io_result(std::fs::read_to_string(&path).map(Value::Str)))
}

fn native_fs_write_string(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let path = str_at(args, 0, "std::fs::write_string")?;
    let contents = str_at(args, 1, "std::fs::write_string")?;
    Ok(io_result(
        std::fs::write(&path, contents).map(|()| Value::Unit),
    ))
}

fn native_fs_append_string(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    use std::io::Write;
    let path = str_at(args, 0, "std::fs::append_string")?;
    let contents = str_at(args, 1, "std::fs::append_string")?;
    let appended = std::fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open(&path)
        .and_then(|mut f| f.write_all(contents.as_bytes()))
        .map(|()| Value::Unit);
    Ok(io_result(appended))
}

fn native_fs_exists(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let path = str_at(args, 0, "std::fs::exists")?;
    Ok(Value::Boolean(std::path::Path::new(&path).exists()))
}

fn native_fs_read_dir(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    use std::cell::RefCell;
    use std::rc::Rc;
    let path = str_at(args, 0, "std::fs::read_dir")?;
    let listed = std::fs::read_dir(&path).and_then(|entries| {
        let mut names = Vec::new();
        for entry in entries {
            let name = entry?.file_name().to_string_lossy().into_owned();
            names.push(Value::Str(name));
        }
        Ok(Value::Array(Rc::new(RefCell::new(names))))
    });
    Ok(io_result(listed))
}

fn native_fs_create_dir(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let path = str_at(args, 0, "std::fs::create_dir")?;
    Ok(io_result(std::fs::create_dir(&path).map(|()| Value::Unit)))
}

fn native_fs_create_dir_all(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let path = str_at(args, 0, "std::fs::create_dir_all")?;
    Ok(io_result(
        std::fs::create_dir_all(&path).map(|()| Value::Unit),
    ))
}

fn native_fs_remove_file(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let path = str_at(args, 0, "std::fs::remove_file")?;
    Ok(io_result(std::fs::remove_file(&path).map(|()| Value::Unit)))
}

fn native_fs_remove_dir(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let path = str_at(args, 0, "std::fs::remove_dir")?;
    Ok(io_result(std::fs::remove_dir(&path).map(|()| Value::Unit)))
}

fn native_fs_remove_dir_all(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let path = str_at(args, 0, "std::fs::remove_dir_all")?;
    Ok(io_result(
        std::fs::remove_dir_all(&path).map(|()| Value::Unit),
    ))
}

// ── std::process host implementations ──────────────────────────────────────

/// Build a `std::process` `ProcessOutput { status, stdout, stderr }` value.
fn process_output_value(status: i64, stdout: String, stderr: String) -> Value {
    let mut fields = std::collections::HashMap::new();
    fields.insert("status".to_string(), Value::I64(status));
    fields.insert("stdout".to_string(), Value::Str(stdout));
    fields.insert("stderr".to_string(), Value::Str(stderr));
    Value::Struct {
        name: "ProcessOutput".to_string(),
        type_id: None,
        fields,
    }
}

fn native_process_args(_args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    use std::cell::RefCell;
    use std::rc::Rc;
    let argv: Vec<Value> = std::env::args().map(Value::Str).collect();
    Ok(Value::Array(Rc::new(RefCell::new(argv))))
}

fn native_process_run(args: &[Value], _span: &crate::ast::Span) -> Result<Value, MetelError> {
    let command = str_at(args, 0, "std::process::run")?;
    // The second argument is a String[] of arguments; the API is shell-free —
    // the command and its arguments are passed directly, with no shell parsing.
    let cmd_args: Vec<String> = match args.get(1) {
        Some(Value::Array(arr)) => arr
            .borrow()
            .iter()
            .map(|v| match v {
                Value::Str(s) => Ok(s.clone()),
                _ => Err(MetelError::internal(
                    "std::process::run: args array must contain Strings",
                )),
            })
            .collect::<Result<_, _>>()?,
        _ => {
            return Err(MetelError::internal(
                "std::process::run: expected (String, String[])",
            ))
        }
    };
    let output = std::process::Command::new(&command)
        .args(&cmd_args)
        .output();
    Ok(result_value(
        output
            .map(|out| {
                let status = out.status.code().map_or(-1, i64::from);
                let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
                let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
                process_output_value(status, stdout, stderr)
            })
            .map_err(|e| os_error_value(e.to_string())),
    ))
}

/// The host implementation for a stdlib `native` function, looked up by its
/// lowered [`NativeKey`]. Total over the closed enum — every variant maps to a
/// host fn (enforced by the coverage test).
pub(super) fn native_host_impl(key: NativeKey) -> RuntimeCallable {
    let (label, fun): (&str, NativeFn) = match key {
        NativeKey::StdCorePrint => ("std::core::print", native_print),
        NativeKey::StdCorePrintln => ("std::core::println", native_println),
        NativeKey::StdCoreDbg => ("std::core::dbg", native_dbg),
        NativeKey::StdCoreAssert => ("std::core::assert", native_assert),
        NativeKey::StdCoreAssertMsg => ("std::core::assert_msg", native_assert_msg),
        NativeKey::StdCoreClock => ("std::core::clock", native_clock),
        NativeKey::StdCoreYoloNone => ("std::core::yolo_none", native_yolo_none),
        NativeKey::StdCoreYoloErr => ("std::core::yolo_err", native_yolo_err),
        NativeKey::StdCorePanic => ("std::core::panic", native_panic),
        NativeKey::StdCoreStringLen => ("String::len", native_string_len),
        NativeKey::StdCoreStringIsEmpty => ("String::is_empty", native_string_is_empty),
        NativeKey::StdCoreStringToUpper => ("String::to_upper", native_string_to_upper),
        NativeKey::StdCoreStringToLower => ("String::to_lower", native_string_to_lower),
        NativeKey::StdCoreStringTrim => ("String::trim", native_string_trim),
        NativeKey::StdCoreStringTrimStart => ("String::trim_start", native_string_trim_start),
        NativeKey::StdCoreStringTrimEnd => ("String::trim_end", native_string_trim_end),
        NativeKey::StdCoreStringContains => ("String::contains", native_string_contains),
        NativeKey::StdCoreStringStartsWith => ("String::starts_with", native_string_starts_with),
        NativeKey::StdCoreStringEndsWith => ("String::ends_with", native_string_ends_with),
        NativeKey::StdCoreStringIndexOf => ("String::index_of", native_string_index_of),
        NativeKey::StdCoreStringSplit => ("String::split", native_string_split),
        NativeKey::StdCoreStringReplace => ("String::replace", native_string_replace),
        NativeKey::StdCoreStringRepeat => ("String::repeat", native_string_repeat),
        NativeKey::StdCoreStringJoin => ("String::join", native_string_join),
        NativeKey::StdCoreStringChars => ("String::chars", native_string_chars),
        NativeKey::StdCoreStringCharAt => ("String::char_at", native_string_char_at),
        NativeKey::StdCoreStringSubstring => ("String::substring", native_string_substring),
        NativeKey::StdCoreToString => ("Display::to_string", native_to_string),
        NativeKey::StdCoreI8From => ("i8::from", native_i8_from),
        NativeKey::StdCoreI16From => ("i16::from", native_i16_from),
        NativeKey::StdCoreI32From => ("i32::from", native_i32_from),
        NativeKey::StdCoreI64From => ("i64::from", native_i64_from),
        NativeKey::StdCoreU8From => ("u8::from", native_u8_from),
        NativeKey::StdCoreU16From => ("u16::from", native_u16_from),
        NativeKey::StdCoreU32From => ("u32::from", native_u32_from),
        NativeKey::StdCoreU64From => ("u64::from", native_u64_from),
        NativeKey::StdCoreF32From => ("f32::from", native_f32_from),
        NativeKey::StdCoreF64From => ("f64::from", native_f64_from),
        NativeKey::StdCoreCharFrom => ("Char::from", native_char_from),
        NativeKey::StdCoreListNew => ("List::new", native_list_new),
        NativeKey::StdCoreListFrom => ("List::from", native_list_from),
        NativeKey::StdCoreListPush => ("List::push", native_list_push),
        NativeKey::StdCoreListPop => ("List::pop", native_list_pop),
        NativeKey::StdCoreListLen => ("List::len", native_list_len),
        NativeKey::StdCoreListGet => ("List::get", native_list_get),
        NativeKey::StdCoreListSet => ("List::set", native_list_set),
        NativeKey::StdCoreListAsSlice => ("List::as_slice", native_list_as_slice),
        NativeKey::StdEnvVar => ("std::env::get", native_env_var),
        NativeKey::StdEnvVars => ("std::env::vars", native_env_vars),
        NativeKey::StdFsReadToString => ("std::fs::read_to_string", native_fs_read_to_string),
        NativeKey::StdFsWriteString => ("std::fs::write_string", native_fs_write_string),
        NativeKey::StdFsAppendString => ("std::fs::append_string", native_fs_append_string),
        NativeKey::StdFsExists => ("std::fs::exists", native_fs_exists),
        NativeKey::StdFsReadDir => ("std::fs::read_dir", native_fs_read_dir),
        NativeKey::StdFsCreateDir => ("std::fs::create_dir", native_fs_create_dir),
        NativeKey::StdFsCreateDirAll => ("std::fs::create_dir_all", native_fs_create_dir_all),
        NativeKey::StdFsRemoveFile => ("std::fs::remove_file", native_fs_remove_file),
        NativeKey::StdFsRemoveDir => ("std::fs::remove_dir", native_fs_remove_dir),
        NativeKey::StdFsRemoveDirAll => ("std::fs::remove_dir_all", native_fs_remove_dir_all),
        NativeKey::StdProcessArgs => ("std::process::args", native_process_args),
        NativeKey::StdProcessRun => ("std::process::run", native_process_run),
    };
    RuntimeCallable::Intrinsic {
        label: label.to_string(),
        fun,
    }
}

/// Register the `std::core` free functions by parsing the embedded core.mtl and
/// binding each `native` declaration to its host implementation (METEL-181).
/// `stdlib/core.mtl` + the `NativeKey` enum are the single source of truth;
/// there is no hand-maintained list to keep in sync with the typechecker (the
/// prelude derives its schemes from the same source). This serves the
/// single-program pipeline; the module-graph pipeline additionally evaluates
/// `std::core` as a real module.
/// The well-known `SymbolId` of a builtin `std::core` aspect, matching the id the
/// name resolver assigns it (the `SymbolTable` pre-seeds these). Lets embedded-core
/// seeding register builtin aspect impls under the same id elaboration stamps into
/// call sites, so aspect dispatch is purely id-based (METEL-185).
pub(super) fn builtin_aspect_id(aspect_name: &str) -> Option<crate::symbols::SymbolId> {
    match aspect_name {
        "Display" => Some(crate::symbols::SYM_ASPECT_DISPLAY),
        "Iterable" => Some(crate::symbols::SYM_ASPECT_ITERABLE),
        "From" => Some(crate::symbols::SYM_ASPECT_FROM),
        _ => None,
    }
}

/// The well-known `SymbolId` of a builtin `std::core` type, matching the id the
/// name resolver assigns it (pre-seeded in `SymbolTable`). Lets embedded-core
/// seeding register builtin type entries under the same id the rest of the
/// pipeline uses, so the runtime type registry is keyed purely by id (METEL-185).
pub(super) fn builtin_type_id(type_name: &str) -> Option<crate::symbols::SymbolId> {
    use crate::symbols::{
        SYM_TYPE_BOOLEAN, SYM_TYPE_CHAR, SYM_TYPE_F32, SYM_TYPE_F64, SYM_TYPE_I16, SYM_TYPE_I32,
        SYM_TYPE_I64, SYM_TYPE_I8, SYM_TYPE_LIST, SYM_TYPE_PERHAPS, SYM_TYPE_RANGE,
        SYM_TYPE_RANGE_INCLUSIVE, SYM_TYPE_RESULT, SYM_TYPE_STRING, SYM_TYPE_U16, SYM_TYPE_U32,
        SYM_TYPE_U64, SYM_TYPE_U8,
    };
    Some(match type_name {
        "boolean" => SYM_TYPE_BOOLEAN,
        "String" => SYM_TYPE_STRING,
        "Char" => SYM_TYPE_CHAR,
        "i8" => SYM_TYPE_I8,
        "i16" => SYM_TYPE_I16,
        "i32" => SYM_TYPE_I32,
        "i64" => SYM_TYPE_I64,
        "u8" => SYM_TYPE_U8,
        "u16" => SYM_TYPE_U16,
        "u32" => SYM_TYPE_U32,
        "u64" => SYM_TYPE_U64,
        "f32" => SYM_TYPE_F32,
        "f64" => SYM_TYPE_F64,
        "List" => SYM_TYPE_LIST,
        "Perhaps" => SYM_TYPE_PERHAPS,
        "Result" => SYM_TYPE_RESULT,
        "Range" => SYM_TYPE_RANGE,
        "RangeInclusive" => SYM_TYPE_RANGE_INCLUSIVE,
        _ => return None,
    })
}

fn register_core_natives_from_embedded(runtime: &mut RuntimeRegistry) {
    fn key_for(binding: &crate::ast::NativeBinding) -> NativeKey {
        NativeKey::from_path(&binding.key_path).unwrap_or_else(|| {
            panic!(
                "embedded std::core declares unknown native binding @{}",
                binding.key_path.join(".")
            )
        })
    }
    let core_path = ["std".to_string(), "core".to_string()];
    let Some(source) = crate::stdlib::lookup(&core_path) else {
        return;
    };
    let program = crate::parser::parse(source, "<embedded std::core>")
        .expect("embedded std::core must parse; it is compiled into the binary");
    for decl in &program.decls {
        match decl {
            crate::ast::Decl::Fun(fun) => {
                let Some(binding) = &fun.native else { continue };
                let key = key_for(binding);
                let value = Value::Callable(native_host_impl(key));
                // Overloaded std::core definitions (the assert pair) register
                // under their canonical overload SymbolId — the same id the
                // typechecker stamps into call sites in every module.
                match crate::typechecker::core_native_symbol(fun) {
                    Some(id) => runtime.register_symbol_value(id, value),
                    None => runtime.register_std_core_value(fun.name.clone(), value),
                }
            }
            crate::ast::Decl::Impl(ib) => {
                let crate::ast::TypeExpr::Named(target_name, _) = &ib.target_type else {
                    continue;
                };
                // Every std::core impl targets a builtin type with a well-known id.
                let Some(target_id) = builtin_type_id(target_name) else {
                    continue;
                };
                for method in &ib.methods {
                    // Only native methods are derivable here; a Metel-bodied
                    // core impl method would need elaboration, which this
                    // single-program seeding path does not run.
                    let Some(binding) = &method.native else {
                        continue;
                    };
                    let key = key_for(binding);
                    let receiver = method.params.first().and_then(|p| p.receiver.clone());
                    let params: Vec<RuntimeTypeRef> = method
                        .params
                        .iter()
                        .filter(|p| p.receiver.is_none())
                        .map(|p| {
                            p.type_ann.as_ref().map(super::runtime_type_ref).expect(
                                "native declarations are fully annotated (enforced by native_fun_ty)",
                            )
                        })
                        .collect();
                    let runtime_method = RuntimeMethod {
                        label: format!("{target_name}::{}", method.name),
                        receiver,
                        signature: RuntimeSignature {
                            params,
                            ret: method.return_type.as_ref().map(super::runtime_type_ref),
                        },
                        body: native_host_impl(key),
                    };
                    if let Some(aspect_name) = &ib.aspect_name {
                        let type_args = ib
                            .aspect_type_args
                            .iter()
                            .map(super::runtime_type_key)
                            .collect();
                        runtime.register_aspect_method(
                            target_id,
                            target_name,
                            aspect_name,
                            builtin_aspect_id(aspect_name),
                            type_args,
                            &method.name,
                            runtime_method,
                        );
                    } else if runtime_method.receiver.is_none() {
                        runtime.register_type_value(
                            target_id,
                            target_name,
                            &method.name,
                            runtime_method,
                        );
                    } else {
                        runtime.register_inherent_method(
                            target_id,
                            target_name,
                            &method.name,
                            runtime_method,
                        );
                    }
                }
            }
            _ => {}
        }
    }
}

pub(super) fn register_builtins(runtime: &mut RuntimeRegistry) {
    fn named(name: &str) -> RuntimeTypeRef {
        RuntimeTypeRef::Named(name.to_string())
    }

    fn method(
        label: &str,
        receiver: Option<crate::ast::ReceiverKind>,
        params: &[&str],
        ret: Option<&str>,
        body: RuntimeCallable,
    ) -> RuntimeMethod {
        RuntimeMethod {
            label: label.to_string(),
            receiver,
            signature: RuntimeSignature {
                params: params.iter().map(|name| named(name)).collect(),
                ret: ret.map(named),
            },
            body,
        }
    }

    fn intrinsic(label: &str, fun: NativeFn) -> RuntimeCallable {
        RuntimeCallable::Intrinsic {
            label: label.to_string(),
            fun,
        }
    }

    fn builtin_value(label: &str, fun: NativeFn) -> RuntimeCallable {
        intrinsic(label, fun)
    }

    macro_rules! register_pattern {
        ($pattern:expr, $method_name:expr, $value:expr) => {
            runtime.register_pattern_method($pattern, $method_name, $value);
        };
    }
    // std::core free functions (print/println/…) and the native impl methods
    // (Display::to_string on primitives, the numeric From cross-product,
    // Char ↔ u32) — all derived from the embedded core.mtl declarations.
    register_core_natives_from_embedded(runtime);

    // String::len is declared in core.mtl (`impl String`) and registered by
    // the embedded derivation above / the std::core module evaluation.

    register_pattern!(
        RuntimeTypePattern::Array,
        "len",
        method(
            "Array::len",
            Some(crate::ast::ReceiverKind::Value),
            &[],
            Some("i64"),
            builtin_value("Array::len", |args, _span| {
                match args.first() {
                    Some(Value::Array(arr)) => Ok(Value::I64(arr.borrow().len() as i64)),
                    _ => Err(MetelError::internal("Array::len: expected array")),
                }
            }),
        )
    );

    // clock / assert (both overloads) / dbg are registered by
    // register_core_natives_from_embedded above.
}

pub(super) fn runtime_registry() -> RuntimeRegistry {
    let mut runtime = RuntimeRegistry::new();
    register_builtins(&mut runtime);
    runtime
}

#[cfg(test)]
mod native_tests {
    use super::*;

    #[test]
    fn every_native_key_has_a_host_impl() {
        // Coverage: each NativeKey must resolve to a registered host
        // implementation. This replaces the old free_function_names() parity
        // check as the single source of truth for native dispatch (METEL-182).
        for key in NativeKey::ALL {
            let callable = native_host_impl(*key);
            match callable {
                RuntimeCallable::Intrinsic { label, .. } => {
                    assert!(!label.is_empty(), "native impl for {key:?} has empty label");
                }
                _ => panic!("native impl for {key:?} is not an intrinsic"),
            }
        }
    }
}
