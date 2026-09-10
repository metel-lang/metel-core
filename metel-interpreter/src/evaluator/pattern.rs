use std::cell::RefCell;
use std::rc::Rc;

use crate::ast::Literal;
use crate::identity::LocalId;
use crate::typed_ast::TypedPattern;

use super::Value;

/// One binding produced by a successful pattern match: the spelling, its
/// lexical identity when identity allocation stamped one, and the bound value
/// (metel-core#1052b). The caller installs each into the environment by
/// [`LocalId`] in the id-indexed frame, falling back to the name.
pub(super) type PatternBinding = (String, Option<LocalId>, Value);

// Float literal patterns (e.g. `1.0 => ...`) match by exact IEEE-754 equality,
// matching the same exact-comparison semantics as `==` (see `eval_binop`) --
// not a bug, so not rewritten to an epsilon comparison.
#[allow(clippy::float_cmp)]
// Exhaustive match over every Pattern/Value combination; splitting it up would
// scatter one coherent dispatch table across many small functions with no
// real gain in clarity.
#[allow(clippy::too_many_lines)]
pub(super) fn match_pattern(
    pattern: &TypedPattern,
    value: &Value,
    out: &mut Vec<PatternBinding>,
) -> bool {
    match pattern {
        TypedPattern::Wildcard(_) => true,

        TypedPattern::Literal(lit, _) => match (lit, value) {
            (Literal::Int(a), Value::I64(b)) => a == b,
            (Literal::Float(a), Value::F64(b)) => a == b,
            (Literal::Char(a), Value::Char(b)) => a == b,
            (Literal::Boolean(a), Value::Boolean(b)) => a == b,
            (Literal::Str(a), Value::Str(b)) => a == b,
            (Literal::Unit, Value::Unit) => true,
            (Literal::SizedInt { value: a, kind }, v) => {
                use crate::ast::IntKind;
                match kind {
                    IntKind::I8 => matches!(v, Value::I8(b)  if *b == *a as i8),
                    IntKind::I16 => matches!(v, Value::I16(b) if *b == *a as i16),
                    IntKind::I32 => matches!(v, Value::I32(b) if *b == *a as i32),
                    IntKind::I64 => matches!(v, Value::I64(b) if *b == *a as i64),
                    IntKind::U8 => matches!(v, Value::U8(b)  if *b == *a as u8),
                    IntKind::U16 => matches!(v, Value::U16(b) if *b == *a as u16),
                    IntKind::U32 => matches!(v, Value::U32(b) if *b == *a as u32),
                    IntKind::U64 => matches!(v, Value::U64(b) if *b == *a as u64),
                }
            }
            (Literal::SizedFloat { value: a, kind }, v) => {
                use crate::ast::FloatKind;
                match kind {
                    FloatKind::F32 => matches!(v, Value::F32(b) if *b == *a as f32),
                    FloatKind::F64 => matches!(v, Value::F64(b) if *b == *a),
                }
            }
            _ => false,
        },

        TypedPattern::Binding(name, local_id, _) => {
            out.push((name.clone(), *local_id, value.clone()));
            true
        }

        TypedPattern::Tuple(sub_patterns, _) => match value {
            Value::Tuple(elems) if elems.len() == sub_patterns.len() => sub_patterns
                .iter()
                .zip(elems.iter())
                .all(|(p, v)| match_pattern(p, v, out)),
            _ => false,
        },

        TypedPattern::EnumVariant { path, fields, .. } => {
            let type_name = if path.len() >= 2 {
                path[path.len() - 2].as_str()
            } else {
                ""
            };
            let variant_name = path.last().map_or("", String::as_str);
            match value {
                Value::Enum {
                    name,
                    variant,
                    fields: enum_fields,
                    ..
                } if name == type_name && variant == variant_name => {
                    // Runtime `Value::Enum` fields are still name-keyed; the
                    // pattern's `FieldId`s wait on the evaluator's id-indexed
                    // frames (#1052). The shorthand binding's `LocalId` is
                    // carried through so the match arm can install it by id.
                    for (field_name, _id, local) in fields {
                        match enum_fields.get(field_name) {
                            Some(v) => {
                                out.push((field_name.clone(), *local, v.clone()));
                            }
                            None => return false,
                        }
                    }
                    true
                }
                _ => false,
            }
        }

        // RFC-0032 §4/§5, RFC-0034 §5: a named struct pattern. `rest` (`..`) allows
        // the struct to carry more fields than the pattern names, the way an array's
        // rest pattern allows more elements than its explicit prefix -- without it,
        // the pattern must name every one of the struct's fields (already enforced
        // as a static exhaustiveness check in inference.rs, checked again here since
        // a Value carries no static guarantee of its own field count).
        TypedPattern::Struct {
            name, fields, rest, ..
        } => match value {
            Value::Struct {
                name: value_name,
                fields: struct_fields,
                ..
            } if value_name == name => {
                if !rest && struct_fields.len() != fields.len() {
                    return false;
                }
                for (field_name, _id, local) in fields {
                    match struct_fields.get(field_name) {
                        Some(v) => {
                            out.push((field_name.clone(), *local, v.clone()));
                        }
                        None => return false,
                    }
                }
                true
            }
            _ => false,
        },

        // #646: `rest` (`..`) allows the record to carry more fields than the pattern
        // names -- the runtime value for a row-bounded generic parameter (`<record T:
        // { x: f64, .. }>`) is an ordinary `Value::Record` like any other, so the same
        // subset-match `Pattern::Struct` already does above applies here verbatim.
        TypedPattern::Record { fields, rest, .. } => match value {
            Value::Record {
                fields: record_fields,
            } => {
                if !rest && record_fields.len() != fields.len() {
                    return false;
                }
                for (field_name, local) in fields {
                    match record_fields.get(field_name) {
                        Some(v) => {
                            out.push((field_name.clone(), *local, v.clone()));
                        }
                        None => return false,
                    }
                }
                true
            }
            _ => false,
        },

        TypedPattern::Array { elems, rest, .. } => {
            match value {
                Value::Array(rc) => {
                    let arr = rc.borrow();
                    if rest.is_none() {
                        // Exact match: array must have exactly `elems.len()` elements.
                        if arr.len() != elems.len() {
                            return false;
                        }
                    } else {
                        // Rest pattern: array must have at least `elems.len()` elements.
                        if arr.len() < elems.len() {
                            return false;
                        }
                    }
                    // Match explicit element patterns.
                    for (pat, val) in elems.iter().zip(arr.iter()) {
                        if !match_pattern(pat, val, out) {
                            return false;
                        }
                    }
                    // Bind rest to the remaining tail. The array rest binding
                    // has no `LocalId` channel yet (#1052), so it stays
                    // name-only and resolves through the name-map fallback.
                    if let Some(rest_name) = rest {
                        let tail: Vec<Value> = arr[elems.len()..].to_vec();
                        out.push((
                            rest_name.clone(),
                            None,
                            Value::Array(Rc::new(RefCell::new(tail))),
                        ));
                    }
                    true
                }
                _ => false,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{match_pattern, LocalId, TypedPattern, Value};
    use crate::ast::Span;

    #[test]
    fn binding_pattern_carries_its_local_id() {
        let pat = TypedPattern::Binding("x".to_string(), Some(LocalId(5)), Span::new(0, 0, "t"));
        let mut out = Vec::new();
        assert!(match_pattern(&pat, &Value::I64(9), &mut out));
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].0, "x");
        assert_eq!(out[0].1, Some(LocalId(5)));
    }

    #[test]
    fn struct_field_shorthand_bindings_carry_their_local_ids() {
        use std::collections::HashMap;
        let pat = TypedPattern::Struct {
            name: "P".to_string(),
            type_id: None,
            fields: vec![
                ("a".to_string(), None, Some(LocalId(1))),
                ("b".to_string(), None, Some(LocalId(2))),
            ],
            rest: false,
            span: Span::new(0, 0, "t"),
        };
        let mut fields = HashMap::new();
        fields.insert("a".to_string(), Value::I64(1));
        fields.insert("b".to_string(), Value::I64(2));
        let value = Value::Struct {
            name: "P".to_string(),
            type_id: None,
            fields,
        };
        let mut out = Vec::new();
        assert!(match_pattern(&pat, &value, &mut out));
        let ids: Vec<_> = out.iter().map(|(n, id, _)| (n.as_str(), *id)).collect();
        assert!(ids.contains(&("a", Some(LocalId(1)))));
        assert!(ids.contains(&("b", Some(LocalId(2)))));
    }
}
