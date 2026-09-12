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

        TypedPattern::EnumVariant {
            path,
            variant_id,
            fields,
            ..
        } => {
            let Value::Enum {
                name,
                variant,
                variant_id: value_variant_id,
                fields: enum_fields,
                ..
            } = value
            else {
                return false;
            };
            // Prefer identity: when both the pattern and the runtime value
            // carry a resolved `VariantId` (ADR-0054 / #1062, metel-core#1128),
            // compare that instead of the bare, source-spelled path segments
            // -- two unrelated modules can each declare a same-named enum
            // with a same-named variant, and a bare-string comparison would
            // silently match (or fail to match) the wrong one. Name
            // comparison stays the documented recovery path when either side
            // has no identity context (`None`, e.g. a block-local enum, or a
            // value built without resolver context).
            let variant_matches =
                if let (Some(pattern_vid), Some(value_vid)) = (variant_id, value_variant_id) {
                    pattern_vid == value_vid
                } else {
                    let type_name = if path.len() >= 2 {
                        path[path.len() - 2].as_str()
                    } else {
                        ""
                    };
                    let variant_name = path.last().map_or("", String::as_str);
                    name == type_name && variant == variant_name
                };
            if !variant_matches {
                return false;
            }
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
                    // Bind rest to the remaining tail, by its LocalId when
                    // identity allocation stamped one (metel-core#1097).
                    if let Some((rest_name, rest_id)) = rest {
                        let tail: Vec<Value> = arr[elems.len()..].to_vec();
                        out.push((
                            rest_name.clone(),
                            *rest_id,
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
    use crate::identity::VariantId;

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

    /// Two unrelated modules can each declare an enum named `Shape` with a
    /// variant named `Circle` (metel-core#1128). `path`/`name`/`variant` are
    /// bare, source-spelled strings and so are identical across both; only
    /// `variant_id` (interned per `(enum SymbolId, variant name)`) tells them
    /// apart. A pattern resolved against one such enum must not match a
    /// runtime value that actually belongs to the other, even though every
    /// bare string involved lines up.
    #[test]
    fn enum_variant_pattern_rejects_a_same_named_variant_from_an_unrelated_enum() {
        use std::collections::HashMap;
        let pat = TypedPattern::EnumVariant {
            path: vec!["Shape".to_string(), "Circle".to_string()],
            variant_id: Some(VariantId(1)),
            fields: vec![("radius".to_string(), None, Some(LocalId(1)))],
            rest: false,
            span: Span::new(0, 0, "t"),
        };
        let mut fields = HashMap::new();
        fields.insert("radius".to_string(), Value::F64(2.0));
        let value = Value::Enum {
            name: "Shape".to_string(),
            type_id: None,
            variant: "Circle".to_string(),
            variant_id: Some(VariantId(2)),
            fields,
        };
        let mut out = Vec::new();
        assert!(
            !match_pattern(&pat, &value, &mut out),
            "a pattern resolved to one enum's variant must not match a value \
             belonging to an unrelated same-named enum's same-named variant"
        );
    }

    #[test]
    fn enum_variant_pattern_matches_the_same_resolved_identity() {
        use std::collections::HashMap;
        let pat = TypedPattern::EnumVariant {
            path: vec!["Shape".to_string(), "Circle".to_string()],
            variant_id: Some(VariantId(1)),
            fields: vec![("radius".to_string(), None, Some(LocalId(1)))],
            rest: false,
            span: Span::new(0, 0, "t"),
        };
        let mut fields = HashMap::new();
        fields.insert("radius".to_string(), Value::F64(2.0));
        let value = Value::Enum {
            name: "Shape".to_string(),
            type_id: None,
            variant: "Circle".to_string(),
            variant_id: Some(VariantId(1)),
            fields,
        };
        let mut out = Vec::new();
        assert!(
            match_pattern(&pat, &value, &mut out),
            "the same resolved VariantId on both sides must match"
        );
        assert_eq!(out[0].0, "radius");
        assert_eq!(out[0].1, Some(LocalId(1)));
        assert!(matches!(out[0].2, Value::F64(r) if r == 2.0));
    }

    /// `variant_id: None` is the documented recovery state (no identity
    /// context, e.g. a block-local enum) -- matching must still fall back to
    /// the bare name comparison, exactly as before #1128.
    #[test]
    fn enum_variant_pattern_falls_back_to_bare_names_without_identity_context() {
        use std::collections::HashMap;
        let pat = TypedPattern::EnumVariant {
            path: vec!["Shape".to_string(), "Circle".to_string()],
            variant_id: None,
            fields: vec![],
            rest: false,
            span: Span::new(0, 0, "t"),
        };
        let value = Value::Enum {
            name: "Shape".to_string(),
            type_id: None,
            variant: "Circle".to_string(),
            variant_id: None,
            fields: HashMap::new(),
        };
        let mut out = Vec::new();
        assert!(
            match_pattern(&pat, &value, &mut out),
            "without identity context on either side, matching falls back to bare names"
        );
    }

    #[test]
    fn array_rest_binding_carries_its_local_id() {
        use std::cell::RefCell;
        use std::rc::Rc;
        let pat = TypedPattern::Array {
            elems: vec![TypedPattern::Binding(
                "head".to_string(),
                Some(LocalId(1)),
                Span::new(0, 0, "t"),
            )],
            rest: Some(("tail".to_string(), Some(LocalId(2)))),
            span: Span::new(0, 0, "t"),
        };
        let value = Value::Array(Rc::new(RefCell::new(vec![
            Value::I64(1),
            Value::I64(2),
            Value::I64(3),
        ])));
        let mut out = Vec::new();
        assert!(match_pattern(&pat, &value, &mut out));
        let rest_binding = out
            .iter()
            .find(|(name, ..)| name == "tail")
            .expect("rest binding present");
        assert_eq!(rest_binding.1, Some(LocalId(2)));
    }
}
