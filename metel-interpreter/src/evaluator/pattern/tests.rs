use super::{LocalId, TypedPattern, Value, match_pattern};
use crate::data::ast::Span;
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
