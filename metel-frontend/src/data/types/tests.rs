use super::Type;

#[test]
fn mutable_reference_display_uses_language_spelling() {
    assert_eq!(
        Type::MutReference(Box::new(Type::I64)).to_string(),
        "&var i64"
    );
}
