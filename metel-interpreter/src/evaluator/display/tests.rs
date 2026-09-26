use super::format_value;
use crate::evaluator::Value;
use std::cell::RefCell;
use std::rc::Rc;

#[test]
fn mutable_reference_value_display_uses_language_spelling() {
    let value = Value::MutReference(Rc::new(RefCell::new(Value::I64(42))));
    assert_eq!(format_value(&value), "&var 42");
}
