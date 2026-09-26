use super::*;

fn span() -> Span {
    Span {
        start: 10,
        end: 20,
        filename: "test.mtl".into(),
        line: 3,
        col: 5,
    }
}

#[test]
fn primary_span_recovers_parse_error_location() {
    let err = MetelError::parse(ParseErrorCode::P0001, "boom", &span());
    let recovered = err.primary_span().expect("parse error has a span");
    assert_eq!(recovered, span());
}

#[test]
fn primary_span_recovers_type_error_location() {
    let err = MetelError::type_error(TypeErrorCode::T0001, "boom", &span());
    let recovered = err.primary_span().expect("type error has a span");
    assert_eq!(recovered, span());
}

#[test]
fn primary_span_recovers_runtime_panic_location() {
    let err = MetelError::panic(RuntimeErrorCode::R0004, "boom", &span());
    let recovered = err.primary_span().expect("runtime panic has a span");
    assert_eq!(recovered, span());
}

#[test]
fn primary_span_is_none_for_internal_errors() {
    assert!(MetelError::internal("bug").primary_span().is_none());
    assert!(MetelError::not_implemented("todo").primary_span().is_none());
}
