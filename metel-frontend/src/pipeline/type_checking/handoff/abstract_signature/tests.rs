use super::*;
use crate::data::types::{CallMultiplicity, CallMutation, NominalId, Type, UseMultiplicity};
use crate::identity::SymbolId;

fn binder(id: u32) -> BindingId {
    BindingId::Global(SymbolId(id))
}

fn scheme(first: u32, second: u32) -> TypeScheme {
    let mut scheme = TypeScheme::mono(InferType::fun(
        vec![
            InferType::Var(TypeVar(first)),
            InferType::Var(TypeVar(second)),
        ],
        InferType::Var(TypeVar(first)),
    ));
    let mut variables = vec![(TypeVar(first), "T"), (TypeVar(second), "U")];
    variables.sort_by_key(|(variable, _)| *variable);
    scheme.quantified_vars = variables.iter().map(|(variable, _)| *variable).collect();
    scheme.param_names = variables
        .iter()
        .map(|(_, name)| (*name).to_string())
        .collect();
    scheme
}

fn freeze(scheme: &TypeScheme, id: u32) -> AbstractSignature {
    freeze_signature(
        scheme,
        binder(id),
        &["T", "U"],
        &Span::new(1, 1, "abstract.mtl"),
    )
    .expect("signature freezes")
}

#[test]
fn non_monotonic_solver_renaming_preserves_abstract_signature() {
    let original = freeze(&scheme(1, 2), 7);
    let renamed = freeze(&scheme(9, 3), 7);
    assert_eq!(original, renamed);
    assert_eq!(original.parameters[0].name.as_deref(), Some("T"));
    assert_eq!(original.parameters[1].name.as_deref(), Some("U"));
}

#[test]
fn implicit_parameter_order_follows_signature_not_solver_numbers() {
    let source = scheme(1, 2);
    let renamed = scheme(9, 3);
    let span = Span::new(1, 1, "implicit.mtl");
    assert_eq!(
        freeze_signature(&source, binder(7), &[], &span).unwrap(),
        freeze_signature(&renamed, binder(7), &[], &span).unwrap(),
    );
}

#[test]
fn parameter_in_another_binder_is_not_the_same_type() {
    let first = freeze(&scheme(1, 2), 7);
    let second = freeze(&scheme(1, 2), 8);
    assert_ne!(first.parameters[0].id, second.parameters[0].id);
    assert_ne!(first.ty, second.ty);
}

#[test]
fn return_only_parameters_and_unknown_row_tails_are_not_defaulted() {
    let mut source = TypeScheme::mono(InferType::fun(
        vec![],
        InferType::RowExtend {
            fields: vec![("token".to_string(), InferType::Concrete(Type::Str))],
            tail: Box::new(InferType::Var(TypeVar(11))),
        },
    ));
    source.quantified_vars = vec![TypeVar(11)];
    source.param_names = vec!["R".to_string()];
    let signature = freeze(&source, 7);
    let AbstractType::Function { result, .. } = signature.ty else {
        panic!("function")
    };
    let AbstractType::OpenRecord { fields, tail } = *result else {
        panic!("open row")
    };
    assert_eq!(
        fields,
        vec![("token".to_string(), AbstractType::Concrete(Type::Str))]
    );
    assert_eq!(*tail, AbstractType::Parameter(signature.parameters[0].id));
}

#[test]
fn function_axes_references_and_nominal_identity_are_preserved() {
    let mut source = scheme(1, 2);
    source.ty = InferType::Fun(
        vec![
            InferType::Reference(Box::new(InferType::Var(TypeVar(1)))),
            InferType::MutReference(Box::new(InferType::Var(TypeVar(2)))),
        ],
        Box::new(InferType::Named(
            "T".to_string(),
            vec![],
            NominalId(Some(SymbolId(99))),
        )),
        CallMultiplicity::Once,
        UseMultiplicity::Move,
        CallMutation::Mutating,
    );
    let signature = freeze(&source, 7);
    let AbstractType::Function {
        parameters,
        result,
        call,
        usage,
        mutation,
    } = signature.ty
    else {
        panic!("function")
    };
    assert!(matches!(&parameters[0], AbstractType::Reference(_)));
    assert!(matches!(&parameters[1], AbstractType::MutReference(_)));
    assert_eq!(call, CallMultiplicity::Once);
    assert_eq!(usage, UseMultiplicity::Move);
    assert_eq!(mutation, CallMutation::Mutating);
    assert!(matches!(
        *result,
        AbstractType::Named {
            identity: NominalId(Some(SymbolId(99))),
            ..
        }
    ));
}

#[test]
fn unquantified_unknown_is_an_error_not_a_bottom_type() {
    let source = TypeScheme::mono(InferType::Var(TypeVar(123)));
    let span = Span {
        line: 4,
        col: 2,
        ..Span::new(0, 1, "bad.mtl")
    };
    let error = freeze_signature(&source, binder(7), &[], &span)
        .expect_err("unquantified variable must not become Never or Unit");
    assert!(
        error
            .to_string()
            .contains("unquantified variable at bad.mtl:4:2")
    );
}
