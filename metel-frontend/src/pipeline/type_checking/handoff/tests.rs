use super::*;
use crate::pipeline::type_checking::typeinference::{
    InferType, TypeDefinitionRegistry, TypeVar, TypeVarGenerator,
};

fn context_with_closure(span: Span, ty: InferType) -> InferContext {
    let mut ctx = InferContext::new(
        TypeDefinitionRegistry::default(),
        TypeVarGenerator::new(),
        &HashMap::new(),
        vec![],
    );
    ctx.record_closure_return_type(span, ty);
    ctx
}

#[test]
fn resolves_closure_return_types_before_construction() {
    let span = Span::new(4, 12, "handoff.mtl");
    let var = TypeVar(7);
    let ctx = context_with_closure(span.clone(), InferType::Var(var));
    let mut subst = Substitution::new();
    subst.bind(var, InferType::int());

    let facts = ResolvedInferenceFacts::resolve(&ctx, &subst).unwrap();

    assert_eq!(facts.closure_return_type(&span), Some(&Type::I64));
}

#[test]
fn omits_polymorphic_closure_facts_resolved_per_call_site() {
    let span = Span::new(4, 12, "handoff.mtl");
    let ctx = context_with_closure(span.clone(), InferType::Var(TypeVar(7)));

    let facts = ResolvedInferenceFacts::resolve(&ctx, &Substitution::new()).unwrap();

    assert_eq!(facts.closure_return_type(&span), None);
}
