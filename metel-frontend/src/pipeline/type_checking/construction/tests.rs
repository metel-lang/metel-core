use super::*;
use crate::identity::{Allocation, MemberTable};
use crate::pipeline::name_resolution::name_resolver::ResolvedNames;
use crate::pipeline::path_normalization::NormalizedModuleGraph;
use crate::pipeline::type_checking::{CheckGraphReport, CorePrelude, check_graph_with_report};
use std::rc::Rc;

#[test]
fn generic_declarations_retain_binder_scoped_abstract_signatures() {
    use crate::data::abstract_body::AbstractType;
    use crate::identity::BindingId;

    let typed = typecheck_source(
        "abstract_signature.mtl",
        r#"
fun pick<T, U>(first: T, second: U) -> T { first }
fun make<V>() -> [V] { [] }
fun plain(value: i64) -> i64 { value }
fun main() {}
"#,
    )
    .report;
    let functions: Vec<_> = typed
        .graph
        .modules
        .iter()
        .flat_map(|module| &module.decls)
        .filter_map(|decl| match decl {
            TypedDecl::Fun(fun) if matches!(fun.name.as_str(), "pick" | "make" | "plain") => {
                Some(fun)
            }
            _ => None,
        })
        .collect();
    let pick = functions.iter().find(|fun| fun.name == "pick").unwrap();
    let signature = pick
        .abstract_signature
        .as_ref()
        .expect("unused generic has a signature");
    assert_eq!(signature.binder, BindingId::Global(pick.def_id.unwrap()));
    assert_eq!(signature.parameters[0].name.as_deref(), Some("T"));
    assert_eq!(signature.parameters[1].name.as_deref(), Some("U"));
    let AbstractType::Function {
        parameters, result, ..
    } = &signature.ty
    else {
        panic!("function")
    };
    assert_eq!(
        parameters[0],
        AbstractType::Parameter(signature.parameters[0].id)
    );
    assert_eq!(
        parameters[1],
        AbstractType::Parameter(signature.parameters[1].id)
    );
    assert_eq!(**result, parameters[0]);
    let make = functions.iter().find(|fun| fun.name == "make").unwrap();
    let make_signature = make.abstract_signature.as_ref().unwrap();
    assert_ne!(signature.parameters[0].id, make_signature.parameters[0].id);
    assert!(
        functions
            .iter()
            .find(|fun| fun.name == "plain")
            .unwrap()
            .abstract_signature
            .is_none()
    );
}

#[test]
fn abstract_signature_retains_aspect_arguments_and_negative_grants() {
    use crate::data::abstract_body::{AbstractBound, AbstractType};
    let typed = typecheck_source(
        "abstract_grants.mtl",
        r#"
aspect Transform<A, B> { fun transform(&self, value: A) -> B; }
struct Token {}
aspect Sink<A> {}
fun translate<T: Transform<U, String>, U>(value: &T, input: U) -> String {
    value.transform(input)
}
fun forward<T: !Clone>(value: T) -> T { value }
fun nominal<T: Sink<Token>>(value: &T) {}
fun main() {}
"#,
    )
    .report;
    let find = |name: &str| {
        typed
            .graph
            .modules
            .iter()
            .flat_map(|module| &module.decls)
            .find_map(|decl| match decl {
                TypedDecl::Fun(fun) if fun.name == name => Some(fun),
                _ => None,
            })
            .unwrap()
    };
    let signature = find("translate").abstract_signature.as_ref().unwrap();
    let facts = signature.facts.as_ref().expect("fact environment retained");
    let AbstractBound::Aspect(aspect) = &facts[0].positive[0] else {
        panic!("aspect grant")
    };
    assert_eq!(aspect.name, "Transform");
    assert_eq!(
        aspect.arguments[0],
        AbstractType::Parameter(signature.parameters[1].id)
    );
    assert!(matches!(
        &aspect.arguments[1],
        AbstractType::Concrete(Type::Str)
    ));
    assert_eq!(
        aspect.identity,
        typed
            .graph
            .type_registry
            .resolve_type_id(&[], "Transform")
            .unwrap()
    );
    let forward = find("forward").abstract_signature.as_ref().unwrap();
    let negative = &forward.facts.as_ref().unwrap()[0].negative;
    assert!(matches!(&negative[0], AbstractBound::Aspect(aspect) if aspect.name == "Clone"));
    assert!(forward.facts.as_ref().unwrap()[0].positive.is_empty());
    assert!(
        find("nominal")
            .abstract_signature
            .as_ref()
            .unwrap()
            .facts
            .is_none(),
        "unresolved nominal identity cannot be complete facts"
    );
}

#[test]
fn abstract_signature_retains_row_equations_fieldwise_and_associated_equalities() {
    use crate::data::abstract_body::{AbstractBound, AbstractType};
    let typed = typecheck_source(
        "abstract_row_facts.mtl",
        r#"
aspect Source { type Item; fun take(&self) -> Item; }
fun extract<T: Source<Item = i64>>(value: &T) -> i64 { value.take() }
fun strip<row R, row Rest>(value: { ..R }) -> { ..Rest }
where R = { token: String, ..Rest } {
    let { token: _, ..rest } := value;
    rest
}
fun clone_row<row R>(value: &{ ..R }) -> { ..R } where all R: Clone { value.clone() }
fun main() {}
"#,
    )
    .report;
    let find = |name: &str| {
        typed
            .graph
            .modules
            .iter()
            .flat_map(|module| &module.decls)
            .find_map(|decl| match decl {
                TypedDecl::Fun(fun) if fun.name == name => Some(fun),
                _ => None,
            })
            .unwrap()
    };
    let extract = find("extract").abstract_signature.as_ref().unwrap();
    let equality = &extract.facts.as_ref().unwrap()[0].associated_equalities[0];
    assert_eq!(equality.aspect.name, "Source");
    assert_eq!(equality.name, "Item");
    assert_eq!(equality.ty, AbstractType::Concrete(Type::I64));
    let strip = find("strip").abstract_signature.as_ref().unwrap();
    let strip_facts = strip.facts.as_ref().unwrap();
    let remainder = &strip_facts[1].remainders[0];
    assert_eq!(remainder.source, strip.parameters[0].id);
    assert_eq!(remainder.removed, ["token"]);
    assert!(strip_facts[0].record_kind);
    assert!(strip_facts[0].positive.iter().any(|bound| matches!(bound,
        AbstractBound::Row { fields, open: true } if fields.iter().any(|(name, ty)| name == "token" && ty == &Some(AbstractType::Concrete(Type::Str))))));
    let clone = find("clone_row").abstract_signature.as_ref().unwrap();
    assert!(clone.facts.as_ref().unwrap().iter().any(|facts| facts.positive.iter().any(|bound|
        matches!(bound, AbstractBound::AllFields { aspects, .. } if aspects.iter().any(|aspect| aspect.name == "Clone")))));
}

#[test]
fn abstract_body_retains_definition_types_and_binding_identities() {
    use crate::data::abstract_body::{
        AbstractBodyPreparation, AbstractExprKind, AbstractStatement, AbstractType,
    };

    let typed = typecheck_source(
        "abstract_body.mtl",
        r#"
fun duplicate<T>(value: T) -> (T, T) { let first := value; (first, value) }
fun forward<row R>(value: { ..R }) -> { ..R } { return value; }
fun selected<T: Clone>(value: &T) -> T { value.clone() }
fun main() {}
"#,
    )
    .report;
    let find = |name: &str| {
        typed
            .graph
            .modules
            .iter()
            .flat_map(|module| &module.decls)
            .find_map(|decl| match decl {
                TypedDecl::Fun(fun) if fun.name == name => Some(fun),
                _ => None,
            })
            .unwrap()
    };
    let duplicate = find("duplicate");
    let Some(AbstractBodyPreparation::Typed(body)) = &duplicate.abstract_body else {
        panic!(
            "simple generic body was not retained: {:?}",
            duplicate.abstract_body
        );
    };
    let parameter = &body.parameters[0];
    assert_eq!(
        parameter.ty,
        AbstractType::Parameter(duplicate.abstract_signature.as_ref().unwrap().parameters[0].id)
    );
    let AbstractStatement::Bind {
        binding,
        value,
        mutable: false,
    } = &body.block.statements[0]
    else {
        panic!("immutable binding")
    };
    assert_ne!(binding.identity, parameter.identity);
    assert_eq!(binding.ty, parameter.ty);
    assert!(matches!(value.kind, AbstractExprKind::Binding(id) if id == parameter.identity));
    let AbstractExprKind::Tuple(items) = &body.block.tail.as_ref().unwrap().kind else {
        panic!("tuple tail")
    };
    assert!(matches!(items[0].kind, AbstractExprKind::Binding(id) if id == binding.identity));
    assert!(matches!(items[1].kind, AbstractExprKind::Binding(id) if id == parameter.identity));
    assert_eq!(items[0].ty, parameter.ty);
    let forward = find("forward");
    assert!(
        matches!(
            &forward.abstract_body,
            Some(AbstractBodyPreparation::Typed(_))
        ),
        "row forwarding: {:?}",
        forward.abstract_body
    );
    assert!(matches!(
        &find("selected").abstract_body,
        Some(AbstractBodyPreparation::Typed(_))
    ));
}

#[test]
fn abstract_body_retains_control_flow_without_guessing_coercions() {
    use crate::data::abstract_body::{
        AbstractBodyPreparation, AbstractExprKind, AbstractStatement,
    };
    let typed = typecheck_source(
        "abstract_control_flow.mtl",
        r#"
fun choose<T>(condition: boolean, first: T, second: T) -> T {
    if (condition) { first } else { second }
}
fun wait<T>(condition: boolean, value: T) -> T {
    while (condition) { loop { break; } }
    value
}
fun exit<T>(value: T) -> T { loop { break value; } }
fun main() {}
"#,
    )
    .report;
    let find = |name: &str| {
        typed
            .graph
            .modules
            .iter()
            .flat_map(|module| &module.decls)
            .find_map(|decl| match decl {
                TypedDecl::Fun(fun) if fun.name == name => Some(fun),
                _ => None,
            })
            .unwrap()
    };
    let Some(AbstractBodyPreparation::Typed(choose)) = &find("choose").abstract_body else {
        panic!("branch body: {:?}", find("choose").abstract_body)
    };
    assert!(matches!(
        choose.block.tail.as_ref().unwrap().kind,
        AbstractExprKind::If { .. }
    ));
    let Some(AbstractBodyPreparation::Typed(wait)) = &find("wait").abstract_body else {
        panic!("loop body: {:?}", find("wait").abstract_body)
    };
    assert!(matches!(
        wait.block.statements[0],
        AbstractStatement::While { .. }
    ));
    assert!(
        matches!(&find("exit").abstract_body, Some(AbstractBodyPreparation::Pending { reason }) if reason.contains("loop coercion"))
    );
}

#[test]
fn abstract_body_retains_aspect_method_dispatch_from_declared_bounds() {
    use crate::data::abstract_body::{
        AbstractBodyPreparation, AbstractExprKind, AbstractPassingMode, AbstractReceiverMode,
        AbstractType,
    };
    let typed = typecheck_source(
        "abstract_aspect_method.mtl",
        r#"
aspect Transform<A, B> { fun transform(&self, value: A) -> B; }
aspect Mutate { fun bump(&var self); }
fun translate<T: Transform<U, String>, U>(value: &T, input: U) -> String { value.transform(input) }
fun update<T: Mutate>(value: &var T) { value.bump(); }
fun main() {}
"#,
    )
    .report;
    let find = |name: &str| {
        typed
            .graph
            .modules
            .iter()
            .flat_map(|module| &module.decls)
            .find_map(|decl| match decl {
                TypedDecl::Fun(fun) if fun.name == name => Some(fun),
                _ => None,
            })
            .unwrap()
    };
    let method = |name: &str| {
        let Some(AbstractBodyPreparation::Typed(body)) = &find(name).abstract_body else {
            panic!("{name}: {:?}", find(name).abstract_body)
        };
        match &body.block.tail.as_ref().unwrap().kind {
            AbstractExprKind::MethodCall(call) => call,
            other => panic!("method: {other:?}"),
        }
    };
    let call = method("translate");
    assert_eq!(call.receiver_mode, AbstractReceiverMode::SharedReference);
    assert_eq!(
        call.aspect,
        typed
            .graph
            .type_registry
            .resolve_type_id(&[], "Transform")
            .unwrap()
    );
    assert_eq!(call.arguments[0].mode, AbstractPassingMode::Value);
    assert!(matches!(call.signature, AbstractType::Function { .. }));
    let update = find("update");
    let Some(AbstractBodyPreparation::Typed(body)) = &update.abstract_body else {
        panic!("update: {:?}", update.abstract_body)
    };
    let statement_kind = match &body.block.statements[0] {
        crate::data::abstract_body::AbstractStatement::Expr(expr) => &expr.kind,
        other => panic!("statement: {other:?}"),
    };
    let AbstractExprKind::MethodCall(call) = statement_kind else {
        panic!("method call")
    };
    assert_eq!(call.receiver_mode, AbstractReceiverMode::MutableReference);
    assert_eq!(
        call.aspect,
        typed
            .graph
            .type_registry
            .resolve_type_id(&[], "Mutate")
            .unwrap()
    );
}

#[test]
fn abstract_body_does_not_drop_bounded_method_generic_facts() {
    use crate::data::abstract_body::AbstractBodyPreparation;
    let typed = typecheck_source(
        "abstract_bounded_method_generic.mtl",
        r#"
aspect GenericSink { fun take<U: Copy>(&self, other: U); }
fun forward<T: GenericSink, U>(value: T, other: U) -> U { value.take(other); other }
fun main() {}
"#,
    )
    .report;
    let forward = typed
        .graph
        .modules
        .iter()
        .flat_map(|module| &module.decls)
        .find_map(|decl| match decl {
            TypedDecl::Fun(fun) if fun.name == "forward" => Some(fun),
            _ => None,
        })
        .unwrap();
    assert!(
        matches!(
            &forward.abstract_body,
            Some(AbstractBodyPreparation::Pending { reason })
                if reason.contains("method dispatch contract")
        ),
        "bounded method generic facts must not be discarded: {:?}",
        forward.abstract_body
    );
}

#[test]
fn abstract_body_retains_open_record_construction_and_spread_position() {
    use crate::data::abstract_body::{AbstractBodyPreparation, AbstractExprKind, AbstractType};
    let typed = typecheck_source(
        "abstract_record_construction.mtl",
        r#"
fun add_token<row R: !{token}>(value: { ..R }, token: String) -> { token: String, ..R } {
    { ..value, token = token }
}
fun main() {}
"#,
    )
    .report;
    let extend = typed
        .graph
        .modules
        .iter()
        .flat_map(|module| &module.decls)
        .find_map(|decl| match decl {
            TypedDecl::Fun(fun) if fun.name == "add_token" => Some(fun),
            _ => None,
        })
        .unwrap();
    let Some(AbstractBodyPreparation::Typed(body)) = &extend.abstract_body else {
        panic!("record construction: {:?}", extend.abstract_body)
    };
    let AbstractExprKind::RecordLiteral { fields, spread } =
        &body.block.tail.as_ref().unwrap().kind
    else {
        panic!("expected record literal")
    };
    assert_eq!(fields.len(), 1);
    assert_eq!(fields[0].0, "token");
    let Some((spread, position)) = spread else {
        panic!("open-row spread was not retained")
    };
    assert_eq!(*position, 0);
    assert!(matches!(spread.ty, AbstractType::Parameter(_)));
    assert!(matches!(
        body.block.tail.as_ref().unwrap().ty,
        AbstractType::OpenRecord { .. }
    ));
}

#[test]
fn abstract_body_retains_nominal_construction_with_instantiated_identity() {
    use crate::data::abstract_body::{AbstractBodyPreparation, AbstractExprKind, AbstractType};
    let typed = typecheck_source(
        "abstract_nominal_construction.mtl",
        r#"
struct Packet<T> { payload: T }
fun wrap<T>(value: T) -> Packet<T> { Packet { payload = value } }
fun main() {}
"#,
    )
    .report;
    let wrap = typed
        .graph
        .modules
        .iter()
        .flat_map(|module| &module.decls)
        .find_map(|decl| match decl {
            TypedDecl::Fun(fun) if fun.name == "wrap" => Some(fun),
            _ => None,
        })
        .unwrap();
    let Some(AbstractBodyPreparation::Typed(body)) = &wrap.abstract_body else {
        panic!("nominal construction: {:?}", wrap.abstract_body)
    };
    let AbstractExprKind::StructLiteral { fields } = &body.block.tail.as_ref().unwrap().kind else {
        panic!("expected nominal construction")
    };
    assert_eq!(fields[0].0, "payload");
    let AbstractType::Named {
        name, arguments, ..
    } = &body.block.tail.as_ref().unwrap().ty
    else {
        panic!("nominal type: {:?}", body.block.tail.as_ref().unwrap().ty)
    };
    assert_eq!(name, "Packet");
    assert!(matches!(arguments[0], AbstractType::Parameter(_)));
}

#[test]
fn abstract_body_retains_nominal_residual_projection_source() {
    use crate::data::abstract_body::{AbstractBodyPreparation, AbstractExprKind, AbstractType};
    let typed = typecheck_source(
        "abstract_residual_projection.mtl",
        r#"
struct Packet<T> { payload: T, token: String }
fun project<T>(value: Packet<T>) { let projected := value.{ payload }; }
fun main() {}
"#,
    )
    .report;
    let project = typed
        .graph
        .modules
        .iter()
        .flat_map(|module| &module.decls)
        .find_map(|decl| match decl {
            TypedDecl::Fun(fun) if fun.name == "project" => Some(fun),
            _ => None,
        })
        .unwrap();
    let Some(AbstractBodyPreparation::Typed(body)) = &project.abstract_body else {
        panic!("residual projection: {:?}", project.abstract_body)
    };
    let crate::data::abstract_body::AbstractStatement::Bind { value, .. } =
        &body.block.statements[0]
    else {
        panic!("expected residual-projection binding")
    };
    let AbstractExprKind::RecordProjection { source, fields } = &value.kind else {
        panic!("expected residual projection")
    };
    assert_eq!(fields, &["payload"]);
    assert!(matches!(source.kind, AbstractExprKind::Binding(_)));
    assert!(matches!(source.ty, AbstractType::Named { .. }));
    assert!(matches!(value.ty, AbstractType::Residual { .. }));
}

#[test]
fn abstract_body_retains_plain_local_rebinding() {
    use crate::data::abstract_body::{
        AbstractBodyPreparation, AbstractExprKind, AbstractStatement,
    };
    let typed = typecheck_source(
        "abstract_assignment.mtl",
        r#"
fun reset<T>(initial: T, replacement: T) -> T {
    var value := initial;
    value := replacement;
    value
}
fun main() {}
"#,
    )
    .report;
    let reset = typed
        .graph
        .modules
        .iter()
        .flat_map(|module| &module.decls)
        .find_map(|decl| match decl {
            TypedDecl::Fun(fun) if fun.name == "reset" => Some(fun),
            _ => None,
        })
        .unwrap();
    let Some(AbstractBodyPreparation::Typed(body)) = &reset.abstract_body else {
        panic!("assignment: {:?}", reset.abstract_body)
    };
    let AbstractStatement::Bind { binding, .. } = &body.block.statements[0] else {
        panic!("expected initial binding")
    };
    let AbstractStatement::Expr(assignment) = &body.block.statements[1] else {
        panic!("expected assignment statement")
    };
    assert!(matches!(
        assignment.kind,
        AbstractExprKind::Assign { target, .. } if target == binding.identity
    ));
}

#[test]
fn abstract_body_retains_generic_owned_closure_capture() {
    use crate::data::abstract_body::{
        AbstractBodyPreparation, AbstractCaptureMode, AbstractExprKind, AbstractStatement,
    };
    let typed = typecheck_source(
        "abstract_closure.mtl",
        r#"
fun relay<T>(value: T) {
    let f := [value] once || { value };
}
fun main() {}
"#,
    )
    .report;
    let relay = typed
        .graph
        .modules
        .iter()
        .flat_map(|module| &module.decls)
        .find_map(|decl| match decl {
            TypedDecl::Fun(fun) if fun.name == "relay" => Some(fun),
            _ => None,
        })
        .unwrap();
    let Some(AbstractBodyPreparation::Typed(body)) = &relay.abstract_body else {
        panic!("closure: {:?}", relay.abstract_body)
    };
    let AbstractStatement::Bind { value, .. } = &body.block.statements[0] else {
        panic!("expected closure binding")
    };
    let AbstractExprKind::Closure(closure) = &value.kind else {
        panic!("expected closure")
    };
    assert_eq!(closure.captures.len(), 1);
    assert_eq!(closure.captures[0].mode, AbstractCaptureMode::Owned);
    assert!(matches!(
        closure.body.tail.as_ref().unwrap().kind,
        AbstractExprKind::Binding(_)
    ));
}

#[test]
fn abstract_body_retains_call_contracts_borrows_and_tuple_places() {
    use crate::data::abstract_body::{
        AbstractBodyPreparation, AbstractExprKind, AbstractPassingMode, AbstractStatement,
        AbstractType,
    };
    use crate::data::types::{CallMultiplicity, CallMutation, UseMultiplicity};
    use crate::identity::BindingId;
    use crate::ownership::place::Projection;
    let typed = typecheck_source(
        "abstract_calls.mtl",
        r#"
fun pass<T>(value: T) -> T { value }
fun read<T>(value: &T) -> &T { value }
fun edit<T>(value: &var T) {}
fun relay<T>(value: T) -> T { pass(value) }
fun borrowed<T>(value: &T) -> &T { read(value) }
fun mutable<T>(value: &var T) { edit(value); }
fun lend<T>(value: T) { read(&value); }
fun temporary<T>(value: T, other: i64) { read(&(value, other)); }
fun first<T, U>(pair: (T, U)) -> T { pair.0 }
fun read_first<T: Copy, U>(pair: &(T, U)) -> T { pair.0 }
fun recursive<T>(value: T) -> T { recursive(value) }
fun invoke_once<T>(f: once |T| -> T, value: T) -> T { f(value) }
fun invoke_mut<T>(f: var |T| -> T, value: T) -> T { f(value) }
fun pointer<T>(f: &|T| -> T, value: T) -> T { f(value) }
fun temp_call<T>(value: T) { read(&pass(value)); }
fun shadow<T>(f: once |T| -> T, value: T) -> T { let recursive := f; recursive(value) }
fun main() {}
"#,
    )
    .report;
    let find = |name: &str| {
        typed
            .graph
            .modules
            .iter()
            .flat_map(|module| &module.decls)
            .find_map(|decl| match decl {
                TypedDecl::Fun(fun) if fun.name == name => Some(fun),
                _ => None,
            })
            .unwrap()
    };
    let body = |name: &str| match &find(name).abstract_body {
        Some(AbstractBodyPreparation::Typed(body)) => body,
        other => panic!("{name} not retained: {other:?}"),
    };
    let tail_call = |name: &str| match &body(name).block.tail.as_ref().unwrap().kind {
        AbstractExprKind::Call(call) => call,
        other => panic!("call expected: {other:?}"),
    };
    let relay = tail_call("relay");
    assert!(
        matches!(relay.callee.kind, AbstractExprKind::Binding(BindingId::Global(id)) if id == find("pass").def_id.unwrap())
    );
    assert_eq!(relay.arguments[0].mode, AbstractPassingMode::Value);
    assert_eq!(
        relay.arguments[0].value.ty,
        AbstractType::Parameter(
            find("relay")
                .abstract_signature
                .as_ref()
                .unwrap()
                .parameters[0]
                .id
        )
    );
    assert_eq!(
        tail_call("borrowed").arguments[0].mode,
        AbstractPassingMode::SharedReference
    );
    let statement_call = |name: &str| match &body(name).block.statements[0] {
        AbstractStatement::Expr(expr) => match &expr.kind {
            AbstractExprKind::Call(call) => call,
            other => panic!("call: {other:?}"),
        },
        other => panic!("statement: {other:?}"),
    };
    assert_eq!(
        statement_call("mutable").arguments[0].mode,
        AbstractPassingMode::MutableReference
    );
    assert!(matches!(
        &statement_call("lend").arguments[0].value.kind,
        AbstractExprKind::Borrow {
            temporary: false,
            mutable: false,
            ..
        }
    ));
    assert!(matches!(
        &statement_call("temporary").arguments[0].value.kind,
        AbstractExprKind::Borrow {
            temporary: true,
            ..
        }
    ));
    let first = body("first").block.tail.as_ref().unwrap().place().unwrap();
    assert_eq!(first.binding, body("first").parameters[0].identity);
    assert_eq!(first.projections, [Projection::TupleIndex(0)]);
    let borrowed = body("read_first")
        .block
        .tail
        .as_ref()
        .unwrap()
        .place()
        .unwrap();
    assert_eq!(
        borrowed.projections,
        [Projection::Deref, Projection::TupleIndex(0)]
    );
    assert!(
        matches!(tail_call("recursive").callee.kind, AbstractExprKind::Binding(BindingId::Global(id)) if id == find("recursive").def_id.unwrap())
    );
    assert!(matches!(
        tail_call("invoke_once").signature,
        AbstractType::Function {
            call: CallMultiplicity::Once,
            usage: UseMultiplicity::Move,
            ..
        }
    ));
    assert!(matches!(
        tail_call("invoke_mut").signature,
        AbstractType::Function {
            mutation: CallMutation::Mutating,
            ..
        }
    ));
    assert!(tail_call("pointer").auto_dereference);
    let AbstractExprKind::Borrow {
        value: temporary,
        temporary: true,
        ..
    } = &statement_call("temp_call").arguments[0].value.kind
    else {
        panic!("call return stored in temporary")
    };
    assert!(matches!(temporary.kind, AbstractExprKind::Call(_)));
    assert!(
        matches!(&find("shadow").abstract_body, Some(AbstractBodyPreparation::Pending { reason }) if reason.contains("local generic call target"))
    );
}

#[test]
fn abstract_body_retains_nominal_structural_and_row_granted_field_selections() {
    use crate::data::abstract_body::{
        AbstractBodyPreparation, AbstractExprKind, AbstractFieldSelection,
    };
    use crate::ownership::place::Projection;
    let typed = typecheck_source(
        "abstract_fields.mtl",
        r#"
struct Box<T> { value: T }
fun take<T>(box: Box<T>) -> T { box.value }
fun peek<T: Copy>(box: &Box<T>) -> T { box.value }
fun known<T>(value: { token: String, item: T }) -> String { value.token }
fun granted<record R: { token: String, .. }>(value: R) -> String { value.token }
fun main() {}
"#,
    )
    .report;
    let find = |name: &str| {
        typed
            .graph
            .modules
            .iter()
            .flat_map(|module| &module.decls)
            .find_map(|decl| match decl {
                TypedDecl::Fun(fun) if fun.name == name => Some(fun),
                _ => None,
            })
            .unwrap()
    };
    let body = |name: &str| match &find(name).abstract_body {
        Some(AbstractBodyPreparation::Typed(body)) => body,
        other => panic!("{name} not retained: {other:?}"),
    };
    let field = |name: &str| match &body(name).block.tail.as_ref().unwrap().kind {
        AbstractExprKind::FieldAccess { selection, .. } => selection,
        other => panic!("field: {other:?}"),
    };
    let AbstractFieldSelection::Nominal {
        field: selected, ..
    } = field("take")
    else {
        panic!("nominal field")
    };
    let owner = typed
        .graph
        .type_registry
        .resolve_type_id(&[], "Box")
        .unwrap();
    let expected = typed
        .graph
        .type_registry
        .struct_fields_by_id(owner)
        .unwrap()[0]
        .id
        .unwrap();
    assert_eq!(*selected, expected, "selected field belongs to {owner:?}");
    assert!(
        matches!(field("known"), AbstractFieldSelection::Structural { label } if label == "token")
    );
    assert!(
        matches!(field("granted"), AbstractFieldSelection::Granted { parameter, label } if *parameter == find("granted").abstract_signature.as_ref().unwrap().parameters[0].id && label == "token")
    );
    let place = body("peek").block.tail.as_ref().unwrap().place().unwrap();
    assert_eq!(place.binding, body("peek").parameters[0].identity);
    assert_eq!(
        place.projections,
        [
            Projection::Deref,
            Projection::field_with_id("value", Some(expected))
        ]
    );
}

#[test]
fn abstract_field_selection_preserves_equal_spelled_cross_module_owners() {
    use crate::data::abstract_body::{
        AbstractBodyPreparation, AbstractExprKind, AbstractFieldSelection,
    };
    let typed = typecheck_sources("abstract_modules/main.mtl", "import alpha::take_alpha; import beta::take_beta; fun main() {}", &[
        ("alpha.mtl", "public struct Box<T> { public value: T } public fun take_alpha<T>(value: Box<T>) -> T { value.value }"),
        ("beta.mtl", "public struct Box<T> { public value: T } public fun take_beta<T>(value: Box<T>) -> T { value.value }"),
    ]).report;
    let selected = |name: &str| {
        let function = typed
            .graph
            .modules
            .iter()
            .flat_map(|module| &module.decls)
            .find_map(|decl| match decl {
                TypedDecl::Fun(fun) if fun.name == name => Some(fun),
                _ => None,
            })
            .unwrap();
        let Some(AbstractBodyPreparation::Typed(body)) = &function.abstract_body else {
            panic!("{name}: {:?}", function.abstract_body)
        };
        let AbstractExprKind::FieldAccess {
            selection: AbstractFieldSelection::Nominal { field, .. },
            ..
        } = &body.block.tail.as_ref().unwrap().kind
        else {
            panic!("nominal field")
        };
        *field
    };
    let alpha = selected("take_alpha");
    let beta = selected("take_beta");
    assert_ne!(alpha, beta);
    for (module, field) in [("alpha", alpha), ("beta", beta)] {
        let owner = typed
            .graph
            .type_registry
            .resolve_type_id(&[module.to_string()], "Box")
            .unwrap();
        assert_eq!(
            field,
            typed
                .graph
                .type_registry
                .struct_fields_by_id(owner)
                .unwrap()[0]
                .id
                .unwrap()
        );
    }
}

#[test]
fn owned_capture_type_is_snapshotted_before_body_restoration() {
    let typed = typecheck_source(
        "capture_entry.mtl",
        r#"
struct Pair { left: String, right: String }
fun make() -> once var || -> Pair {
    var pair := Pair { left = "old", right = "gone" };
    let left := pair.left;
    let right := pair.right;
    [pair] once var || -> Pair {
        pair.left := "new";
        pair.right := "back";
        pair
    }
}
fun main() {}
"#,
    )
    .report;
    let fun = typed
        .graph
        .modules
        .iter()
        .flat_map(|module| &module.decls)
        .find_map(|decl| match decl {
            TypedDecl::Fun(fun) if fun.name == "make" => Some(fun),
            _ => None,
        })
        .expect("make is present");
    let FunBody::Typed(body) = &fun.body else {
        panic!("make has a typed body");
    };
    let TypedExpr::Closure {
        owned_capture_types,
        body,
        ..
    } = body.tail.as_deref().unwrap()
    else {
        panic!("make returns a closure");
    };
    assert!(
        matches!(&owned_capture_types[0].1, Type::Residual { fields, .. } if fields.is_empty())
    );
    assert!(
        matches!(body.tail.as_deref().unwrap().ty(), Type::Named(name, ..) if name.ends_with("Pair"))
    );
}

/// The non-comment lines of every `pipeline/type_checking/construction*` source
/// file — excluding this test module itself, which quotes the very API names
/// these checks forbid (as string literals in its own assertions).
fn construction_code() -> Vec<(String, String)> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/pipeline/type_checking");
    let mut files = Vec::new();
    for entry in std::fs::read_dir(root.join("construction")).expect("construction/ exists") {
        let path = entry.expect("dir entry").path();
        if path.file_name().and_then(|n| n.to_str()) != Some("tests.rs") {
            files.push(path);
        }
    }
    files
        .into_iter()
        .map(|path| {
            let code = std::fs::read_to_string(&path)
                .expect("construction source readable")
                .lines()
                .filter(|line| !line.trim_start().starts_with("//"))
                .collect::<Vec<_>>()
                .join("\n");
            (path.display().to_string(), code)
        })
        .collect()
}

/// The full pipeline (parse → resolve → identity → normalize → coherence →
/// typecheck) that most tests below need before they can inspect a typed
/// program's identity annotations. Bundles the identity tables alongside the
/// typed report since a couple of tests need to rebuild a `TypeCtx` from
/// them directly, rather than only reading the already-typed IR.
struct TypedFixture {
    report: CheckGraphReport,
    normalized: NormalizedModuleGraph,
    members: MemberTable,
    allocation: Allocation,
    names: Rc<ResolvedNames>,
}

fn typecheck_source(root: &str, source: &str) -> TypedFixture {
    typecheck_sources(root, source, &[])
}

fn typecheck_sources(root: &str, source: &str, files: &[(&str, &str)]) -> TypedFixture {
    use crate::pipeline::parsing::module_loader::{self, MultiFileSourceProvider};

    let mut provider = MultiFileSourceProvider::new(root, source);
    for (path, source) in files {
        provider = provider.with_file(*path, *source);
    }
    let graph =
        module_loader::load_virtual_root_with(root, &provider).expect("in-memory root loads");
    let names = crate::pipeline::name_resolution::name_resolver::resolve(&graph).expect("resolves");
    let members = crate::identity::collect_members_for_graph(&graph, &names);
    let allocation = crate::identity::allocate_for_graph(&graph, &names);
    let normalized =
        crate::pipeline::path_normalization::normalize(graph, names.clone()).expect("normalizes");
    crate::pipeline::coherence::check(&normalized).expect("coheres");
    let report = check_graph_with_report(
        &normalized,
        &CorePrelude::default(),
        Some(crate::identity::FrozenIdentity {
            members: &members,
            binding_spans: &allocation.binding_spans,
        }),
    )
    .expect("typechecks");
    TypedFixture {
        report,
        normalized,
        members,
        allocation,
        names,
    }
}

// arch-verifies: ["arch.type-inference.requirement-3"]
#[test]
fn from_impl_lookup_runs_in_inference_not_construction() {
    for (path, code) in construction_code() {
        assert!(
            !code.contains("has_from_impl"),
            "{path} looks up `From` impls; `?` coercion is decided in inference (`infer_propagate_error`)"
        );
    }
}

// arch-verifies: ["arch.type-inference.requirement-4"]
#[test]
fn construction_never_runs_the_constraint_solver() {
    for (path, code) in construction_code() {
        for forbidden in ["InferContext", ".solve(", "solve_constraints", "occurs_in"] {
            assert!(
                !code.contains(forbidden),
                "{path} references `{forbidden}`; construction consumes solved facts and must not re-run inference"
            );
        }
    }
}

/// metel-core#1052 (Option A): `construct_generic_body`'s runtime
/// reconstruction of a generic function body gets real `BindingId`s too,
/// not just the ahead-of-time construction pass — because `body` is the
/// exact same `ast::Block` the identity walk already processed, so its
/// `binding_spans` entries apply unchanged regardless of which concrete
/// type this particular call instantiates.
// arch-verifies: ["arch.type-construction.requirement-2"]
#[test]
fn construct_generic_body_stamps_a_real_local_id() {
    use crate::data::typed_ast::TypedExpr;
    use crate::data::types::Type;
    use crate::identity::BindingId;

    let root = "generic.mtl";
    let source = "fun pick<T>(a: T, b: T) -> T {\n\tlet r := a;\n\tr\n}\n";
    let TypedFixture {
        report: typed_report,
        normalized,
        members,
        allocation,
        names,
    } = typecheck_source(root, source);

    // The raw (untyped) declaration — `construct_generic_body` takes the
    // same `ast::Block` the identity walk already saw. std::core is a
    // synthesized module ahead of the user's root, so find `pick` by name
    // rather than assuming module order.
    let module = normalized
        .modules()
        .iter()
        .find(|m| {
            m.program
                .decls
                .iter()
                .any(|d| matches!(d, Decl::Fun(f) if f.name == "pick"))
        })
        .expect("the module declaring `fun pick`");
    let Decl::Fun(fun) = module
        .program
        .decls
        .iter()
        .find(|d| matches!(d, Decl::Fun(f) if f.name == "pick"))
        .expect("`fun pick` in the raw graph")
    else {
        unreachable!()
    };
    let typed_module = typed_report
        .graph
        .modules
        .iter()
        .find(|m| m.module_path == module.module_path)
        .expect("the matching typed module");
    let scheme = typed_module
        .scheme_env
        .get("pick")
        .expect("a scheme for `pick`")
        .clone();

    let type_ctx = crate::pipeline::type_checking::type_engine::TypeCtx {
        scheme_env: typed_module.scheme_env.clone(),
        registry: typed_report.graph.type_registry.clone(),
        members: Some(Rc::new(members)),
        binding_spans: Some(Rc::new(allocation.binding_spans)),
        symbols: Some(Rc::new(names.symbols.clone())),
        current_module: typed_module.module_path.clone(),
    };

    let typed_block = construct_generic_body(
        &scheme,
        &fun.params,
        &[Type::I64, Type::I64],
        &fun.body,
        &fun.span,
        &type_ctx,
        crate::pipeline::type_checking::GenericBodyOptions::default(),
    )
    .expect("reconstructs for i64 args");

    let r_id = typed_block
        .stmts
        .iter()
        .find_map(|d| match d {
            TypedDecl::Let(ld) if ld.name == "r" => ld.local_id,
            _ => None,
        })
        .expect("a local in a runtime-reconstructed generic body carries a LocalId");
    let TypedExpr::Ident(_, Some(BindingId::Local(used)), _, _) =
        typed_block.tail.as_deref().unwrap()
    else {
        panic!("the tail `r` should be a resolved local reference");
    };
    assert_eq!(
        *used, r_id,
        "the reconstructed body's `r` use resolves to the same LocalId as its `let`"
    );

    // Reconstructing the same generic body for a *different* concrete
    // instantiation yields the same `LocalId` for `r` — a binding's
    // lexical identity does not depend on which type parameterized this
    // particular call (relevant to go-to-definition / find-references
    // across monomorphizations).
    let typed_block_str = construct_generic_body(
        &scheme,
        &fun.params,
        &[Type::Str, Type::Str],
        &fun.body,
        &fun.span,
        &type_ctx,
        crate::pipeline::type_checking::GenericBodyOptions::default(),
    )
    .expect("reconstructs for str args");
    let r_id_str = typed_block_str
        .stmts
        .iter()
        .find_map(|d| match d {
            TypedDecl::Let(ld) if ld.name == "r" => ld.local_id,
            _ => None,
        })
        .expect("`let r` carries a LocalId in the str instantiation too");
    assert_eq!(
        r_id, r_id_str,
        "the same source binding keeps one LocalId across monomorphizations"
    );
}

/// metel-core#1098: `expr?` desugars (in `construct_propagate_error`) into
/// a synthesized match with an `Ok`-arm `value` binding and an `Err`-arm
/// `error` binding — neither has a source pattern to hang an id off, so
/// the identity walk binds one synthetic id at the `?`'s own span
/// (`allocate.rs`'s `PropagateError` case) and construction shares it
/// between both arms, since they're mutually exclusive at runtime.
#[test]
fn propagate_error_desugar_shares_one_local_id_between_arms() {
    use crate::data::typed_ast::{FunBody, TypedExpr, TypedPattern};

    let root = "prop.mtl";
    let source = "fun get_id() -> Result<i64, i64> { Result::Ok { value = 5 } }\n\
                       fun use_it() -> Result<i64, i64> {\n\
                       \tlet v := get_id()?;\n\
                       \tResult::Ok { value = v }\n\
                       }\n";
    let typed_report = typecheck_source(root, source).report;

    let module = typed_report
        .graph
        .modules
        .iter()
        .find(|m| {
            m.decls
                .iter()
                .any(|d| matches!(d, TypedDecl::Fun(f) if f.name == "use_it"))
        })
        .expect("the module declaring `use_it`");
    let TypedDecl::Fun(fun) = module
        .decls
        .iter()
        .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "use_it"))
        .expect("`use_it`")
    else {
        unreachable!()
    };
    let FunBody::Typed(body) = &fun.body else {
        panic!("use_it should have a typed body");
    };
    let match_expr = body
        .stmts
        .iter()
        .find_map(|d| match d {
            TypedDecl::Let(ld) if ld.name == "v" => match &ld.value {
                TypedExpr::Match(m) => Some(m),
                _ => None,
            },
            _ => None,
        })
        .expect("the `?` desugars to a match assigned to `v`");

    let ok_id = match &match_expr.arms[0].pattern {
        TypedPattern::EnumVariant { fields, .. } => fields[0].2,
        other => panic!("expected the Ok-arm's EnumVariant pattern, got {other:?}"),
    };
    let err_id = match &match_expr.arms[1].pattern {
        TypedPattern::EnumVariant { fields, .. } => fields[0].2,
        other => panic!("expected the Err-arm's EnumVariant pattern, got {other:?}"),
    };
    assert!(
        ok_id.is_some(),
        "the `?` desugar's Ok-arm binding should carry a LocalId"
    );
    assert_eq!(
        ok_id, err_id,
        "the Ok-arm value and Err-arm error share one LocalId \
             (mutually exclusive match arms, safe to share one frame slot)"
    );
}

/// metel-core#1100: a top-level `let`/`mut`'s own initializer expression
/// is now walked by the identity allocator (`allocate.rs`'s
/// `walk_value_body`, wired into `allocate_module`'s top-level loop) —
/// previously only `Decl::Fun`/`Impl`/`Aspect` bodies were, so a
/// reference *inside* a top-level initializer (e.g. `let apply_fn :=
/// add_one;`) never got a `PositionHit::Reference` entry to promote and
/// stayed `BindingId`-less. This also fixed metel-core#1099 as a side
/// effect: a top-level `let`-bound closure literal's own parameters are
/// inside that same never-walked initializer.
#[test]
fn toplevel_let_initializer_reference_carries_a_symbol_id() {
    use crate::data::typed_ast::{FunBody, TypedExpr};
    use crate::identity::BindingId;

    let root = "toplevel_init.mtl";
    let source = "fun add_one(x: i64) -> i64 { x + 1 }\n\
                       let apply_fn := add_one;\n\
                       fun main() -> i64 {\n\
                       \tapply_fn(41)\n\
                       }\n";
    let typed_report = typecheck_source(root, source).report;

    let module = typed_report
        .graph
        .modules
        .iter()
        .find(|m| {
            m.decls
                .iter()
                .any(|d| matches!(d, TypedDecl::Let(ld) if ld.name == "apply_fn"))
        })
        .expect("the module declaring `apply_fn`");
    let TypedDecl::Let(apply_fn) = module
        .decls
        .iter()
        .find(|d| matches!(d, TypedDecl::Let(ld) if ld.name == "apply_fn"))
        .expect("`let apply_fn`")
    else {
        unreachable!()
    };
    let TypedExpr::Ident(name, binding, ..) = &apply_fn.value else {
        panic!(
            "apply_fn's initializer should be a bare Ident reference to `add_one`, got {:?}",
            apply_fn.value
        );
    };
    assert_eq!(name, "add_one");
    assert!(
        matches!(binding, Some(BindingId::Global(_))),
        "the `add_one` reference inside apply_fn's own initializer should \
             carry its declaration's SymbolId, not stay identity-less"
    );

    // The call inside `main` still resolves through `Call::callee_id`, as
    // it did before this fix (this file's earlier check makes sure the
    // fix didn't regress the already-working case).
    let TypedDecl::Fun(main) = module
        .decls
        .iter()
        .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "main"))
        .expect("`main`")
    else {
        unreachable!()
    };
    let FunBody::Typed(body) = &main.body else {
        panic!("main should have a typed body");
    };
    let TypedExpr::Call { callee_id, .. } = body.tail.as_deref().unwrap() else {
        panic!(
            "main's tail should be the apply_fn(41) call, got {:?}",
            body.tail
        );
    };
    assert!(
        callee_id.is_some(),
        "apply_fn(41) should still dispatch via Call::callee_id"
    );
}

/// metel-core#1096: an implicit (no `[...]` list) closure's free
/// `Copy`-typed variables are materialized as `CaptureSpec::Clone`
/// entries (`verify_closure_capture_list`'s new return value), each
/// carrying the same `LocalId` as its enclosing binding — here,
/// `make_adder`'s own parameter `x`, captured implicitly by the closure
/// it returns.
#[test]
fn implicit_copy_capture_carries_the_enclosing_local_id() {
    use crate::data::typed_ast::{FunBody, TypedExpr};

    let root = "implicit_capture.mtl";
    let source = "fun make_adder(x: i64) -> |i64| -> i64 {\n\
                       \t|y: i64| -> i64 { x + y }\n\
                       }\n\
                       fun main() -> i64 {\n\
                       \tlet add5 := make_adder(5);\n\
                       \tadd5(3)\n\
                       }\n";
    let typed_report = typecheck_source(root, source).report;

    let module = typed_report
        .graph
        .modules
        .iter()
        .find(|m| {
            m.decls
                .iter()
                .any(|d| matches!(d, TypedDecl::Fun(f) if f.name == "make_adder"))
        })
        .expect("the module declaring `make_adder`");
    let TypedDecl::Fun(fun) = module
        .decls
        .iter()
        .find(|d| matches!(d, TypedDecl::Fun(f) if f.name == "make_adder"))
        .expect("`make_adder`")
    else {
        unreachable!()
    };
    let FunBody::Typed(body) = &fun.body else {
        panic!("make_adder should have a typed body");
    };
    let TypedExpr::Closure {
        captures,
        capture_ids,
        ..
    } = body.tail.as_deref().unwrap()
    else {
        panic!(
            "make_adder's tail should be the inner closure, got {:?}",
            body.tail
        );
    };
    assert_eq!(
        captures.len(),
        1,
        "the implicit closure should materialize one capture for `x`, got {captures:?}"
    );
    assert!(
        matches!(&captures[0], crate::data::ast::CaptureSpec::Clone { name, .. } if name == "x"),
        "the materialized capture should be a Clone of `x`, got {:?}",
        captures[0]
    );
    assert_eq!(
        capture_ids, &fun.param_ids,
        "the materialized capture's LocalId should match make_adder's own \
             parameter x's LocalId — same binding, same identity"
    );
    assert!(
        matches!(capture_ids[0], Some(_)),
        "the capture should carry a real LocalId, not None"
    );
}

/// metel-core#1101: `extend<T> T[]: Aspect { ... }` (the structural
/// array-pattern target) previously had no `SymbolId` interned for its
/// methods at all -- `name_resolver.rs`'s `impl_target_name` and
/// `identity/allocate.rs`'s `allocate_module` both only recognized
/// `TypeExpr::Named` targets, silently skipping `TypeExpr::Array` ones.
/// With no owner `SymbolId` to hash against, every local inside such a
/// method's body -- including `self` -- got no `LocalId` at all. Both
/// now key these under a synthetic owner name ("[]Array" as of
/// metel-core#1121, originally the bare "Array" until that collided with
/// a literal `extend Array: Aspect { ... }` nominal target).
#[test]
fn array_extend_method_self_param_carries_a_local_id() {
    let root = "array_extend.mtl";
    let source = "aspect Show {\n\
                       \tfun show(&self) -> i64;\n\
                       }\n\
                       extend<T> [T]: Show {\n\
                       \tfun show(&self) -> i64 {\n\
                       \t\tvar n := 0;\n\
                       \t\tfor (item in self) {\n\
                       \t\t\tn += 1;\n\
                       \t\t}\n\
                       \t\treturn n;\n\
                       \t}\n\
                       }\n\
                       fun main() -> i64 {\n\
                       \t[1, 2, 3].show()\n\
                       }\n";
    let typed_report = typecheck_source(root, source).report;

    let method = typed_report
        .graph
        .modules
        .iter()
        .find_map(|m| {
            m.decls.iter().find_map(|d| match d {
                TypedDecl::Impl(ib)
                    if matches!(ib.target_type, crate::data::ast::TypeExpr::Array(_)) =>
                {
                    ib.methods.iter().find(|f| f.name == "show")
                }
                _ => None,
            })
        })
        .expect("the array-extend impl's `show` method");
    assert!(
        !method.param_ids.is_empty(),
        "show(&self) should have at least one param_ids entry"
    );
    assert!(
        method.param_ids[0].is_some(),
        "the self param should carry a real LocalId, not None"
    );
}

#[test]
fn nominal_array_extend_does_not_collide_with_structural_array_extend() {
    // metel-core#1121: a literal `extend Array: Aspect { ... }` (a real,
    // reachable nominal impl target -- `Array` is accepted as a written
    // type name, see `conversions.rs`'s `("Array", 1)` case) used to be
    // keyed under the exact same synthetic owner name ("Array") as
    // `extend<T> T[]: Aspect { ... }` (the structural array-pattern
    // target, metel-core#1101). With the same owner and the same lexical
    // shape (one `var` binding named `n`), both methods' locals hashed
    // to the *same* LocalId. Fixed by keying the structural case under
    // "[]Array" instead, a string no `TypeExpr::Named` target can ever
    // spell (Metel identifiers can't contain `[`/`]`).
    let root = "array_owner_collision.mtl";
    let source = "aspect Show {\n\
                       \tfun show(&self) -> i64;\n\
                       }\n\
                       extend Array: Show {\n\
                       \tfun show(&self) -> i64 {\n\
                       \t\tvar n := 1;\n\
                       \t\tn\n\
                       \t}\n\
                       }\n\
                       extend<T> [T]: Show {\n\
                       \tfun show(&self) -> i64 {\n\
                       \t\tvar n := 2;\n\
                       \t\tn\n\
                       \t}\n\
                       }\n\
                       fun main() -> i64 {\n\
                       \t[1, 2, 3].show()\n\
                       }\n";
    let typed_report = typecheck_source(root, source).report;

    // Search across every module's decls, not just the root's own --
    // std::core's prelude has its own `extend<T> T[]: ...` impls loaded
    // alongside it, so restricting to "the first module with an Impl
    // decl" would find the wrong module entirely.
    let all_decls = typed_report
        .graph
        .modules
        .iter()
        .flat_map(|m| m.decls.iter());
    let nominal_self_id = all_decls
            .clone()
            .find_map(|d| match d {
                TypedDecl::Impl(ib)
                    if matches!(&ib.target_type, crate::data::ast::TypeExpr::Named(n, _) if n == "Array") =>
                {
                    ib.methods.iter().find(|f| f.name == "show")
                }
                _ => None,
            })
            .expect("the nominal `extend Array` impl's `show` method")
            .param_ids[0]
            .expect("nominal self param should carry a real LocalId");
    let structural_self_id = all_decls
        .clone()
        .find_map(|d| match d {
            TypedDecl::Impl(ib)
                if matches!(ib.target_type, crate::data::ast::TypeExpr::Array(_)) =>
            {
                ib.methods.iter().find(|f| f.name == "show")
            }
            _ => None,
        })
        .expect("the structural `extend<T> [T]` impl's `show` method")
        .param_ids[0]
        .expect("structural self param should carry a real LocalId");

    assert_ne!(
        nominal_self_id, structural_self_id,
        "the nominal and structural Array impls' self params must not \
             collide onto the same LocalId"
    );
}

#[test]
fn qualified_path_static_method_call_carries_a_type_id() {
    // metel-core#1093: a static-method reference (`Type::method`,
    // resolved via `ctx.method_env`) constructs a `TypedExpr::Path` — it
    // should carry the owning type's SymbolId.
    //
    // The sibling case (a fieldful enum-variant path used as a curried
    // constructor value, e.g. `Colour::Custom`) is stamped by the same
    // construction code with a `variant_id` too, but isn't covered here:
    // that surface form doesn't type-check at all today (metel-core#1108,
    // a separate, pre-existing inference gap found while writing this
    // test) — every real fieldful-variant reference in the codebase goes
    // through `match` or an immediate struct literal instead, neither of
    // which builds a `TypedExpr::Path`.
    use crate::data::typed_ast::{FunBody, TypedExpr};

    let root = "qualified_path.mtl";
    let source = "struct Point {\n\
                       \tx: i64,\n\
                       }\n\
                       extend Point {\n\
                       \tfun origin() -> Point {\n\
                       \t\tPoint { x = 0 }\n\
                       \t}\n\
                       }\n\
                       fun main() -> i64 {\n\
                       \tlet p := Point::origin();\n\
                       \tp.x\n\
                       }\n";
    let typed_report = typecheck_source(root, source).report;

    let main_body = typed_report
        .graph
        .modules
        .iter()
        .find_map(|m| {
            m.decls.iter().find_map(|d| match d {
                TypedDecl::Fun(f) if f.name == "main" => match &f.body {
                    FunBody::Typed(block) => Some(block),
                    _ => None,
                },
                _ => None,
            })
        })
        .expect("typed `main` body");

    let value = main_body
        .stmts
        .iter()
        .find_map(|d| match d {
            TypedDecl::Let(l) if l.name == "p" => Some(&l.value),
            _ => None,
        })
        .expect("`let p` not found");
    let (type_id, variant_id) = match value {
        TypedExpr::Call { callee, .. } => match callee.as_ref() {
            TypedExpr::Path {
                type_id,
                variant_id,
                ..
            } => (*type_id, *variant_id),
            other => panic!("callee is not a Path: {other:?}"),
        },
        other => panic!("`p`'s value is not a Call: {other:?}"),
    };
    assert!(
        type_id.is_some(),
        "Point::origin()'s callee Path should carry Point's SymbolId"
    );
    assert!(
        variant_id.is_none(),
        "a static method is not a variant constructor"
    );
}

#[test]
fn record_projection_base_carries_its_binding_id() {
    // metel-core#1054 (record-projection identity slice): `self.{ fd }`'s
    // base is re-typed as a synthesised `Ident` node; it should resolve
    // to `self`'s own `LocalId`, the same as any other reference to
    // `self` in the method body, not `None`.
    use crate::data::typed_ast::{FunBody, TypedExpr};
    use crate::identity::BindingId;

    let root = "record_projection.mtl";
    let source = "struct Handle {\n\
                       \tfd: i64,\n\
                       }\n\
                       extend Handle {\n\
                       \tfun narrow(self) -> i64 {\n\
                       \t\tlet r := self.{ fd };\n\
                       \t\tr.fd\n\
                       \t}\n\
                       }\n\
                       fun main() -> i64 {\n\
                       \tHandle { fd = 5 }.narrow()\n\
                       }\n";
    let typed_report = typecheck_source(root, source).report;

    let narrow_body = typed_report
        .graph
        .modules
        .iter()
        .find_map(|m| {
            m.decls.iter().find_map(|d| match d {
                TypedDecl::Impl(ib) => ib.methods.iter().find_map(|f| {
                    if f.name == "narrow" {
                        match &f.body {
                            FunBody::Typed(block) => Some(block),
                            _ => None,
                        }
                    } else {
                        None
                    }
                }),
                _ => None,
            })
        })
        .expect("typed `narrow` body");

    let value = narrow_body
        .stmts
        .iter()
        .find_map(|d| match d {
            TypedDecl::Let(l) if l.name == "r" => Some(&l.value),
            _ => None,
        })
        .expect("`let r` not found");
    let object = match value {
        TypedExpr::RecordLiteral { fields, .. } => match fields.as_slice() {
            [(_, TypedExpr::FieldAccess { object, .. })] => object.as_ref(),
            other => panic!("expected one projected field, got {other:?}"),
        },
        other => panic!("`r`'s value is not a RecordLiteral: {other:?}"),
    };
    match object {
        TypedExpr::Ident(name, binding, ..) => {
            assert_eq!(name, "self");
            assert!(
                matches!(binding, Some(BindingId::Local(_))),
                "self.{{ fd }}'s base should carry self's LocalId, not {binding:?}"
            );
        }
        other => panic!("projection base is not an Ident: {other:?}"),
    }
}

#[test]
fn toplevel_bare_statement_reference_carries_a_symbol_id() {
    // metel-core#1116: a bare top-level statement (`w.get();`, outside any
    // `fun`) referencing an earlier top-level `let` -- the identity
    // walker's own module-level dispatch never visits `Decl::Stmt` at all
    // (it only descends into `Fun`/`Let`/`Mut`/`Impl`/`Aspect` bodies), so
    // this reference has no `binding_spans` entry of its own. Construction
    // falls back to the reference-resolver's separate `Def` table (a
    // whole-module walk that does cover bare statements) -- verified here
    // by checking the receiver Ident still carries a real SymbolId.
    use crate::data::typed_ast::{TypedExpr, TypedStmt};

    let root = "toplevel_stmt.mtl";
    let source = "struct Wrapper {\n\
                       \tn: i64,\n\
                       }\n\
                       extend Wrapper {\n\
                       \tfun get(self) -> i64 {\n\
                       \t\tself.n\n\
                       \t}\n\
                       }\n\
                       let w := Wrapper { n = 5 };\n\
                       w.get();\n";
    let typed_report = typecheck_source(root, source).report;

    let stmt = typed_report
        .graph
        .modules
        .iter()
        .find_map(|m| {
            m.decls.iter().find_map(|d| match d {
                TypedDecl::Stmt(s) => Some(s.as_ref()),
                _ => None,
            })
        })
        .expect("the top-level `w.get();` statement");
    let binding = match stmt {
        TypedStmt::Expr(TypedExpr::MethodCall { receiver, .. }) => match receiver.as_ref() {
            TypedExpr::Ident(_, binding, ..) => *binding,
            other => panic!("receiver is not an Ident: {other:?}"),
        },
        other => panic!("not a MethodCall statement: {other:?}"),
    };
    assert!(
        binding.is_some(),
        "w's reference in the top-level statement should carry a real BindingId, not None"
    );
}
