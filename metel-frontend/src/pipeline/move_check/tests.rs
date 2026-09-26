use super::*;
use crate::pipeline::coherence;
use crate::pipeline::name_resolution::name_resolver;
use crate::pipeline::parsing::module_loader;
use crate::pipeline::path_normalization;
use crate::pipeline::type_checking;
use std::io::Write;
use std::sync::atomic::{AtomicU64, Ordering};

fn move_violations_for_source(source: &str) -> Vec<MoveViolation> {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let path =
        std::env::temp_dir().join(format!("metel_move_check_{}_{n}.mtl", std::process::id()));
    {
        let mut file = std::fs::File::create(&path).expect("create temp fixture");
        file.write_all(source.as_bytes())
            .expect("write temp fixture");
    }
    let violations = (|| {
        let graph = module_loader::load_root(&path).expect("load temp fixture");
        let names = name_resolver::resolve(&graph).expect("resolve temp fixture");
        let normalized =
            path_normalization::normalize(graph, names).expect("normalize temp fixture");
        coherence::check(&normalized).expect("coherence temp fixture");
        let typed = type_checking::check_graph(&normalized, &type_checking::CorePrelude::default())
            .expect("typecheck temp fixture");
        collect_graph_violations(&typed)
            .violations
            .into_iter()
            .filter(|violation| violation.use_span.filename == path.to_string_lossy())
            .collect()
    })();
    let _ = std::fs::remove_file(&path);
    violations
}

/// RFC-0137 slice 2: some shapes that `move_check` used to be the only thing
/// to reject are now caught earlier, by move-triggered row narrowing, as a
/// plain typecheck error. Assert the frontend rejects `source` with a message
/// containing `needle`.
fn assert_typecheck_error_contains(source: &str, needle: &str) {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let path =
        std::env::temp_dir().join(format!("metel_narrow_err_{}_{n}.mtl", std::process::id()));
    std::fs::write(&path, source).expect("write temp fixture");
    let result = (|| {
        let graph = module_loader::load_root(&path)?;
        let names = name_resolver::resolve(&graph)?;
        let normalized = path_normalization::normalize(graph, names)?;
        coherence::check(&normalized)?;
        type_checking::check_graph(&normalized, &type_checking::CorePrelude::default()).map(|_| ())
    })();
    let _ = std::fs::remove_file(&path);
    let err = result.expect_err("expected a typecheck error, got a clean typecheck");
    let msg = err.to_string();
    assert!(
        msg.contains(needle),
        "expected typecheck error to contain {needle:?}, got: {msg}"
    );
}

fn assert_has_violation(source: &str, binding: &str) -> Vec<MoveViolation> {
    let violations = move_violations_for_source(source);
    assert!(
        violations
            .iter()
            .any(|violation| violation.binding == binding),
        "expected a move violation for `{binding}`, got {violations:#?}"
    );
    violations
}

fn assert_no_violations(source: &str) {
    let violations = move_violations_for_source(source);
    assert!(
        violations.is_empty(),
        "unexpected violations: {violations:#?}"
    );
}

fn move_warnings_for_source(source: &str) -> Vec<String> {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "metel_move_check_warning_{}_{n}.mtl",
        std::process::id()
    ));
    {
        let mut file = std::fs::File::create(&path).expect("create temp fixture");
        file.write_all(source.as_bytes())
            .expect("write temp fixture");
    }
    let warnings = (|| {
        let graph = module_loader::load_root(&path).expect("load temp fixture");
        let names = name_resolver::resolve(&graph).expect("resolve temp fixture");
        let normalized =
            path_normalization::normalize(graph, names).expect("normalize temp fixture");
        coherence::check(&normalized).expect("coherence temp fixture");
        let typed = type_checking::check_graph(&normalized, &type_checking::CorePrelude::default())
            .expect("typecheck temp fixture");
        check_graph(&typed).expect("move-check temp fixture")
    })();
    let _ = std::fs::remove_file(&path);
    warnings
}

// arch-verifies: ["arch.move-check.requirement-1"]
#[test]
fn unchecked_generic_body_is_reported_to_compiler_callers() {
    let warnings = move_warnings_for_source(
        r#"
aspect FirstMarker {
fun inspect(&self);
}

aspect SecondMarker {
fun inspect(&self);
}

aspect Container {
type Item: FirstMarker + SecondMarker;
fun get(self) -> Item;
}

fun inspect<T: Container>(value: T) {
let item := value.get();
item.inspect();
}

fun main() { }
"#,
    );
    assert!(
        warnings.iter().any(|warning| {
            warning.contains("ambiguous aspect method `inspect`")
                && warning.contains("FirstMarker, SecondMarker")
        }),
        "expected the reconstruction failure reason, got {warnings:#?}"
    );
}

#[test]
fn bounded_generic_mut_receiver_and_argument_are_reborrowed() {
    let warnings = move_warnings_for_source(
        r#"
aspect Blend {
fun blend(&var self, other: &var Self);
}

fun blend_twice<T: Blend>(value: T, other: T) {
var value := value;
var other := other;
value.blend(&var other);
value.blend(&var other);
}

fun main() { }
"#,
    );
    assert!(
        warnings.is_empty(),
        "bounded generic method body was not fully checked: {warnings:#?}"
    );
}

#[test]
fn bounded_generic_method_generic_copy_bound_is_checked() {
    let warnings = move_warnings_for_source(
        r#"
aspect GenericSink {
fun take<U: Copy>(&self, other: U);
}

fun take_copy<T: GenericSink, U: Copy>(value: T, other: U) -> U {
value.take(other);
other
}

fun main() { }
"#,
    );
    assert!(
        warnings.is_empty(),
        "bounded method-generic body was not fully checked: {warnings:#?}"
    );
}

#[test]
fn unmet_method_generic_bound_is_reported_unchecked() {
    let warnings = move_warnings_for_source(
        r#"
aspect GenericSink {
fun take<U: Copy>(&self, other: U);
}

fun take_unbounded<T: GenericSink, U>(value: T, other: U) {
value.take(other);
}

fun main() { }
"#,
    );
    assert!(
        warnings
            .iter()
            .any(|warning| warning.contains("does not implement `Copy`")),
        "expected the reconstruction failure reason, got {warnings:#?}"
    );
}

// arch-verifies: ["arch.move-check.requirement-1"]
#[test]
fn assignment_move_then_use_is_reported() {
    assert_has_violation(
        r#"
fun main() {
let a := "hello";
let b := a;
let c := a;
}
"#,
        "a",
    );
}

#[test]
fn argument_move_then_use_is_reported() {
    assert_has_violation(
        r#"
fun take(s: String) { }

fun main() {
let s := "hello";
take(s);
let again := s;
}
"#,
        "s",
    );
}

#[test]
fn return_move_then_use_is_reported() {
    assert_has_violation(
        r#"
fun forward(s: String) -> String {
return s;
}

fun main() {
let s := "hello";
let kept := forward(s);
let again := s;
}
"#,
        "s",
    );
}

#[test]
fn copy_type_can_be_used_twice() {
    assert_no_violations(
        r#"
fun main() {
let n := 41;
let a := n;
let b := n;
}
"#,
    );
    assert_no_violations(
        r#"
fun main() {
let n := 5;
let f := || -> i64 { return n; };
assert(n == 5);
}
"#,
    );
}

#[test]
fn using_moved_field_again_is_a_typecheck_error() {
    // RFC-0137 slice 2 (metel-core#858): the first `pair.left` narrows `pair`
    // to `Pair.{ right }`, so the second projection of `left` is rejected at
    // typecheck, before `--move-check` ever runs.
    assert_typecheck_error_contains(
        r#"
struct Pair {
left: String,
right: i64,
}

fun main() {
let pair := Pair { left = "a", right = 1 };
let moved: String := pair.left;
let again: String := pair.left;
}
"#,
        "left",
    );
}

#[test]
fn sibling_field_stays_accessible_after_partial_move() {
    assert_no_violations(
        r#"
struct Pair {
left: String,
right: i64,
}

fun main() {
let pair := Pair { left = "a", right = 1 };
let moved: String := pair.left;
let still_live: i64 := pair.right;
}
"#,
    );
}

// arch-verifies: ["arch.move-check.requirement-1"]
#[test]
fn whole_value_use_after_partial_move_is_a_typecheck_error() {
    // RFC-0137 slice 2 (metel-core#858): `pair` narrows to `Pair.{ right }`
    // after `pair.left` moves, so passing it where the whole `Pair` is
    // required is a plain typecheck error, not only a `--move-check` finding.
    assert_typecheck_error_contains(
        r#"
struct Pair {
left: String,
right: i64,
}

fun take(pair: Pair) -> i64 {
pair.right
}

fun main() {
let pair := Pair { left = "a", right = 1 };
let moved: String := pair.left;
let value: i64 := take(pair);
}
"#,
        "partially-moved `Pair`",
    );
}

// arch-verifies: ["arch.move-check.requirement-1"]
#[test]
fn partial_move_of_drop_type_is_reported() {
    assert_has_violation(
        r#"
struct Handle {
name: String,
fd: i64,
}

extend Handle: Drop {
fun drop(&var self) { }
}

fun main() {
let handle := Handle { name = "x", fd = 1 };
let name := handle.name;
}
"#,
        "handle",
    );
}

#[test]
fn partial_move_of_drop_type_in_match_binding_is_reported() {
    assert_has_violation(
        r#"
struct Handle {
name: String,
fd: i64,
}

extend Handle: Drop {
fun drop(&var self) { }
}

fun main() {
let handle := Handle { name = "x", fd = 1 };
let n := match (handle.name) {
    name => name.len(),
};
}
"#,
        "handle",
    );
}

/// A record pattern moves at field granularity, like a struct field access:
/// the moved field is gone, and the record may no longer be used as a whole.
///
/// The `Drop` variant of this test is deliberately absent rather than
/// overlooked. An anonymous record can never implement `Drop` (RFC-0116 §3,
/// enforced in `coherence`: "anonymous records cannot implement `Drop`"), so
/// a record pattern partially moving a `Drop` value is unrepresentable. An
/// earlier revision tried to write it by destructuring a *nominal* struct
/// with a record pattern, which the typechecker rejects outright — the test
/// was failing on its own fixture, not on the checker.
#[test]
fn record_pattern_moves_at_field_granularity() {
    assert_has_violation(
        r#"
fun take(r: { n: i64, name: String }) -> i64 {
return r.n;
}

fun main() {
let r := { name = "x", n = 1 };
let moved := match (r) {
    { name, n } => name,
};
let again := take(r);
}
"#,
        "r",
    );
}

#[test]
fn tuple_pattern_partial_move_of_drop_prefix_is_reported() {
    assert_has_violation(
        r#"
struct Wrapper {
pair: (String, i64),
}

extend Wrapper: Drop {
fun drop(&var self) { }
}

fun main() {
let wrapper := Wrapper { pair = ("x", 1) };
let n := match (wrapper.pair) {
    (name, _) => name.len(),
};
}
"#,
        "wrapper",
    );
}

#[test]
fn enum_payload_pattern_partial_move_of_drop_prefix_is_reported() {
    assert_has_violation(
        r#"
enum MaybeText {
Empty,
Full { text: String },
}

struct Wrapper {
payload: MaybeText,
}

extend Wrapper: Drop {
fun drop(&var self) { }
}

fun main() {
let wrapper := Wrapper {
    payload = MaybeText::Full { text = "x" },
};
let n := match (wrapper.payload) {
    MaybeText::Full { text } => text.len(),
    MaybeText::Empty => 0,
};
}
"#,
        "wrapper",
    );
}

#[test]
fn nested_direct_partial_move_of_drop_prefix_is_reported() {
    assert_has_violation(
        r#"
struct Wrapper {
pair: (String, i64),
}

extend Wrapper: Drop {
fun drop(&var self) { }
}

fun main() {
let wrapper := Wrapper { pair = ("x", 1) };
let name := wrapper.pair.0;
}
"#,
        "wrapper",
    );
}

#[test]
fn tuple_element_partial_move_then_reuse_is_reported() {
    assert_has_violation(
        r#"
fun main() {
let pair := ("x", 1);
let left := pair.0;
let again := pair.0;
}
"#,
        "pair",
    );
}

#[test]
fn enum_payload_move_consumes_whole_value() {
    assert_has_violation(
        r#"
enum MaybeText {
Empty,
Full { text: String },
}

fun main() {
let value := MaybeText::Full { text = "x" };
let n := match (value) {
    MaybeText::Full { text } => text.len(),
    MaybeText::Empty => 0,
};
let again := value;
}
"#,
        "value",
    );
}

// arch-verifies: ["arch.move-check.requirement-1"]
#[test]
fn array_element_move_is_reported() {
    assert_has_violation(
        r#"
fun main() {
let xs := ["x"];
let first := xs[0];
}
"#,
        "xs",
    );
}

#[test]
fn array_element_move_in_match_binding_is_reported() {
    assert_has_violation(
        r#"
fun main() {
let xs := ["x"];
let n := match (xs[0]) {
    s => s.len(),
};
}
"#,
        "xs",
    );
}

#[test]
fn array_pattern_binding_array_element_is_reported() {
    assert_has_violation(
        r#"
fun main() {
let xs: [String; 1] := ["x"];
let n := match (xs) {
    [s] => s.len(),
};
}
"#,
        "xs",
    );
}

#[test]
fn closure_capture_then_use_is_reported() {
    let violations = assert_has_violation(
        r#"
fun main() {
let s := "hello";
let f := [s] once || -> String { s };
let again := s;
}
"#,
        "s",
    );
    assert_eq!(violations[0].moved_type, "String");
}

#[test]
fn move_in_one_if_arm_persists_after_join() {
    assert_has_violation(
        r#"
fun main() {
let s := "hello";
if (true) {
    let moved := s;
} else {
    let keep := 0;
}
let again := s;
}
"#,
        "s",
    );
}

#[test]
fn move_in_loop_body_persists_after_loop() {
    assert_has_violation(
        r#"
fun main() {
let s := "hello";
loop {
    let moved := s;
    break;
}
let again := s;
}
"#,
        "s",
    );
}

#[test]
fn mut_ref_argument_reborrows_cleanly() {
    assert_no_violations(
        r#"
struct Counter { value: i64 }

fun bump(r: &var Counter) { }

fun main() {
var c := Counter { value = 0 };
let r := &var c;
bump(r);
bump(r);
}
"#,
    );
}

// arch-verifies: ["arch.move-check.requirement-1"]
#[test]
fn plain_binding_of_mut_ref_then_use_is_reported() {
    assert_has_violation(
        r#"
struct Counter { value: i64 }

fun bump(r: &var Counter) { }

fun main() {
var c := Counter { value = 0 };
let r := &var c;
let q := r;
bump(r);
}
"#,
        "r",
    );
}

#[test]
fn move_site_is_not_reported_as_its_own_use() {
    let violations = move_violations_for_source(
        r#"
struct Pair {
left: String,
right: i64,
}

fun main() {
let pair := Pair { left = "a", right = 1 };
let moved := pair.left;
}
"#,
    );
    assert!(
        violations.is_empty(),
        "the move site must not accuse itself: {violations:#?}"
    );
}

#[test]
fn moving_projection_does_not_report_base_as_only_use() {
    let violations = move_violations_for_source(
        r#"
struct Pair {
left: String,
right: i64,
}

fun main() {
let pair := Pair { left = "a", right = 1 };
let moved := pair.left;
let sibling := pair.right;
}
"#,
    );
    assert!(
        violations.is_empty(),
        "moving `pair.left` must not report `pair` as used-after-move: {violations:#?}"
    );
}

/// A tuple literal takes ownership of its elements. Regression for a false
/// negative where they were only *observed*: the element stayed usable
/// afterwards, and every rule `consume_place` enforces was skipped.
#[test]
fn tuple_literal_consumes_its_elements() {
    assert_has_violation(
        r#"
struct Owned {
s: String,
}

fun main() {
let a := Owned { s = "x" };
let t := (a, 1);
let n := a.s.len();
}
"#,
        "a",
    );
}

#[test]
fn tuple_literal_cannot_partially_move_a_drop_type() {
    assert_has_violation(
        r#"
struct Handle {
name: String,
fd: i64,
}

extend Handle: Drop {
fun drop(&var self) { }
}

fun main() {
let h := Handle { name = "x", fd = 1 };
let t := (h.name, 1);
}
"#,
        "h",
    );
}

#[test]
fn array_literal_cannot_move_an_array_element() {
    assert_has_violation(
        r#"
fun main() {
let xs := ["a"];
let ys := [xs[0]];
}
"#,
        "xs",
    );
}

// arch-verifies: ["arch.move-check.requirement-1"]
#[test]
fn borrowed_array_for_in_cannot_move_a_noncopy_element() {
    assert_has_violation(
        r#"
fun first<T>(items: T[]) -> T {
for (item in items) {
    return item;
}
panic("empty")
}

fun main() { }
"#,
        "item",
    );
}

#[test]
fn borrowed_array_for_in_allows_copy_elements() {
    assert_no_violations(
        r#"
fun first<T: Copy>(items: T[]) -> T {
for (item in items) {
    return item;
}
panic("empty")
}

fun main() {
let values: i64[] := [1, 2, 3];
assert(first(values) == 1);
}
"#,
    );
}

#[test]
fn function_values_are_copy() {
    assert_no_violations(
        r#"
fun increment(value: i64) -> i64 { value + 1 }

fun apply(f: |i64| -> i64) -> i64 { f(1) }

fun main() {
let f := increment;
assert(apply(f) == 2);
assert(apply(f) == 2);
}
"#,
    );
}

// --- #337: type conversion must preserve arity or fail outright ---------------------
//
// These exercise the conversion helpers directly. The misalignment they guard against
// needs an unresolved `InferType::Var` to survive into a parameter list, which the
// reconstruction path does not currently produce from source -- it abandons a body
// wholesale instead. So there is no `.mtl` fixture that would fail without the fix;
// asserting on the helpers is what actually pins the invariant.

use crate::pipeline::type_checking::typeinference::{InferType, TypeVar};

fn var() -> InferType {
    InferType::Var(TypeVar(0))
}

fn concrete() -> InferType {
    InferType::Concrete(Type::I64)
}

#[test]
fn tuple_with_an_unresolved_element_converts_to_none_not_a_shorter_tuple() {
    let ty = InferType::Tuple(vec![var(), concrete()]);
    assert_eq!(infer_to_type(&ty), None);
}

#[test]
fn record_with_an_unresolved_field_converts_to_none_not_a_smaller_record() {
    let ty = InferType::Record(vec![
        ("a".to_string(), var()),
        ("b".to_string(), concrete()),
    ]);
    assert_eq!(infer_to_type(&ty), None);
}

#[test]
fn fun_with_an_unresolved_param_converts_to_none_not_a_shorter_signature() {
    let ty = InferType::fun(vec![var(), concrete()], concrete());
    assert_eq!(infer_to_type(&ty), None);
}

#[test]
fn named_with_an_unresolved_argument_converts_to_none_not_fewer_arguments() {
    let ty = InferType::Named(
        "Holder".to_string(),
        vec![var(), concrete()],
        crate::data::types::NominalId::NONE,
    );
    assert_eq!(infer_to_type(&ty), None);
}

#[test]
fn fully_resolved_compounds_still_convert_and_keep_their_arity() {
    let tuple = InferType::Tuple(vec![concrete(), concrete(), concrete()]);
    assert_eq!(
        infer_to_type(&tuple),
        Some(Type::Tuple(vec![Type::I64, Type::I64, Type::I64]))
    );

    let fun = InferType::fun(vec![concrete(), concrete()], concrete());
    assert_eq!(
        infer_to_type(&fun),
        Some(Type::Fun(
            vec![Type::I64, Type::I64],
            Box::new(Type::I64),
            crate::data::types::CallMultiplicity::Many,
            crate::data::types::UseMultiplicity::Copy,
            crate::data::types::CallMutation::Reading,
        ))
    );
}

#[test]
fn method_arg_types_are_none_when_a_parameter_is_unresolved() {
    // Receiver plus three parameters, the middle one unresolved. A filtered list would
    // be `[i64, i64]`, and `observe_call_args` -- which indexes positionally -- would
    // then judge the third argument against the second parameter's type. That decides
    // borrow-vs-move, so the shift silently turns a reborrow into a move or back.
    let fun_ty = InferType::fun(vec![concrete(), concrete(), var(), concrete()], concrete());
    assert_eq!(infer_method_arg_types(&fun_ty), None);
}

#[test]
fn method_arg_types_skip_the_receiver_and_keep_the_rest_in_order() {
    let fun_ty = InferType::fun(
        vec![
            InferType::Concrete(Type::Boolean),
            InferType::Concrete(Type::I64),
            InferType::Concrete(Type::MutReference(Box::new(Type::I64))),
        ],
        concrete(),
    );
    assert_eq!(
        infer_method_arg_types(&fun_ty),
        Some(vec![Type::I64, Type::MutReference(Box::new(Type::I64))])
    );
}

// ── Loop-carried moves (#291) ────────────────────────────────────────────
//
// A loop body is walked more than once while its entry state grows. These
// pin the two things that are easy to get wrong about that: what reaches the
// next iteration, and that walking twice does not report twice.

#[test]
fn a_loop_carried_move_is_reported_once_not_once_per_pass() {
    let violations = assert_has_violation(
        r#"
fun main() {
let s := "hello";
var i := 0;
loop {
    i += 1;
    let moved := s;
    if (i == 2) { break; }
}
}
"#,
        "s",
    );
    assert_eq!(
        violations.len(),
        1,
        "the body is walked once per widening pass; only the last may report"
    );
    assert!(violations[0].moved_in_previous_iteration);
}

#[test]
fn nested_loops_report_a_carried_move_once_each_not_once_per_outer_pass() {
    let violations = assert_has_violation(
        r#"
fun main() {
let s := "hello";
var i := 0;
while (i < 3) {
    i += 1;
    var j := 0;
    while (j < 2) {
        j += 1;
        let moved := s;
    }
}
}
"#,
        "s",
    );
    assert_eq!(violations.len(), 1, "got {violations:#?}");
}

#[test]
fn a_move_reached_only_by_breaking_out_does_not_reach_the_next_iteration() {
    assert_no_violations(
        r#"
fun main() {
let s := "hello";
var i := 0;
loop {
    i += 1;
    if (i == 2) {
        let moved := s;
        break;
    }
}
}
"#,
    );
}

#[test]
fn a_move_reached_only_by_returning_does_not_reach_the_next_iteration() {
    assert_no_violations(
        r#"
fun main() {
let s := "hello";
var i := 0;
loop {
    i += 1;
    if (i == 2) {
        let moved := s;
        return;
    }
}
}
"#,
    );
}

#[test]
fn a_move_before_continue_reaches_the_next_iteration() {
    let violations = assert_has_violation(
        r#"
fun main() {
let s := "hello";
var i := 0;
loop {
    i += 1;
    let moved := s;
    if (i < 3) { continue; }
    break;
}
}
"#,
        "s",
    );
    assert!(violations[0].moved_in_previous_iteration);
}

#[test]
fn a_move_that_breaks_out_is_still_visible_after_the_loop() {
    assert_has_violation(
        r#"
fun main() {
let s := "hello";
var i := 0;
loop {
    i += 1;
    if (i == 2) {
        let moved := s;
        break;
    }
}
let again := s;
}
"#,
        "s",
    );
}

#[test]
fn a_binding_declared_inside_the_body_is_fresh_each_iteration() {
    assert_no_violations(
        r#"
fun main() {
var i := 0;
while (i < 3) {
    i += 1;
    let local := "fresh";
    let moved := local;
}
}
"#,
    );
}

#[test]
fn a_move_on_a_returning_branch_does_not_reach_the_code_after_the_if() {
    // The `return` leaves the function, so the move never happened on the
    // path that reaches `again`.
    assert_no_violations(
        r#"
fun main() {
let s := "hello";
if (true) {
    let moved := s;
    return;
}
let again := s;
}
"#,
    );
}

#[test]
fn a_move_on_a_branch_that_falls_through_still_reaches_the_code_after_the_if() {
    assert_has_violation(
        r#"
fun main() {
let s := "hello";
if (true) {
    let moved := s;
}
let again := s;
}
"#,
        "s",
    );
}

// ── Writing to a moved place reinitializes it ────────────────────────────
//
// A write does not read its target. These matter most inside a loop, where
// move-then-replace is the idiomatic body, but the rule is not loop-specific.

#[test]
fn reassigning_a_moved_binding_makes_it_valid_again() {
    assert_no_violations(
        r#"
fun main() {
var s := "hello";
let moved := s;
s := "again";
let ok := s;
}
"#,
    );
}

#[test]
fn reassigning_a_moved_binding_inside_a_loop_is_not_loop_carried() {
    assert_no_violations(
        r#"
fun main() {
var s := "hello";
var i := 0;
loop {
    i += 1;
    let moved := s;
    s := "again";
    if (i == 3) { break; }
}
}
"#,
    );
}

#[test]
fn reassigning_a_moved_field_makes_the_whole_value_usable_again() {
    assert_no_violations(
        r#"
struct Pair { left: String, right: String }

fun main() {
var p := Pair { left = "a", right = "b" };
let taken := p.left;
p.left := "c";
let whole := p;
}
"#,
    );
}

#[test]
fn assigning_a_field_does_not_revive_a_wholly_moved_value() {
    // The write needs a base it can reach, and `p` is gone.
    assert_has_violation(
        r#"
struct Pair { left: String, right: String }

fun main() {
var p := Pair { left = "a", right = "b" };
let whole := p;
p.left := "c";
}
"#,
        "p",
    );
}

#[test]
fn assigning_one_field_leaves_a_sibling_field_moved() {
    // RFC-0137 (metel-core#858/#950): reassigning `left` does not clear the
    // `right` move, so `p` stays narrowed to `Pair.{ left }`. Binding it at
    // its narrowed type (`let whole := p;`) is fine; using it where the whole
    // `Pair` is required is the error — caught at type-check time now.
    assert_typecheck_error_contains(
        r#"
struct Pair { left: String, right: String }

fun take_whole(p: Pair) -> i64 { 0 }

fun main() {
var p := Pair { left = "a", right = "b" };
let taken := p.right;
p.left := "c";
let n := take_whole(p);
}
"#,
        "partially-moved `Pair`",
    );
}

#[test]
fn a_loop_with_no_reachable_break_diverges() {
    // The inner `loop` always returns, so the outer loop's back edge is
    // never taken and its body's move happens at most once.
    assert_no_violations(
        r#"
fun main() {
let s := "hello";
var i := 0;
while (i < 3) {
    i += 1;
    let moved := s;
    loop { return; }
}
}
"#,
    );
}

#[test]
fn an_inner_loop_that_can_break_leaves_the_outer_back_edge_live() {
    assert_has_violation(
        r#"
fun main() {
let s := "hello";
var i := 0;
while (i < 3) {
    i += 1;
    let moved := s;
    loop { break; }
}
}
"#,
        "s",
    );
}

// ── Shadowing (#343) ─────────────────────────────────────────────────────
//
// Binding a name clears its moved state, which is right for the new binding
// and must not destroy the one it shadows. The delicate part is that a
// `break` or `continue` records its state *before* the shadow's scope is
// popped, so the recorded state has to be unwound first.

#[test]
fn a_shadow_does_not_launder_a_loop_carried_move() {
    assert_has_violation(
        r#"
fun main() {
let s := "original";
var i := 0;
loop {
    i += 1;
    let moved := s;
    let s := "replacement";
    if (i == 2) { break; }
}
}
"#,
        "s",
    );
}

#[test]
fn a_shadow_does_not_launder_a_move_carried_out_through_break() {
    assert_has_violation(
        r#"
fun main() {
let s := "original";
loop {
    let moved := s;
    let s := "replacement";
    break;
}
let again := s;
}
"#,
        "s",
    );
}

#[test]
fn a_move_of_a_shadow_does_not_escape_its_scope_through_break() {
    // The inverse error: unwinding must not carry the *shadow's* move out
    // and pin it on the outer binding, which was never moved.
    assert_no_violations(
        r#"
fun main() {
let s := "original";
var i := 0;
loop {
    i += 1;
    let s := "shadow";
    let moved := s;
    if (i == 2) { break; }
}
let outer := s;
}
"#,
    );
}

#[test]
fn rebinding_the_same_name_twice_in_one_scope_restores_the_outermost() {
    // `pop_scope` unwinds in reverse; forwards would leave the second
    // shadow's empty state instead of what the scope was entered with.
    assert_has_violation(
        r#"
fun main() {
let s := "original";
var i := 0;
loop {
    i += 1;
    let moved := s;
    let s := "first";
    let s := "second";
    if (i == 2) { break; }
}
}
"#,
        "s",
    );
}

#[test]
fn a_repeated_move_through_a_dereference_is_a_violation() {
    let violations = assert_has_violation(
        r#"
fun eat(s: String) -> i64 { 1 }

fun main() {
let s := "hello";
let p := &s;
let first := eat(*p);
let second := eat(*p);
}
"#,
        "p",
    );
    assert_eq!(format_place(&violations[0].moved_place), "(*p)");
}

// ── By-value receivers through a reference (#348) ───────────────────────
//
// `&T` and `&var T` are both `Copy` at the reference-place level, so
// consuming the receiver *place* records nothing — the checker has to
// recognise a by-value `self` method reached through a reference and
// reject it directly, not by tracking a move of the place that never
// happens. Rejected at the first call, not the second.

// arch-verifies: ["arch.move-check.requirement-1"]
#[test]
fn a_by_value_method_through_a_shared_reference_is_rejected_at_the_first_call() {
    let violations = assert_has_violation(
        r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun main() {
let b := B { v = "owned" };
let r := &b;
let first := r.eat();
}
"#,
        "r",
    );
    assert_eq!(violations.len(), 1);
    assert_eq!(format_place(&violations[0].moved_place), "(*r)");
}

#[test]
fn a_by_value_method_through_an_explicit_deref_is_rejected_identically() {
    // Auto-deref (`r.eat()`) and an explicit `*` (`(*r).eat()`) dispatch to
    // the same method and must be rejected the same way — checking only
    // the receiver's static type would miss this spelling, since the
    // deref has already happened by the time `self.ty()` is read.
    let violations = assert_has_violation(
        r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun main() {
let b := B { v = "owned" };
let r := &b;
let first := (*r).eat();
}
"#,
        "r",
    );
    assert_eq!(format_place(&violations[0].moved_place), "(*r)");
}

#[test]
fn a_by_value_method_through_a_mut_reference_is_rejected_at_the_first_call() {
    // `&var T` is not `Copy`, so before this fix the second call was
    // rejected as reuse of the moved *reference* — the wrong reason. The
    // first call must be rejected now, for the actual reason.
    let violations = assert_has_violation(
        r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun main() {
var b := B { v = "owned" };
let r := &var b;
let first := r.eat();
}
"#,
        "r",
    );
    assert_eq!(violations[0].kind, MoveViolationKind::MoveOutOfReference);
}

#[test]
fn a_by_value_method_through_a_generic_bound_reference_is_rejected() {
    // Concrete and generic dispatch resolve through the same
    // `consume_method_receiver`, so there is no second copy of this rule
    // that could disagree with the concrete case above.
    assert_has_violation(
        r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun twice<T: Consume>(x: &T) -> String {
let a := x.eat();
return x.eat();
}

fun main() {
let b := B { v = "owned" };
let result := twice(&b);
}
"#,
        "x",
    );
}

#[test]
fn a_by_value_method_through_a_non_ident_receiver_is_rejected() {
    // The receiver is `pair.0`, not an identifier — the same shape #347
    // found unguarded for `&var self`. The check is keyed on the
    // receiver's type and place, not on `Expr::Ident`.
    let violations = assert_has_violation(
        r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun consume_sneak<T: Consume>(pair: (&T, i64)) -> String {
return pair.0.eat();
}

fun main() {
let b := B { v = "owned" };
let result := consume_sneak((&b, 1));
}
"#,
        "pair",
    );
    assert_eq!(format_place(&violations[0].moved_place), "(*pair.0)");
}

#[test]
fn an_owned_by_value_receiver_is_still_an_ordinary_move() {
    // The rule is about a reference in the way, not about by-value
    // receivers in general.
    assert_has_violation(
        r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun main() {
let b := B { v = "owned" };
let out := b.eat();
let again := b.v;
}
"#,
        "b",
    );
}

#[test]
fn ref_and_mut_ref_methods_through_a_reference_are_unaffected() {
    assert_no_violations(
        r#"
aspect Show { fun show(&self) -> String; }
aspect Bump { fun bump(&var self); }
struct B { v: String }
extend B: Show { fun show(&self) -> String { return self.v.clone(); } }
struct C { v: i64 }
extend C: Bump { fun bump(&var self) { self.v := self.v + 1; } }

fun main() {
let b := B { v = "x" };
let r := &b;
let a := r.show();
let c := r.show();

var cc := C { v = 0 };
let rc := &var cc;
rc.bump();
rc.bump();
}
"#,
    );
}

#[test]
fn a_by_value_method_through_a_reference_is_allowed_when_the_pointee_is_copy() {
    // `illegal_move_kind` (the pre-existing "outright ban" mechanism this
    // check reuses via `report_illegal_move`) already gates every one of
    // its bans on `is_copy` first — a Copy value can always be read back
    // out. `receiver_place_is_behind_a_reference` must not skip that same
    // gate, or a Copy struct's by-value method becomes uncallable through
    // a reference at all, which RFC-0067a SS3a explicitly allows ("only
    // copied, and only when the referent's type actually permits
    // copying"). Called twice through the same reference to confirm
    // nothing is consumed either.
    assert_no_violations(
        r#"
struct Pair { a: i64, b: i64 }
extend Pair: Copy;
extend Pair { fun sum(self) -> i64 { self.a + self.b } }

fun main() {
let p := Pair { a = 1, b = 2 };
let r := &p;
let first := r.sum();
let second := r.sum();
}
"#,
    );
}

#[test]
fn a_by_value_method_on_a_non_place_reference_receiver_is_rejected() {
    // A call result, `if`, `match`, or cast has no nameable `Place` at
    // all, so `receiver_place_is_behind_a_reference`'s second signal
    // (a `Deref` projection) can never fire for it — only the first
    // signal (the receiver's own static type) can. An earlier version of
    // `report_move_out_of_reference` returned early when `place_from_expr`
    // gave `None`, silently accepting this; found by adversarial review.
    let violations = assert_has_violation(
        r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun get_ref(x: &B) -> &B { return x; }

fun main() {
let b := B { v = "owned" };
let out := get_ref(&b).eat();
}
"#,
        "<temporary>",
    );
    assert_eq!(violations.len(), 1);
}

#[test]
fn a_by_value_method_through_a_double_reference_names_every_layer() {
    // `deref_layers` must count every implicit layer from the receiver's
    // own type, not just append one `Deref` unconditionally — otherwise
    // `rr: &&B` reports `(*rr)` (still a reference, not the `B` actually
    // moved) instead of `(*(*rr))`. Found by adversarial review.
    let violations = assert_has_violation(
        r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }

fun main() {
let b := B { v = "owned" };
let r := &b;
let rr := &r;
let out := rr.eat();
}
"#,
        "rr",
    );
    assert_eq!(violations.len(), 1);
    assert_eq!(format_place(&violations[0].moved_place), "(*(*rr))");
}

// ── Moving a value out of a reference at non-receiver positions (#648) ──
//
// #602 (above) only ever intercepted a by-value method *receiver*. Every
// other position a value can be moved from — a `let` initializer, a
// by-value argument, a plain field read — funnels through the ordinary
// `consume_place` -> `illegal_move_kind` path instead, which never
// consulted whether a projection stepped through a reference. These
// exercise that path directly.

#[test]
fn move_out_of_self_field_in_a_ref_self_method_is_rejected() {
    // The motivating repro for #648: `self` in a `&self` method is a
    // reference like any other, but nothing checked it before this fix.
    let violations = assert_has_violation(
        r#"
struct Name { value: String }
struct Item { name: Name, count: i64 }
extend Item {
fun peek(&self) -> String {
    let v := self.name.value;
    v
}
}
fun main() {
let item := Item { name = Name { value = "n" }, count = 1 };
let _ := item.peek();
}
"#,
        "self",
    );
    assert_eq!(violations.len(), 1);
    assert_eq!(violations[0].kind, MoveViolationKind::MoveOutOfReference);
    assert_eq!(format_place(&violations[0].moved_place), "self.name.value");
}

#[test]
fn move_out_of_a_field_read_through_a_plain_reference_parameter_is_rejected() {
    // Same rule, no `self` involved — an ordinary `&T` parameter.
    let violations = assert_has_violation(
        r#"
struct Name { value: String }
struct Item { name: Name, count: i64 }
fun peek(item: &Item) -> String {
let v := item.name.value;
v
}
fun main() {
let item := Item { name = Name { value = "n" }, count = 1 };
let _ := peek(&item);
}
"#,
        "item",
    );
    assert_eq!(violations.len(), 1);
    assert_eq!(format_place(&violations[0].moved_place), "item.name.value");
}

#[test]
fn general_assignment_out_of_an_explicit_deref_is_rejected() {
    // RFC-0071 SS7.1's own named example: `let x: B = *r;`.
    assert_has_violation(
        r#"
struct B { v: String }
fun main() {
let b := B { v = "x" };
let r := &b;
let x: B := *r;
}
"#,
        "r",
    );
}

#[test]
fn by_value_argument_passing_out_of_an_explicit_deref_is_rejected() {
    // RFC-0071 SS7.1's other named example: `f(*r)`.
    assert_has_violation(
        r#"
struct B { v: String }
fun takes(b: B) -> String { b.v }
fun main() {
let b := B { v = "x" };
let r := &b;
let n := takes(*r);
}
"#,
        "r",
    );
}

#[test]
fn by_value_argument_passing_a_field_read_through_a_reference_is_rejected() {
    // The field-read form of the same argument-position gap: `f(r.field)`,
    // no explicit `*` anywhere.
    assert_has_violation(
        r#"
struct Name { value: String }
struct Item { name: Name }
fun takes(v: String) -> i64 { v.len() }
fun main() {
let item := Item { name = Name { value = "x" } };
let r := &item;
let n := takes(r.name.value);
}
"#,
        "r",
    );
}

#[test]
fn copy_field_read_through_a_reference_is_still_allowed() {
    // The `Copy` gate must survive the new check exactly as it does for
    // #602's receiver case: a `Copy` value can always be read back out.
    assert_no_violations(
        r#"
struct Item { count: i64, name: String }
fun peek(item: &Item) -> i64 {
let v := item.count;
v
}
fun main() {
let item := Item { count = 5, name = "n" };
let _ := peek(&item);
}
"#,
    );
}

#[test]
fn by_value_method_through_an_interior_reference_field_is_rejected() {
    // A different manifestation of the same gap, reached through
    // `consume_method_receiver`'s own fallback: #602's
    // `receiver_place_is_behind_a_reference` only inspects the
    // *immediate* receiver's own type/place, so it misses a receiver
    // reached via auto-deref through an *interior* reference-typed field
    // (`outer.inner.payload`, where `inner: &Middle`). That fallback
    // still routes through `consume_expr_with_cause` -> `illegal_move_kind`
    // when its own check misses, so this fix closes it as a side effect —
    // this test proves it rather than leaving it as an assumption.
    assert_has_violation(
        r#"
aspect Consume { fun eat(self) -> String; }
struct B { v: String }
extend B: Consume { fun eat(self) -> String { return self.v; } }
struct Middle { payload: B }
struct Outer { inner: &Middle }
fun main() {
let b := B { v = "owned" };
let middle := Middle { payload = b };
let outer := Outer { inner = &middle };
let taken := outer.inner.payload.eat();
}
"#,
        "outer",
    );
}

#[test]
fn ref_self_method_that_only_reads_is_still_unaffected() {
    // Reading a Copy field, or calling a &self/&var self method, through
    // self must remain completely unaffected by the corrected self type.
    assert_no_violations(
        r#"
struct Item { count: i64, name: String }
extend Item {
fun show(&self) -> String {
    return "${self.count}: ${self.name}";
}
}
fun main() {
let item := Item { count = 1, name = "n" };
println(item.show());
}
"#,
    );
}
