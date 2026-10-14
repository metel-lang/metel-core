use super::*;
use crate::pipeline::coherence;
use crate::pipeline::name_resolution::name_resolver;
use crate::pipeline::parsing::module_loader;
use crate::pipeline::path_normalization;
use crate::pipeline::type_checking;
use std::io::Write;
use std::sync::atomic::{AtomicU64, Ordering};

fn move_violations_for_source(source: &str) -> Vec<MoveViolation> {
    move_report_for_source(source).violations
}

fn move_report_for_source(source: &str) -> MoveCheckReport {
    move_report_for_source_with(source, |_| {})
}

/// Drop everything the abstract path and the legacy reconstruction fallback rely
/// on, so a generic body genuinely cannot be analysed.
fn make_generic_bodies_unanalyzable(graph: &mut TypedModuleGraph) {
    for module in &mut graph.modules {
        module.scheme_env.clear();
        for decl in &mut module.decls {
            if let TypedDecl::Fun(fun) = decl {
                fun.abstract_body = None;
            }
        }
    }
}

fn move_report_for_source_with(
    source: &str,
    prepare: impl FnOnce(&mut TypedModuleGraph),
) -> MoveCheckReport {
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
        let members = crate::identity::collect_members_for_graph(&graph, &names);
        let allocation = crate::identity::allocate_for_graph(&graph, &names);
        let normalized =
            path_normalization::normalize(graph, names).expect("normalize temp fixture");
        coherence::check(&normalized).expect("coherence temp fixture");
        let mut typed = type_checking::check_graph_with_report(
            &normalized,
            &type_checking::CorePrelude::default(),
            Some(crate::identity::FrozenIdentity {
                members: &members,
                binding_spans: &allocation.binding_spans,
            }),
        )
        .expect("typecheck temp fixture")
        .graph;
        prepare(&mut typed);
        let mut report = collect_graph_violations(&typed);
        report
            .violations
            .retain(|violation| violation.use_span.filename == path.to_string_lossy());
        report
            .checked_abstract_generic_bodies
            .retain(|span| span.filename == path.to_string_lossy());
        report
    })();
    let _ = std::fs::remove_file(&path);
    violations
}

#[test]
fn abstract_ownership_retains_builtin_array_length_and_temporary_inputs() {
    let report = move_report_for_source_with(
        r#"
fun borrowed<T>(values: [T; 2]) -> i64 { values.len() + values.len() }
fun projected<T>(values: ([T; 2], i64)) -> i64 { values.0.len() + values.0.len() }
fun temporary<T>(value: T) { let length := [value].len(); value; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        3,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "value");
}

#[test]
fn abstract_ownership_checks_inherited_defaults_with_separate_impl_facts() {
    let report = move_report_for_source_with(
        r#"
fun identity<T>(value: T) -> T { value }
aspect Echo {
    fun echo<V>(self, value: V) -> V { identity(value) }
    fun duplicate<V>(self, value: V) { let first := value; let second := value; }
}
struct Box<T> { public value: T }
struct Other<T> { public value: T }
extend<T> Box<T>: Echo {}
extend<T> Other<T>: Echo {}
extend<row R> { ..R }: Echo {}
aspect Repeat<A> {
    fun repeat(self, value: A) { let first := value; let second := value; }
}
extend<T: Copy> Box<T>: Repeat<T> {}
extend<T> Other<T>: Repeat<T> {}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        9,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 4, "{report:#?}");
    assert!(
        report
            .violations
            .iter()
            .all(|violation| violation.binding == "value")
    );
}

#[test]
fn abstract_ownership_retains_equation_destructuring_shapes() {
    let report = move_report_for_source_with(
        r#"
fun strip<row R, row Rest>(value: { ..R }) -> { ..Rest }
where R = { token: String, ..Rest } {
    let { token: _, ..rest } := value;
    rest
}
fun strip_two<row R, row Mid, row Rest>(value: { ..R }) -> { ..Rest }
where R = { token: String, ..Mid }, Mid = { count: i64, ..Rest } {
    let { token: _, count: _, ..rest } := value;
    rest
}
fun alternate<row R, row A, row B>(value: { ..R }) -> { ..B }
where R = { a: i64, ..A }, R = { b: i64, ..B } {
    let { b, ..rest } := value;
    rest
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                for decl in &module.decls {
                    if let TypedDecl::Fun(fun) = decl
                        && matches!(fun.name.as_str(), "strip" | "strip_two" | "alternate")
                    {
                        assert!(
                            matches!(
                                fun.abstract_body,
                                Some(crate::data::abstract_body::AbstractBodyPreparation::Typed(
                                    _
                                ))
                            ),
                            "{}: {:?}; {:?}",
                            fun.name,
                            fun.abstract_body,
                            fun.abstract_signature
                        );
                    }
                }
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        3,
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_retains_body_only_associated_projections() {
    let report = move_report_for_source_with(
        r#"
aspect Source { type Item: Copy; fun get(self) -> Item; }
aspect OwnedSource { type Item; fun get(self) -> Item; }
fun copied<S: Source>(source: S) {
    let item := source.get(); let first := item; let second := item;
}
fun consumed<S: OwnedSource>(source: S) {
    let item := source.get(); let first := item; let second := item;
}
fun receiver<S: OwnedSource>(source: S) { source.get(); source.get(); }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        3,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 2, "{report:#?}");
}

#[test]
fn abstract_ownership_retains_structural_method_remainder_facts() {
    let report = move_report_for_source_with(
        r#"
aspect Strip { fun strip(self); }
extend<row R, row Rest> { ..R }: Strip where R = { token: String, ..Rest } {
    fun strip(self) {
        let { token: _, ..rest } := self;
        let remainder: { ..Rest } := rest;
    }
}
aspect StripCopy { fun strip_copy(self); }
extend<row R: Copy, row Rest> { ..R }: StripCopy where R = { count: i64, ..Rest } {
    fun strip_copy(self) {
        let { count: _, ..rest } := self;
        let first := rest;
    }
}
aspect StripTemporary { fun strip_temporary(self); }
extend<row R, row Rest> { ..R }: StripTemporary where R = { token: String, ..Rest } {
    fun strip_temporary(self) {
        let { token: _, ..rest } := identity(self);
    }
}
fun identity<T>(value: T) -> T { value }
fun safe<record S: !Drop + { token: String }>(value: S) {
    let { token: _, ..rest } := value;
}
fun ambiguous<S: { token: String }>(value: S) {
    let { token: _, ..rest } := value;
}
fun strip_row<row R, row Rest>(value: { ..R }) where R = { token: String, ..Rest } {
    let { token: _, ..rest } := value;
    let remainder: { ..Rest } := rest;
    let first := remainder;
    let second := remainder;
}
fun strip_copy_row<row R: Copy, row Rest>(value: { ..R }) where R = { count: i64, ..Rest } {
    let { count: _, ..rest } := value;
    let first := rest;
    let second := rest;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        7,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "remainder");
    assert_eq!(
        report
            .abstract_body_fallbacks
            .iter()
            .filter(|fallback| fallback.reason
                == "record destructuring requires retained destructor-absence evidence")
            .count(),
        1,
        "{report:#?}"
    );
}

#[test]
fn abstract_ownership_keeps_aspect_names_when_impl_parameters_are_renamed() {
    let report = move_report_for_source_with(
        r#"
aspect R {}
aspect EchoBound { fun echo<R>(&self, value: R) -> R; }
extend<row R: R> { ..R }: EchoBound {
    fun echo<R>(&self, value: R) -> R { value }
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_checks_structural_record_definitions_without_callers() {
    let report = move_report_for_source_with(
        r#"
aspect ReadCount { fun read(&self) -> i64; }
aspect Consume { fun consume(self); fun other<R>(&self, value: R); }
aspect Copied { fun copied(self); }
extend { count: i64 }: ReadCount {
    fun read(&self) -> i64 { self.count + self.count }
}
extend<row R> { ..R }: Consume where R: Copy {
    fun consume(self) { let first := self; let second := self; }
    fun other<R>(&self, value: R) { let first := value; let second := value; }
}
extend<row R> { ..R }: Copied where all R: Copy {
    fun copied(self) { let first := self; let second := self; }
}
aspect Absent { fun no_token(&self); }
aspect Caller { fun absent(&self); }
extend<row Q: !{ token }> { ..Q }: Absent { fun no_token(&self) {} }
extend<row R> { ..R }: Caller where R: !{ token } {
    fun absent(&self) { self.no_token(); }
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        6,
        "{report:#?}"
    );
    // Field-wise Copy cannot grant nominal Copy to an arbitrary record receiver.
    assert_eq!(report.violations.len(), 3, "{report:#?}");
}

#[test]
fn abstract_ownership_retains_body_only_method_row_equations() {
    let report = move_report_for_source_with(
        r#"
struct Holder {}
extend Holder {
    fun check<row R: Copy, row Rest>() where R = { count: i64, ..Rest } {
        let repeat := [] |value: { ..Rest }| { let one := value; let two := value; };
    }
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_retains_method_body_only_parameters() {
    for bound in ["", ": Copy"] {
        let source = format!(
            "struct Marker {{ count: i64 }}\n\
             extend Marker {{\n\
                 fun check<T{bound}>() {{\n\
                     let take := [] |value: T| {{ let one := value; let two := value; }};\n\
                 }}\n\
             }}\n\
             fun main() {{}}"
        );
        let report = move_report_for_source_with(&source, |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        });
        assert_eq!(
            report.checked_abstract_generic_bodies.len(),
            1,
            "{report:#?}"
        );
        assert_eq!(
            report.violations.len(),
            usize::from(bound.is_empty()),
            "{report:#?}"
        );
    }
}

#[test]
fn abstract_ownership_keeps_all_associated_result_origins() {
    for (first, second) in [("first", "second"), ("second", "first")] {
        for second_bound in ["", ": Copy", ": Duplicable"] {
            let source = format!(
                "import std::core::Copy as Duplicable;\n\
                 aspect Source {{\n\
                     type First: Copy; type Second{second_bound};\n\
                     fun first(&self) -> First; fun second(&self) -> Second;\n\
                 }}\n\
                 fun select<S: Source>(source: &S, choose: boolean) {{\n\
                     let item := if (choose) {{ source.{first}() }} else {{ source.{second}() }};\n\
                     let one := item; let two := item;\n\
                 }}\n\
                 fun main() {{}}"
            );
            let report = move_report_for_source_with(&source, |graph| {
                for module in &mut graph.modules {
                    module.scheme_env.clear();
                }
            });
            assert_eq!(
                report.checked_abstract_generic_bodies.len(),
                1,
                "{report:#?}"
            );
            assert_eq!(
                report.violations.len(),
                usize::from(second_bound.is_empty()),
                "{report:#?}"
            );
        }
    }
}

#[test]
fn abstract_ownership_does_not_confuse_associated_copy_bound_identity() {
    for bound in ["Copy", "!BuiltinCopy"] {
        let source = format!(
            "import std::core::Copy as BuiltinCopy;\n\
             aspect Copy {{}}\n\
             aspect Source {{ type Item: {bound}; fun get(self) -> Item; }}\n\
             fun reuse<S: Source>(source: S) {{\n\
                 let item := source.get(); let first := item; let second := item;\n\
             }}\n\
             fun main() {{}}"
        );
        let report = move_report_for_source_with(&source, |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        });
        assert_eq!(
            report.checked_abstract_generic_bodies.len(),
            1,
            "{report:#?}"
        );
        assert_eq!(report.violations.len(), 1, "{report:#?}");
        assert_eq!(report.violations[0].binding, "item", "{report:#?}");
    }
}

#[test]
fn abstract_ownership_retains_expected_type_resolved_unit_variants() {
    let report = move_report_for_source_with(
        r#"
fun unqualified<T>() -> Perhaps<T> { None : Perhaps<T> }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_retains_static_paths_and_unit_variants() {
    let report = move_report_for_source_with(
        r#"
enum Choice<T> { Some { value: T }, None }
struct Factory { count: i64 }
extend Factory { fun count() -> i64 { 1 } }
fun empty<T>() -> Choice<T> { Choice::None }
fun selected<T>(value: T) -> i64 {
    let count := Factory::count();
    let consumed := value;
    value;
    count
}
fun collection<T>(value: T) -> List<T> {
    var result: List<T> := List::new();
    result.push(value);
    result
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        3,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
}

#[test]
fn abstract_ownership_uses_selected_conditional_receiver_mode() {
    let report = move_report_for_source_with(
        r#"
struct Holder<T> { value: T }
extend<T: Copy> Holder<T> { fun touch(&self) -> i64 { 1 } }
extend<T: !Copy> Holder<T> { fun touch(self) -> i64 { 2 } }
fun borrowed<T: Copy>(value: Holder<T>) -> i64 { value.touch() + value.touch() }
struct Reverse<T> { value: T }
extend<T: !Copy> Reverse<T> { fun touch(self) -> i64 { 2 } }
extend<T: Copy> Reverse<T> { fun touch(&self) -> i64 { 1 } }
fun owned<T: !Copy>(value: Reverse<T>) -> i64 { value.touch() + value.touch() }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert!(
        report
            .checked_abstract_generic_bodies
            .iter()
            .any(|span| span.line == 5),
        "{report:#?}"
    );
    assert!(
        report
            .checked_abstract_generic_bodies
            .iter()
            .any(|span| span.line == 9),
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].use_span.line, 9);
}

#[test]
fn abstract_ownership_retains_contextual_literal_array_indices() {
    let report = move_report_for_source_with(
        r#"
fun borrowed<T>(values: [T]) { let selected := &values[0]; }
fun owned<T: Copy>(values: [T; 2]) -> T { values[1] }
fun dynamic_empty<T>(values: [T; 0], index: u64) { let selected := &values[index]; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        3,
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_keeps_borrowed_and_guarded_match_bindings_pending() {
    let report = move_report_for_source_with(
        r#"
fun borrowed<T>(value: &T) { match (value) { bound => { bound; } } }
fun guarded<T>(condition: boolean, value: T) {
    match (value) { bound if condition => {}, _ => {} }
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert!(
        report.checked_abstract_generic_bodies.is_empty(),
        "{report:#?}"
    );
    for reason in [
        "borrowed match binding move contracts are not yet retained",
        "match guard flow facts are not yet retained",
    ] {
        assert!(
            report
                .abstract_body_fallbacks
                .iter()
                .any(|fallback| fallback.reason == reason),
            "{report:#?}"
        );
    }
}

#[test]
fn abstract_ownership_checks_resolved_match_patterns_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
enum Flag { On, Off }
fun flag<T>(tag: Flag, unused: T) -> boolean {
    match (tag) { On => true, Off => false }
}
fun literal<T>(tag: i64, first: T, second: T) -> T {
    match (tag) { 1 => first, _ => second }
}
fun bound<T>(value: T) {
    match (value) { moved => { let consumed := moved; moved; } }
}
fun copied<T: Copy>(value: T) {
    match (value) { moved => { let copied := moved; moved; } }
    value;
}
fun make<T>(value: T) -> Perhaps<T> { Perhaps::Some { value = value } }
fun payload<T>(value: T) {
    match (make(value)) { Some { value } => { let consumed := value; value; }, None => {} }
}
fun temporary<T>(value: T) {
    match ((value, 0)) { moved => { let consumed := moved; } }
    value;
}
fun temporary_array<T>(value: T) {
    match ([value]) { _ => {} }
    value;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        8,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 4, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_checks_record_bound_matches_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun describe<record T: { x: f64, .. }>(value: T) -> f64 {
    match (value) { { x, .. } => x }
}
fun closed<record T: { x: f64 }>(value: T) -> f64 {
    match (value) { { x, .. } => x }
}
fun exact<record T: { x: f64, y: f64 }>(value: T) -> f64 {
    match (value) { { x, y } => x + y }
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        3,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert!(report.abstract_body_fallbacks.is_empty(), "{report:#?}");
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_checks_nominal_row_record_patterns_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
record Packet<row R> { id: i64, data: { ..R } }
extend<row R> Packet<..R> {
    fun packet_id(self) -> i64 {
        let { id, .. } := self;
        id
    }
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert!(report.abstract_body_fallbacks.is_empty(), "{report:#?}");
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_consumes_unproved_nominal_record_copy_without_granting_it() {
    let report = move_report_for_source_with(
        r#"
record Packet<row R> { id: i64, data: { ..R } }
fun consume<row R>(value: Packet<..R>) { let moved := value; }
fun duplicate<row R>(value: Packet<..R>) {
    let first := value;
    let second := value;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert!(report.abstract_body_fallbacks.is_empty(), "{report:#?}");
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "value");
}

#[test]
fn abstract_ownership_checks_nested_tuple_patterns_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun first<T, U>(pair: (T, (U, i64))) -> T {
    match (pair) { (value, (_, _)) => value }
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert!(report.abstract_body_fallbacks.is_empty(), "{report:#?}");
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_checks_exact_fixed_array_patterns_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun first<T>(items: [T; 2]) -> T {
    match (items) { [head, _] => head }
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert!(report.abstract_body_fallbacks.is_empty(), "{report:#?}");
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_checks_fixed_array_rest_patterns_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun leading<T>(items: [T; 3]) -> T {
    match (items) { [value, ..rest] => value }
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert!(report.abstract_body_fallbacks.is_empty(), "{report:#?}");
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_checks_boolean_matches_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun choose<T>(condition: boolean, first: T, second: T) -> T {
    match (condition) { true => first, false => second }
}
fun repeated<T>(condition: boolean, value: T) {
    match (condition) { true => { let first := value; }, false => {} }
    value;
}
fun copied<T: Copy>(condition: boolean, value: T) {
    match (condition) { true => { let first := value; }, _ => {} }
    value;
}
fun returned<T>(condition: boolean, value: T) {
    match (condition) { true => { let first := value; return; }, false => {} }
    value;
}
fun restored<T>(condition: boolean, original: T, replacement: T) -> T {
    var value := original;
    let moved := value;
    match (condition) { true => { value := replacement; }, _ => { value := replacement; } }
    value
}
fun consumed<T>(value: T) -> boolean { true }
fun scrutinee_effect<T>(value: T) {
    match (consumed(value)) { true => {}, _ => {} }
    value;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        7,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 2, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_keeps_noncopy_temporary_indices_pending() {
    let report = move_report_for_source_with(
        r#"
fun temporary<T>(value: T) { let first := [value][0u64]; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert!(
        report.checked_abstract_generic_bodies.is_empty(),
        "{report:#?}"
    );
    assert!(
        report.abstract_body_fallbacks.iter().any(|fallback| {
            !fallback.span.filename.starts_with("<embedded")
                && fallback.reason == "temporary index ownership contract is not yet retained"
        }),
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_checks_copy_elements_of_temporary_arrays() {
    let report = move_report_for_source_with(
        r#"
fun number<T>(value: T) -> i64 { 7 }
fun index<T>(value: T) -> u64 { 0u64 }
fun copied<T: Copy>(value: T, position: u64) -> T { [value, value][position] }
fun effects<T>(value: T, other: T) {
    let result := [number(value), 0][index(other)];
    value; other;
}
fun borrowed<T>(value: T, other: T) {
    let result := (&[number(value), 0])[index(other)];
    value; other;
}
fun nested<T>(value: T, other: T) {
    let result := [[number(value), 0], [0, 1]][index(other)][0u64];
    value; other;
}
fun returning<T>(value: T) {
    let gone := value;
    let result := [loop { return; break 0; }, 0][index(value)];
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        7,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 6, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_keeps_non_numeric_compound_operators_pending() {
    let report = move_report_for_source_with(
        r#"
fun text<T>(unused: T) { var text := "a"; text += "b"; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert!(
        report.checked_abstract_generic_bodies.is_empty(),
        "{report:#?}"
    );
    assert!(
        report.abstract_body_fallbacks.iter().any(|fallback| {
            !fallback.span.filename.starts_with("<embedded")
                && fallback.reason == "compound assignment operator contract is not yet retained"
        }),
        "{report:#?}"
    );
}

#[test]
fn abstract_ownership_reads_compound_targets_without_duplicate_errors() {
    let report = move_report_for_source_with(
        r#"
fun moved<record R: { n: i64, .. }>(value: R) {
    var target := value;
    let gone := target;
    target.n += 1;
}
fun partial<record R: { n: i64, payload: String, .. }>(value: R) {
    var target := value;
    let gone := target.payload;
    target.n += 1;
}
fun stopped<record R: { idx: u64, .. }>(values: &var [[i64; 2]; 2], value: R) {
    let gone := value;
    values[loop { return; break 0u64; }][value.idx] += 1;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        3,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
}

#[test]
fn abstract_ownership_checks_numeric_compound_assignments() {
    let report = move_report_for_source_with(
        r#"
fun choose<T>(value: T) -> u64 { 0u64 }
fun assigned<T>(value: T) {
    var n := 1;
    n += 2; n -= 1; n *= 2; n /= 2; n %= 3;
}
fun indexed<T>(values: &var [i64; 2], value: T) {
    values[choose(value)] += 1;
    value;
}
fun tupled<T>(values: &var [(i64, i64); 2], value: T) {
    values[choose(value)].0 *= 2;
    value;
}
fun projected<record R: { n: i64, .. }>(values: &var [R; 2]) {
    values[0u64].n -= 1;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        5,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 2, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_keeps_non_numeric_cast_contracts_pending() {
    let report = move_report_for_source_with(
        r#"
fun identity<T>(value: T) -> T { value as T }
fun text<T>(unused: T, value: String) -> String { value as String }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert!(
        report.checked_abstract_generic_bodies.is_empty(),
        "{report:#?}"
    );
    assert_eq!(
        report
            .abstract_body_fallbacks
            .iter()
            .filter(|fallback| {
                !fallback.span.filename.starts_with("<embedded")
                    && fallback.reason
                        == "cast dispatch and ownership contracts are not yet retained"
            })
            .count(),
        2,
        "{report:#?}"
    );
}

#[test]
fn abstract_ownership_checks_numeric_casts_and_indices() {
    let report = move_report_for_source_with(
        r#"
fun choose<T>(value: T) -> i64 { 0 }
fun read<T>(values: &[T; 2], value: T) {
    let element := &values[choose(value) as u64];
    value;
}
fun write<T>(values: &var [T; 2], value: T, spare: T) {
    values[choose(value) as u64] := spare;
    value;
}
fun numeric<T>(value: T, number: i64) -> f64 { number as f64 }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        4,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 2, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_checks_break_read_copy_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun narrowed<T>(unused: T, value: &i64) -> i64 {
    loop { break value; }
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_checks_value_producing_loops() {
    let report = move_report_for_source_with(
        r#"
fun extracted<T>(value: T) -> T { loop { break value; } }
fun repeated<T>(value: T) {
    let result := loop { break value; };
    value;
}
fun copied<T: Copy>(value: T) -> T {
    let result := loop { break value; };
    value
}
fun nested<T>(value: T) -> T {
    loop {
        let result := loop { break value; };
        break result;
    }
}
fun statement_loops<T>(value: T) -> T {
    while (true) { break; }
    for (var i := 0; i < 1; i := i + 1) { break; }
    for (item in [1, 2]) { break; }
    loop { break value; }
}
fun returning<T>(value: T) {
    let moved := value;
    let result: () := loop { break if (true) { return; } else { return; }; };
    value;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        6,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_stops_assignment_inputs_after_return() {
    let report = move_report_for_source_with(
        r#"
fun stopped<record T: { idx: u64, .. }>(values: &var [[i64; 2]; 2], value: T) {
    let moved := value;
    values[loop { return; break 0u64; }][value.idx] := 1;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_checks_assignment_rhs_before_index_inputs() {
    let report = move_report_for_source_with(
        r#"
fun choose<T>(first: T, second: T) -> u64 { 0u64 }
fun ordered<T>(slots: &var [T; 2], value: T, spare: T) {
    slots[choose(value, spare)] := value;
}
fun divergent<T>(slots: &var [T; 2], value: T) {
    slots[choose(value, value)] := if (true) { return; } else { return; };
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        3,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert!(
        report.violations[0]
            .moved_span
            .as_ref()
            .is_some_and(|moved| report.violations[0].use_span.col < moved.col),
        "{report:#?}"
    );
}

#[test]
fn abstract_ownership_keeps_assignment_storage_contracts_pending() {
    let report = move_report_for_source_with(
        r#"
fun stored<T>(slots: &var [once || -> T; 2], value: T) {
    slots[0u64] := [value] once || { value };
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert!(
        report.checked_abstract_generic_bodies.is_empty(),
        "{report:#?}"
    );
    assert!(
        report
            .abstract_body_fallbacks
            .iter()
            .any(|fallback| fallback.reason == "assignment storage contract is not yet retained"),
        "{report:#?}"
    );
}

#[test]
fn abstract_ownership_evaluates_indexed_assignment_inputs_once() {
    let report = move_report_for_source_with(
        r#"
fun choose<T>(value: T) -> u64 { 0u64 }
fun assigned<T: Copy>(values: &var [T; 2], value: T, index: u64) { values[index] := value; }
fun field_write<T>(values: &var [{ x: i64 }; 2], value: T) {
    values[choose(value)].x := 1;
    let again := value;
}
fun tuple_write<T>(values: &var [(i64, i64); 2], value: T) {
    values[choose(value)].0 := 1;
    let again := value;
}
fun nested<T>(values: &var [[i64; 2]; 2], first: T, second: T) {
    values[choose(first)][choose(second)] := 1;
    let again_first := first; let again_second := second;
}
fun rhs<T>(values: &var [T; 2], value: T, index: u64) {
    values[index] := value; let again := value;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        6,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert_eq!(report.violations.len(), 5, "{report:#?}");
    assert!(
        report
            .abstract_body_fallbacks
            .iter()
            .all(|fallback| fallback.span.filename.starts_with("<embedded std::")),
        "{report:#?}"
    );
}

#[test]
fn abstract_ownership_keeps_for_continue_reinitializations() {
    let report = move_report_for_source_with(
        r#"
fun eat<T>(value: T) -> i64 { 0 }
fun restored<T>(value: T, replacement: T) {
    var slot := value;
    let first := slot;
    for (; true; eat(slot)) { slot := replacement; continue; }
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert!(!report.violations.is_empty(), "{report:#?}");
    assert!(
        report
            .violations
            .iter()
            .all(|violation| violation.binding == "replacement"),
        "{report:#?}"
    );
    assert!(
        report
            .violations
            .iter()
            .all(|violation| violation.moved_in_previous_iteration),
        "{report:#?}"
    );
}

#[test]
fn abstract_ownership_does_not_consume_unreachable_for_tails() {
    let report = move_report_for_source_with(
        "fun bad<T>(value: T) { for (;;) { continue; (value, value) } } fun main() {}",
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_checks_for_initializers_steps_and_continue_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun eat<T>(value: T) -> i64 { 0 }
fun init_once<T>(value: T) {
    for (let held: T := value; false; ) { let seen := &held; }
}
fun copied<T: Copy>(value: T) {
    for (var i: i64 := 0; i < 2; i := i + 1) { let first := value; }
}
fun step_move<T>(value: T) {
    for (; true; eat(value)) { continue; }
}
fun step_read<T>(value: T) {
    for (; true; eat(value)) { let first := value; continue; }
}
fun broken<T>(value: T) {
    for (; true; eat(value)) { break; }
    let kept := value;
}
fun returned<T>(value: T) {
    for (; true; eat(value)) { return; }
}
fun condition_returns<T>(value: T) {
    for (; if (true) { return; } else { return; }; eat(value)) { continue; }
    let unreachable := value;
    let also_unreachable := value;
}
fun initializer_returns<T>(value: T) {
    for (return; true; eat(value)) { continue; }
}
fun unconditioned<T>(value: T) {
    for (;;) { return; }
    let unreachable := value;
    let also_unreachable := value;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        10,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert!(
        report
            .abstract_body_fallbacks
            .iter()
            .all(|fallback| fallback.span.filename.starts_with("<embedded std::")),
        "{report:#?}"
    );
    assert!(
        report
            .violations
            .iter()
            .any(|violation| violation.moved_in_previous_iteration),
        "{report:#?}"
    );
    assert!(
        report
            .violations
            .iter()
            .any(|violation| !violation.moved_in_previous_iteration),
        "{report:#?}"
    );
    assert!(
        report
            .violations
            .iter()
            .all(|violation| violation.use_span.line == 10 || violation.use_span.line == 13),
        "{report:#?}"
    );
}

#[test]
fn abstract_ownership_checks_exact_ascriptions_and_read_copy() {
    let report = move_report_for_source_with(
        r#"
fun moved<T>(value: T) { let first := (value: T); let second := value; }
fun copied<T: Copy>(value: T) { let first := (value: T); let second := value; }
fun coerced<T>(unused: T, value: &i64) { let owned := (value: i64); }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        3,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_uses_retained_nominal_coherence_without_samples() {
    let report = move_report_for_source_with(
        r#"
struct Owned<T> { value: T }
struct Ticket { count: i64 }
extend Ticket: Copy;
enum Choice<T> { Some { value: T }, None }
struct Handle { name: String }
extend Handle: Drop { fun drop(&var self) {} }
fun repeated<T>(value: Owned<T>) { let first := value; let again := value; }
fun copied<T>(value: Ticket, unused: T) { let first := value; let again := value; }
fun payload<T>(value: Choice<T>) -> T {
    match (value) { Some { value } => value, None => { loop {} } }
}
fun destructor<T>(value: Handle, unused: T) { let name := value.name; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        4,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 2, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_retains_nominal_self_identity_in_generic_bodies() {
    let report = move_report_for_source_with(
        r#"
struct Box<T> { value: T }
extend<T> Box<T> {
    fun consume(self) -> Box<T> { self }
    fun twice(self) { let first := self; let again := self; }
}
fun main() {}
"#,
        |graph| {
            let expected = graph
                .type_registry
                .resolve_type_id(&[], "Box")
                .expect("Box identity");
            let methods = graph
                .modules
                .iter()
                .flat_map(|module| &module.decls)
                .filter_map(|decl| match decl {
                    TypedDecl::Impl(implementation) => Some(&implementation.methods),
                    _ => None,
                })
                .flatten()
                .filter(|method| method.name == "consume" || method.name == "twice")
                .collect::<Vec<_>>();
            assert_eq!(methods.len(), 2);
            for method in methods {
                let Some(crate::data::abstract_body::AbstractBodyPreparation::Typed(body)) =
                    &method.abstract_body
                else {
                    panic!("missing abstract method body");
                };
                assert_eq!(body.nominal_ownership.len(), 1, "{body:#?}");
                assert!(
                    body.nominal_ownership.iter().all(|fact| matches!(
                        &fact.ty,
                        crate::data::abstract_body::AbstractType::Named { identity, .. }
                            if identity.get() == Some(expected)
                    )),
                    "{body:#?}"
                );
            }
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "self");
}

#[test]
fn abstract_ownership_keeps_unknown_conjuncts_distinct_from_disproved_candidates() {
    let report = move_report_for_source_with(
        r#"
aspect Marker {}
aspect Other {}
struct Guard<A, B> { name: String }
extend<A, B> Guard<A, B>: Drop where A: Marker, B: Other { fun drop(&var self) {} }
struct Witness<A, B> { count: i64 }
extend<A, B> Witness<A, B>: Copy;
extend<A, B> Witness<A, B>: !Copy where A: Marker, B: Other;
struct Token<T> { count: i64 }
extend<T> Token<T>: Copy where T: Marker, T: Other;
fun extract<A: !Marker, B>(value: Guard<A, B>) -> String { value.name }
fun unknown_drop<A: Marker, B>(value: Guard<A, B>) -> String { value.name }
fun copied<A: !Marker, B>(value: Witness<A, B>) { let first := value; let again := value; }
fun unknown_override<A: Marker, B>(value: Witness<A, B>) { let first := value; let again := value; }
fun token<T: Marker + Other>(value: Token<T>) { let first := value; let again := value; }
fun unknown_token<T: Marker>(value: Token<T>) { let first := value; let again := value; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        4,
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 3, "{report:#?}");
}

#[test]
fn abstract_ownership_proves_where_conditions_and_destructor_disjointness() {
    let report = move_report_for_source_with(
        r#"
aspect Marker {}
struct Wrapper<T> { value: T }
extend<T> Wrapper<T>: Copy where T: Copy;
struct Guard<T> { name: String, tag: T }
extend<T> Guard<T>: Drop where T: Marker { fun drop(&var self) {} }
fun copied<T: Copy>(value: Wrapper<T>) { let first := value; let again := value; }
fun allowed<T: !Marker>(value: Guard<T>) -> String { value.name }
fun denied<T: Marker>(value: Guard<T>) -> String { value.name }
fun unknown<T>(value: Guard<T>) -> String { value.name }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        4,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].use_span.line, 9, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 1, "{report:#?}");
}

#[test]
fn abstract_ownership_proves_conditional_negative_override() {
    let report = move_report_for_source_with(
        r#"
aspect Marker {}
struct Witness<T> { count: i64 }
extend<T> Witness<T>: Copy;
extend<T: Marker> Witness<T>: !Copy;
fun allowed<T: !Marker>(value: Witness<T>) { let first := value; let again := value; }
fun denied<T: Marker>(value: Witness<T>) { let first := value; let again := value; }
fun unknown<T>(value: Witness<T>) { let first := value; let again := value; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].use_span.line, 7, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 1, "{report:#?}");
}

// arch-verifies: ["arch.move-check.requirement-8"]
#[test]
fn abstract_ownership_proves_declared_conditional_copy() {
    let report = move_report_for_source_with(
        r#"
struct Wrapper<T> { value: T }
extend<T: Copy> Wrapper<T>: Copy;
struct Swapped<A, B> { count: i64 }
extend<Y: Copy, X> Swapped<X, Y>: Copy;
aspect Marker {}
struct Token<T> { count: i64 }
extend<T: !Marker> Token<T>: Copy;
fun copied<T: Copy>(value: Wrapper<T>) { let first := value; let again := value; }
fun swapped<T, U: Copy>(value: Swapped<T, U>) { let first := value; let again := value; }
fun excluded<T: !Marker>(value: Token<T>) { let first := value; let again := value; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        3,
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_retains_unrestricted_generic_nominal_impls() {
    let report = move_report_for_source_with(
        r#"
struct Witness<T> { count: i64 }
extend<T> Witness<T>: Copy;
enum Mark<T> { Only }
extend<T> Mark<T>: Copy;
struct Guardian<T> { value: T }
extend<T> Guardian<T>: Drop { fun drop(&var self) {} }
fun copied<T>(value: Witness<T>) { let first := value; let again := value; }
fun enum_copied<T>(value: Mark<T>) { let first := value; let again := value; }
fun partial<T>(value: Guardian<T>) { let field := value.value; }
fun whole<T>(value: Guardian<T>) { let first := value; let again := value; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        5,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 2, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_does_not_grant_copy_from_an_unrelated_marker() {
    let report = move_report_for_source_with(
        r#"
aspect Copy {}
struct Marker { count: i64 }
extend Marker: Copy;
fun repeated<T>(value: Marker, unused: T) { let first := value; let again := value; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert!(
        report.checked_abstract_generic_bodies.is_empty(),
        "{report:#?}"
    );
    assert!(
        report
            .abstract_body_fallbacks
            .iter()
            .any(|fallback| fallback.reason
                == "abstract conditional nominal aspect entailment is not yet retained"),
        "{report:#?}"
    );
}

#[test]
fn abstract_ownership_preserves_aliased_ownership_aspects() {
    let report = move_report_for_source_with(
        r#"
import std::core::Copy as Repeatable;
import std::core::Drop as Finalize;
struct Witness<T> { count: i64 }
extend<T> Witness<T>: Repeatable;
struct Guardian<T> { value: T }
extend<T> Guardian<T>: Finalize { fun drop(&var self) {} }
struct Conditional<T> { value: T }
extend<T: Copy> Conditional<T>: Finalize { fun drop(&var self) {} }
fun copied<T>(value: Witness<T>) { let first := value; let again := value; }
fun partial<T>(value: Guardian<T>) { let field := value.value; }
fun unknown<T>(value: Conditional<T>) { let field := value.value; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        4,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].use_span.line, 11, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 1, "{report:#?}");
}

#[test]
fn abstract_ownership_keeps_aliased_negative_overrides_pending() {
    let report = move_report_for_source_with(
        r#"
import std::core::Copy as Repeatable;
struct Witness<T> { count: i64 }
extend<T> Witness<T>: Copy;
extend Witness<String>: !Repeatable;
fun repeated<T>(value: Witness<T>) { let first := value; let again := value; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert!(
        report.checked_abstract_generic_bodies.is_empty(),
        "{report:#?}"
    );
    assert!(
        report
            .abstract_body_fallbacks
            .iter()
            .any(|fallback| fallback.reason
                == "abstract conditional nominal aspect entailment is not yet retained"),
        "{report:#?}"
    );
}

#[test]
fn abstract_ownership_does_not_generalize_specialized_nominal_copy() {
    let report = move_report_for_source_with(
        r#"
struct Box<T> { value: T }
extend Box<i64>: Copy;
fun twice<T>(value: Box<T>) { let first := value; let again := value; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert!(
        report.checked_abstract_generic_bodies.is_empty(),
        "{report:#?}"
    );
    assert!(
        report
            .abstract_body_fallbacks
            .iter()
            .any(|fallback| fallback.reason
                == "abstract conditional nominal aspect entailment is not yet retained"),
        "{report:#?}"
    );
}

#[test]
fn abstract_ownership_does_not_assume_conditional_destructor_absent() {
    let report = move_report_for_source_with(
        r#"
struct Guard<T> { value: T }
extend<T: Copy> Guard<T>: Drop { fun drop(&var self) {} }
fun take<T>(value: Guard<T>) -> T { value.value }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    // The destructor definition is checkable; its conditional applicability
    // must not become a negative Drop proof for the unbounded extraction.
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert_eq!(
        report.checked_abstract_generic_bodies[0].line, 3,
        "{report:#?}"
    );
    assert!(
        report
            .abstract_body_fallbacks
            .iter()
            .any(|fallback| fallback.reason
                == "abstract conditional nominal aspect entailment is not yet retained"),
        "{report:#?}"
    );
}

#[test]
fn abstract_ownership_checks_unused_definitions_without_a_reconstruction_context() {
    let report = move_report_for_source_with(
        r#"
fun repeated<T>(value: T) { let first := value; let second := value; }
fun copied<T: Copy>(value: T) { let first := value; let second := value; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "value");
    assert_eq!(report.violations[0].use_span.line, 2);
    assert_eq!(report.skipped_generic_bodies_user, 0);
}

#[test]
fn abstract_ownership_preserves_borrowed_arguments_and_receivers() {
    let report = move_report_for_source(
        r#"
aspect Inspect { fun inspect(&self); }
aspect Consume { fun consume(self); }
fun borrow<T>(value: &T) {}
fun observed<T: Inspect>(value: T) { borrow(&value); value.inspect(); value.inspect(); }
fun consumed<T: Consume>(value: T) { value.consume(); value.consume(); }
fun moved_reference<T>(value: &T) -> T { *value }
fun main() {}
"#,
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        4,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 2, "{report:#?}");
    assert!(
        report
            .violations
            .iter()
            .any(|violation| violation.moved_by_value_receiver)
    );
    assert!(
        report
            .violations
            .iter()
            .any(|violation| violation.kind == MoveViolationKind::MoveOutOfReference)
    );
}

// arch-verifies: ["arch.move-check.requirement-8"]
#[test]
fn abstract_ownership_distinguishes_unknown_and_copy_row_tails() {
    let report = move_report_for_source(
        r#"
fun repeated<row R>(value: { ..R }) { let first := value; let second := value; }
fun copied<row R>(value: { ..R }) where all R: Copy { let first := value; let second := value; }
fun main() {}
"#,
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].use_span.line, 2);
}

#[test]
fn abstract_ownership_restores_projected_places_and_keeps_shadowed_identities_distinct() {
    let report = move_report_for_source(
        r#"
fun restore<T>(initial: T, replacement: T) -> T {
    var pair := (initial, 0);
    let first := pair.0;
    pair.0 := replacement;
    pair.0
}
fun shadow<T>(value: T, other: T) {
    let first := value;
    let value := other;
    let second := value;
}
fun main() {}
"#,
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_retains_loop_carried_moves_and_function_exits() {
    let report = move_report_for_source(
        r#"
fun repeated<T>(value: T) { loop { let moved := value; } }
fun exits<T>(value: T) { loop { let moved := value; return; } }
fun main() {}
"#,
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert!(report.violations[0].moved_in_previous_iteration);
}

#[test]
fn abstract_ownership_consumes_by_value_receivers_through_references() {
    let report = move_report_for_source(
        r#"
aspect Take { fun take(self); }
fun receiver<T: Take>(value: &T) { value.take(); }
fun mutable_reference<T>(value: &&var T) -> &var T { *value }
fun main() {}
"#,
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 2, "{report:#?}");
    assert!(
        report
            .violations
            .iter()
            .all(|violation| violation.kind == MoveViolationKind::MoveOutOfReference)
    );
}

#[test]
fn abstract_ownership_checks_move_only_owned_closure_entry_and_body() {
    let report = move_report_for_source(
        r#"
fun repeated<T>(value: T) {
    let f := [value] once || { let first := value; let second := value; };
}
fun unused<T>(value: T) {
    let f := [value] once || {};
    let again := value;
}
fun main() {}
"#,
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 2, "{report:#?}");
    assert!(
        report
            .violations
            .iter()
            .all(|violation| violation.binding == "value")
    );
}

#[test]
fn abstract_ownership_reports_preparation_and_consumer_fallbacks_without_partial_results() {
    let report = move_report_for_source_with(
        r#"
struct Holder<T> { value: T }
extend<T: Copy> Holder<T>: Copy;
fun preparation<T>(value: T) { fun nested() -> i64 { 1 } }
fun ownership<T>(value: T, holder: Holder<T>) {
    let first := value; let second := value; let held := holder;
}
fun completed<T: Copy>(value: T) { let first := value; let second := value; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    let fallbacks: Vec<_> = report
        .abstract_body_fallbacks
        .iter()
        .filter(|fallback| !fallback.span.filename.starts_with("<embedded std::"))
        .collect();
    assert_eq!(fallbacks.len(), 2, "{report:#?}");
    assert_eq!(fallbacks[0].stage, AbstractBodyFallbackStage::Preparation);
    assert_eq!(
        fallbacks[0].reason,
        "nested declarations and patterns are not yet retained in abstract bodies"
    );
    assert_eq!(fallbacks[1].stage, AbstractBodyFallbackStage::Ownership);
    assert_eq!(
        fallbacks[1].reason,
        "abstract conditional nominal aspect entailment is not yet retained"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 2, "{report:#?}");
}

#[test]
fn abstract_ownership_checks_builtin_operators_and_operand_effects_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun eat<T>(value: T) -> boolean { true }
fun numeric<T>(unused: T, left: i64, right: i64, flag: boolean) {
    let sum := -left + right * 2;
    let ordered := sum < right;
    let logical := !flag || ordered;
    let range := left..right;
}
fun text<T>(unused: T, value: String) {
    let first := value + "a"; let second := value + "b";
}
fun bad_read<T>(unused: T, value: String) {
    let moved := value; let compare := value == "gone";
}
fun eager<T>(value: T) { let both := eat(value) && eat(value); }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        5,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 2, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert!(
        report
            .abstract_body_fallbacks
            .iter()
            .all(|fallback| fallback.span.filename.starts_with("<embedded std::")),
        "{report:#?}"
    );
}

#[test]
fn abstract_ownership_checks_array_iteration_modes_and_loop_carried_moves() {
    let report = move_report_for_source_with(
        r#"
fun copied<T: Copy>(items: [T]) {
    for (item in items) { let first := item; let second := item; }
}
fun owned<T>(items: [T; 2]) { for (item in items) { let first := item; } }
fun borrowed<T>(items: [T]) { for (item in items) { let first := item; } }
fun copied_reference<T: Copy>(items: &[T]) {
    for (item in items) { let first := item; let second := item; }
}
fun repeated<T>(value: T, items: [i64; 2]) {
    for (item in items) { let moved := value; }
}
fun captured<T>(items: [T]) {
    for (item in items) { let f := [item] once || {}; }
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        6,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert_eq!(report.violations.len(), 3, "{report:#?}");
    assert_eq!(
        report
            .violations
            .iter()
            .filter(|violation| violation.kind == MoveViolationKind::BorrowedArrayElementMove)
            .count(),
        2,
        "{report:#?}"
    );
    assert_eq!(
        report
            .violations
            .iter()
            .filter(|violation| violation.moved_in_previous_iteration)
            .count(),
        1,
        "{report:#?}"
    );
}

#[test]
fn abstract_ownership_checks_copyable_closure_contracts_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun copied<T: Copy>(value: T) {
    let f := [value] once || { value };
    let first := f;
    let second := f;
}

fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_preserves_closure_capture_contracts_through_local_aliases() {
    let report = move_report_for_source_with(
        r#"
fun empty<T>(unused: T) {
    let f := [] || {}; let first := f; let second := f; f(); f();
}
fun copied<T: Copy>(value: T) {
    let f := [value] || { let first := value; let second := value; };
    f(); f(); let alias := f; alias();
}
fun borrowed<T>(value: T) {
    let f := [&value] once || { let first := value; let second := value; };
    let first := f; let second := f;
}
fun nested<T: Copy>(value: T) {
    let f := [value] once || { value };
    let g := [f] once || { let first := f; let second := f; };
    let first := g; let second := g; let again := f;
}
fun moved<T>(value: T) {
    let f := [value] once || {}; let first := f; let second := f;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        5,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 3, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert_eq!(
        report
            .violations
            .iter()
            .filter(|violation| violation.kind == MoveViolationKind::MoveOutOfReference)
            .count(),
        2
    );
}

// arch-verifies: ["arch.move-check.requirement-8", "arch.move-check.requirement-10"]
#[test]
fn abstract_ownership_retains_implicit_copy_capture_environments() {
    let report = move_report_for_source_with(
        r#"
fun copied<T: Copy>(value: T) {
    let f := || { let first := value; let second := value; };
    f(); f(); let alias := f; alias(); let again := value;
}
fun owned<T>(value: T) {
    let f := [value] once || { value }; let first := f; let second := f;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    // `owned` moves its `once` closure twice; `copied` is a legal Copy environment.
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_does_not_erase_implicit_captures_in_nominal_literals() {
    let report = move_report_for_source_with(
        r#"
struct Packet<T> { payload: T }
fun copied<T: Copy>(value: T) {
    let f := || { let packet := Packet { payload = value }; };
    let again := value;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_closed_rows_preserve_noncopy_and_mixed_head_controls() {
    let report = move_report_for_source(
        r#"
fun copied<row R: { count: i64 }>(r: { ..R }) { let first := r; let second := r; }
fun owned<row R: { payload: String }>(r: { ..R }) { let first := r; let second := r; }
fun mixed<row R: { count: i64 }>(r: { payload: String, ..R }) { let first := r; let second := r; }
fun mixed_copy<row R: { count: i64 }>(r: { header: i64, ..R }) { let first := r; let second := r; }
fun branded<record T: { count: i64 }>(r: T) { let first := r; let second := r; }
fun main() {}
"#,
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        5,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 3, "{report:#?}");
    assert!(
        report
            .violations
            .iter()
            .all(|violation| matches!(violation.use_span.line, 3 | 4 | 6))
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_renders_global_binding_names_without_identity_tokens() {
    let report = move_report_for_source(
        r#"
let token := "owned";
fun repeated<T>(unused: T) { let first := token; let second := token; }
fun main() {}
"#,
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "token");
    assert_eq!(report.violations[0].moved_place.to_string(), "token");
}

#[test]
fn abstract_ownership_checks_exact_local_annotations_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun repeated<T>(value: T) { let first: T := value; let second: T := first; let third := first; }
fun copied<T: Copy>(value: T) { let first: T := value; let second: T := first; let third := first; }
fun restored<T>(value: T, replacement: T) { var local: T := value; let first := local; local := replacement; let second: T := local; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        3,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "first");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_checks_annotated_read_copy_coercions_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun copied<T>(unused: T, value: &i64) { let first: i64 := value; }
fun shared<T>(unused: T, value: &var i64) { let first: &i64 := value; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_checks_callable_boundaries_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun invoke(callback: once || -> i64) -> i64 { callback() }
fun returned<T>(value: T) -> once || -> T { [value] once || { value } }
fun annotated<T: Copy>(value: T) {
    let callback: once || -> T := [value] once || { value };
    let first := callback; let second := callback;
}
fun argument<T>(value: T) {
    let callback := [value] once || { 1 };
    invoke(callback); callback();
}
fun explicit<T>(value: T) -> once || -> T { return [value] once || { value }; }
fun branch<T>(value: T, other: T, flag: boolean) -> once || -> T {
    if (flag) { [value] once || { value } } else { [other] once || { other } }
}
fun ascribed<T: Copy>(value: T) {
    let callback := ([value] once || { value }: once || -> T);
    let first := callback; let second := callback;
}
fun preserved<T: Copy>(value: T) {
    let source := [value] once || -> T { value };
    let callback: once || -> T := source;
    source();
    let first := callback; let second := callback;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        7,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert_eq!(report.violations.len(), 4, "{report:#?}");
    assert!(
        report
            .violations
            .iter()
            .all(|violation| violation.binding == "callback")
    );
}

#[test]
fn abstract_ownership_checks_borrowed_value_boundaries_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun deep<T>(unused: T, value: &&i64) { let first: i64 := value; let again := value; }
fun returned<T>(unused: T, value: &i64) -> i64 { value }
fun explicit<T>(unused: T, value: &i64) -> i64 { return value; }
fun exited<T>(unused: T, value: &i64) -> i64 { loop { break value; } }
fun ascribed<T>(unused: T, value: &i64) { let first := (value: i64); let again := value; }
fun copied_record<T: Copy>(value: &{ item: T }) -> { item: T } { value }
fun shared<T>(unused: T, value: &var i64) { let first: &i64 := value; let again := value; }
fun mutable_read<T>(unused: T, value: &var i64) { let first: i64 := value; let again := value; }
fun borrowed<T>(owned: T) -> &i64 { &1 }
fun effect<T>(value: T) { let copied: i64 := borrowed(value); let again := value; }
fun tail_ascribed<T>(unused: T, value: &i64) -> i64 { (value: i64) }
fun nested<T>(unused: T, value: &i64) {
    let callback := [value] once || -> i64 { (value: &i64) };
    callback()
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        12,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert_eq!(report.violations.len(), 2, "{report:#?}");
    assert_eq!(report.violations[0].binding, "value");
    assert_eq!(report.violations[0].use_span.line, 8);
    assert_eq!(report.violations[1].use_span.line, 11);
}

#[test]
fn abstract_ownership_checks_array_views_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun empty<T>() -> [T] { [] }
fun returned<T>(value: [T; 2]) -> [T] { value }
fun explicit<T>(value: [T; 2]) -> [T] { return value; }
fun exited<T>(value: [T; 2]) -> [T] { loop { break value; } }
fun ascribed<T>(value: [T; 2]) -> [T] { (value: [T]) }
fun copied_view<T>(value: [T]) { let first := value; let second := value; }
fun binding<T>(value: [T; 2]) {
    let view: [T] := value; let first := view; let second := view; let owner := value;
}
fun literal<T>(value: T) { let view: [T] := [value]; let again := value; }
fun illegal<T>(view: [T]) { let value := view[0]; }
fun indexed<T: Copy>(view: [T]) { let first := view[0]; let second := view[0]; }
fun moved<T>(value: [T; 1]) { let owner := value; let view: [T] := value; }
fun copy_owner<T>(unused: T, value: [i64; 1]) { let owner := value; let view: [i64] := value; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        12,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert_eq!(report.violations.len(), 3, "{report:#?}");
    assert_eq!(report.violations[0].binding, "value");
    assert_eq!(report.violations[0].use_span.line, 11);
    assert_eq!(report.violations[1].binding, "view");
    assert_eq!(
        report.violations[1].kind,
        MoveViolationKind::ArrayElementMove
    );
    assert_eq!(report.violations[2].binding, "value");
    assert_eq!(report.violations[2].kind, MoveViolationKind::UseAfterMove);
}

#[test]
fn abstract_ownership_checks_array_view_arguments_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun take<T>(view: [T]) -> i64 { view.len() }
struct Sink {}
extend Sink {
    fun accept<T>(&self, view: [T]) -> i64 { view.len() }
}
fun repeated<T>(value: [T; 2]) { take(value); take(value); let owner := value; }
fun method<T>(sink: &Sink, value: [T; 2]) { sink.accept(value); let owner := value; }
fun literal<T>(value: T) { take([value]); let again := value; }
fun empty<T>(unused: T) { take::<T>([]); }
fun need<T: Copy>(value: &T) {}
fun bounded<T: Copy>(value: T) { need::<T>(&value); let first := value; let second := value; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        8,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "value");
    assert_eq!(report.violations[0].use_span.line, 9);
}

#[test]
fn abstract_ownership_checks_explicit_call_bound_forwarding() {
    assert_typecheck_error_contains(
        "fun need<T: Copy>(value: T) {} fun bad<U>(value: U) { need::<U>(value); } fun main() {}",
        "[T0012]",
    );
    assert_typecheck_error_contains(
        "fun take<T>(value: [T]) {} fun bad<U>(value: U) { take::<U, i64>([]); } fun main() {}",
        "[T0004]",
    );
    assert_typecheck_error_contains(
        "fun absent<row R: !{token}>(values: [{..R}]) -> i64 { values.len() } fun caller<row T>() -> i64 { absent::<T>([]) } fun main() {}",
        "[T0012]",
    );
    let report = move_report_for_source_with(
        "fun no_drop<T: !Drop>(value: T) -> T { value } fun copied<T: Copy>(value: T) -> T { no_drop::<T>(value) } fun main() {}",
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_checks_array_view_receivers_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
extend<T> [T] { fun width(self) -> i64 { self.len() } }
fun value_receiver<T>(value: [T; 2]) { value.width(); value.width(); let owner := value; }
fun borrowed_receiver<T>(value: &[T; 2]) { value.width(); let again := value; }
fun absent<row R: !{token}>(values: [{..R}]) -> i64 { values.len() }
fun forwarded<row R: !{token}>(values: [{..R}]) -> i64 { absent::<R>(values) }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        5,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_checks_unused_generic_methods_and_inherited_grants() {
    let report = move_report_for_source_with(
        r#"
struct Holder {}
extend Holder {
    fun repeated<T>(&self, value: T) { let first := value; let second := value; }
    fun copied<T: Copy>(&self, value: T) { let first := value; let second := value; }
}
struct Bounded<T: Copy> { value: T }
extend<T> Bounded<T> {
    fun inherited(&self, value: T) { let first := value; let second := value; }
    fun extra<U>(&self, value: T, extra: U) { let a := value; let b := value; let c := extra; let d := extra; }
}
struct Packet<T> { payload: T }
extend<T> Packet<T> {
    fun borrowed(&self) { let first := self.payload; }
}
fun main() {}
"#,
        |graph| {
            for method in graph
                .modules
                .iter()
                .flat_map(|module| &module.decls)
                .filter_map(|decl| {
                    if let TypedDecl::Impl(ib) = decl {
                        Some(&ib.methods)
                    } else {
                        None
                    }
                })
                .flatten()
                .filter(|method| {
                    matches!(
                        method.name.as_str(),
                        "repeated" | "copied" | "inherited" | "extra" | "borrowed"
                    )
                })
            {
                assert!(
                    matches!(
                        method.abstract_body,
                        Some(crate::data::abstract_body::AbstractBodyPreparation::Typed(
                            _
                        ))
                    ),
                    "{}: {:?}",
                    method.name,
                    method.abstract_body
                );
            }
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        5,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 3, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert!(
        report
            .violations
            .iter()
            .any(|violation| violation.kind == MoveViolationKind::MoveOutOfReference)
    );
}

#[test]
fn abstract_ownership_distinguishes_conditional_method_binders() {
    let report = move_report_for_source_with(
        r#"
struct Holder<T> { value: T }
extend<T: Copy> Holder<T> { fun probe<U>(&self, value: U) { let moved := value; value; } }
extend<T: !Copy> Holder<T> { fun probe<V: Copy>(&self, value: V) { let copied := value; value; } }
fun main() {}
"#,
        |graph| {
            use crate::data::abstract_body::AbstractBodyPreparation;
            let methods = graph
                .modules
                .iter()
                .flat_map(|module| &module.decls)
                .filter_map(|decl| {
                    if let TypedDecl::Impl(ib) = decl {
                        Some(ib.methods.iter())
                    } else {
                        None
                    }
                })
                .flatten()
                .filter(|method| method.name == "probe")
                .collect::<Vec<_>>();
            assert_eq!(methods.len(), 2);
            let signatures = methods
                .iter()
                .map(|method| {
                    method
                        .abstract_signature
                        .as_ref()
                        .expect("retained method signature")
                })
                .collect::<Vec<_>>();
            assert_ne!(signatures[0].binder, signatures[1].binder);
            for method in methods {
                assert!(matches!(
                    &method.abstract_body,
                    Some(AbstractBodyPreparation::Typed(_))
                ));
            }
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
}

#[test]
fn abstract_ownership_aligns_method_templates_with_forward_recursive_calls() {
    let report = move_report_for_source_with(
        r#"
struct Holder {}
extend Holder {
    fun forward<T>(&self, value: T) -> T { let returned := left(value); value }
    fun copy_forward<T: Copy>(&self, value: T) -> T { let returned := left(value); value }
}
fun left<T>(value: T) -> T { right(value) }
fun right<U>(value: U) -> U { left(value) }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        4,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "value");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_inherits_fieldwise_copy_through_row_remainders() {
    let report = move_report_for_source_with(
        r#"
fun copied<row R, row Rest>(source: { ..R }, rest: { ..Rest })
where R = { token: i64, ..Rest }, all R: Copy {
    let first := rest; let second := rest;
}
fun chained<row R, row Mid, row Rest>(source: { ..R }, rest: { ..Rest })
where R = { token: i64, ..Mid }, Mid = { count: i64, ..Rest }, all R: Copy {
    let first := rest; let second := rest;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert!(report.violations.is_empty(), "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_does_not_reverse_row_remainder_copy_grants() {
    let report = move_report_for_source_with(
        r#"
fun source<row R, row Rest>(value: { ..R }, rest: { ..Rest })
where R = { token: String, ..Rest }, all Rest: Copy {
    let first := value; let second := value;
}
fun unbounded<row R, row Rest>(rest: { ..Rest })
where R = { token: i64, ..Rest } {
    let first := rest; let second := rest;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 2, "{report:#?}");
    assert_eq!(report.violations[0].binding, "value");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_remainder_copy_requires_every_exception_removed() {
    // Exceptions are internal retained facts, not a separate surface syntax.
    let report = move_report_for_source_with(
        r#"
fun covered<row R, row Rest>(source: { ..R }, rest: { ..Rest })
where R = { token: i64, ..Rest }, all R: Copy {
    let first := rest; let second := rest;
}
fun uncovered<row R, row Rest>(source: { ..R }, rest: { ..Rest })
where R = { token: i64, ..Rest }, all R: Copy {
    let first := rest; let second := rest;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
                for decl in &mut module.decls {
                    let TypedDecl::Fun(fun) = decl else { continue };
                    let label = match fun.name.as_str() {
                        "covered" => "token",
                        "uncovered" => "payload",
                        _ => continue,
                    };
                    let signature = fun.abstract_signature.as_mut().expect("signature");
                    let mut changed = false;
                    for bound in signature
                        .facts
                        .as_mut()
                        .expect("facts")
                        .iter_mut()
                        .flat_map(|facts| &mut facts.positive)
                    {
                        if let crate::data::abstract_body::AbstractBound::AllFields {
                            except, ..
                        } = bound
                        {
                            except.push(label.to_string());
                            changed = true;
                        }
                    }
                    assert!(changed, "fieldwise grant retained");
                }
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "rest");
}

#[test]
fn abstract_ownership_checks_array_index_reads_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun copied<T: Copy>(values: [T; 2], index: u64) { let first := values[index]; let second := values[index]; }
fun owned<T>(values: [T; 2], index: u64) { let first := values[index]; }
fun borrowed<T>(values: &[T; 2], index: u64) { let first := values[index]; }
fun nested<T>(values: ([T; 2], i64), index: u64) { let first := values.0[index]; }
fun view<T: Copy>(values: &[T], index: u64) { let first := values[index]; let second := values[index]; }
fun deep<T: Copy>(values: & &[T; 2], index: u64) { let first := values[index]; let second := values[index]; }
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        6,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 3, "{report:#?}");
    assert!(
        report
            .violations
            .iter()
            .all(|violation| violation.kind == MoveViolationKind::ArrayElementMove)
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_evaluates_indices_inside_projection_chains() {
    let report = move_report_for_source_with(
        r#"
fun choose<T>(value: T) -> u64 { 0u64 }
fun indexed<T>(values: [(i64, i64); 2], value: T) {
    let first := values[choose(value)].0;
    let second := value;
}
fun observed<T>(values: [i64; 2], value: T) {
    values[choose(value)];
    let second := value;
}
fun nested<T>(values: [[i64; 2]; 2], indices: [u64; 2], value: T) {
    let first := values[indices[choose(value)]][0u64];
    let second := value;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        4,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 3, "{report:#?}");
    assert!(report.violations.iter().all(|violation| violation.kind
        == MoveViolationKind::UseAfterMove
        && violation.binding == "value"));
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_separates_index_coercions_from_retained_operations() {
    let report = move_report_for_source_with(
        r#"
fun coerced<T: Copy>(values: [T; 2]) { let first := values[0]; }
fun temporary<T: Copy>(value: T, index: u64) { let first := [value, value][index]; }
fun assigned<T: Copy>(values: &var [T; 2], value: T, index: u64) { values[index] := value; }
fun choose<T>(value: T) -> u64 { 0u64 }
fun field_write<T>(values: &var [{ x: i64 }; 2], value: T) {
    values[choose(value)].x := 1;
    let again := value;
}
fun tuple_write<T>(values: &var [(i64, i64); 2], value: T) {
    values[choose(value)].0 := 1;
    let again := value;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                for decl in &module.decls {
                    if let TypedDecl::Fun(fun) = decl
                        && matches!(fun.name.as_str(), "field_write" | "tuple_write")
                    {
                        assert!(
                            matches!(
                                &fun.abstract_body,
                                Some(crate::data::abstract_body::AbstractBodyPreparation::Typed(
                                    _
                                ))
                            ),
                            "{}: {:?}",
                            fun.name,
                            fun.abstract_body
                        );
                    }
                }
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        6,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert_eq!(report.violations.len(), 2, "{report:#?}");
}

#[test]
fn abstract_ownership_checks_record_destructuring_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
fun owned<T>(value: { payload: T, count: i64 }) {
    let { payload, .. } := value; let count := value.count;
    let first := payload; let again := payload;
}
fun copied<T: Copy>(value: { payload: T, count: i64 }) {
    let { payload, .. } := value; let first := payload; let again := payload;
}
fun temporary<T>(value: T) {
    let { payload, .. } := { payload = value, count = 1 }; let again := value;
}
fun remainder<T>(value: { payload: T, count: i64 }) {
    let { payload, ..rest } := value; let first := rest; let again := rest;
}
fun mutable<T>(value: T, replacement: T) {
    let var { payload, .. } := { payload = value }; let first := payload;
    payload := replacement; let again := payload;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        5,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 2, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_evaluates_record_pattern_indices_once() {
    let report = move_report_for_source_with(
        r#"
fun choose<T>(value: T) -> u64 { 0u64 }
fun indexed<T>(values: [{ left: i64, right: i64 }; 2], value: T) {
    let { left, right } := values[choose(value)]; let again := value;
}
fun forbidden<T>(values: [{ payload: T }; 2], index: u64) {
    let { payload } := values[index];
}
fun discarded<T>(values: [{ payload: T }; 2], index: u64) {
    let { payload: _ } := values[index];
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        4,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 3, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_preserves_empty_rows_and_pattern_identities_without_guessing_open_shapes() {
    let report = move_report_for_source_with(
        r#"
fun copied<row R>(value: { payload: String, ..R }) where all R: Copy {
    let { payload: _, ..rest } := value; let first := rest; let again := rest;
}
fun owned<row R>(value: { payload: String, ..R }) {
    let { payload: _, ..rest } := value; let first := rest; let again := rest;
}
fun empty<T>(value: { payload: T }) {
    let { payload: _, ..rest } := value; let first := rest; let again := rest;
}
fun shadow<T>(payload: T, value: { payload: T }) {
    let { payload } := value; let first := payload; let again := payload;
}
fun preserved<T, row R>(value: { payload: T, ..R }) {
    let { payload, .. } := value; let first := payload; let again := payload;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        5,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 3, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_composes_row_heads_and_copy_tails() {
    let report = move_report_for_source_with(
        r#"
fun copied<row R, row Tail>(value: { ..R })
where R = { count: i64, ..Tail }, all Tail: Copy {
    let first := value; let again := value;
}
fun chained<row R, row Rest, row Tail>(rest: { ..Rest })
where R = { token: String, ..Rest }, Rest = { count: i64, ..Tail }, all Tail: Copy {
    let first := rest; let again := rest;
}
fun owned<row R, row Tail>(value: { ..R })
where R = { token: String, ..Tail }, all Tail: Copy {
    let first := value; let again := value;
}
fun alternatives<T, row R, row A, row B: Copy>(value: { ..R })
where R = { a: T, ..A }, R = { b: i64, ..B }, all A: Copy {
    let first := value; let again := value;
}
fun closed_alternative<T, row R: { a: T, b: i64 }, row B: Copy>(value: { ..R })
where R = { b: i64, ..B } {
    let first := value; let again := value;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        5,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "value");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_derives_closed_remainder_ownership_without_samples() {
    let report = move_report_for_source_with(
        r#"
fun copied<row R: { token: String, count: i64 }, row Rest>(rest: { ..Rest })
where R = { token: String, ..Rest } {
    let first := rest; let again := rest;
}
fun owned<row R: { token: i64, payload: String }, row Rest>(rest: { ..Rest })
where R = { token: i64, ..Rest } {
    let first := rest; let again := rest;
}
fun empty<row R: { token: String }, row Rest>(rest: { ..Rest })
where R = { token: String, ..Rest } {
    let first := rest; let again := rest;
}
fun chain<row R: { token: String, payload: String, count: i64 }, row Rest, row Tail>(tail_value: { ..Tail })
where R = { token: String, ..Rest }, Rest = { payload: String, ..Tail } {
    let first := tail_value; let again := tail_value;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        4,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "rest");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_checks_parameter_backed_record_pattern_consumption() {
    let report = move_report_for_source_with(
        r#"
fun whole<row R>(value: { payload: String, ..R }) where all R: Copy {
    let { payload: _, ..rest } := value;
    let first := rest; let again := rest;
    let invalid := value;
}
fun fields<row R>(value: { payload: String, count: i64, ..R }) {
    let { payload: _, .. } := value;
    let count := value.count;
    let invalid := value.payload;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 2, "{report:#?}");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
}

#[test]
fn abstract_ownership_checks_explicit_open_record_pattern_remainders() {
    let report = move_report_for_source_with(
        r#"
fun copied<T, row R: !{ payload }>(payload: T, tail_value: { ..R }) where all R: Copy {
    let { payload: _, ..rest } := { payload = payload, ..tail_value };
    let first := rest; let again := rest;
}
fun owned<T, row R: !{ payload }>(payload: T, tail_value: { ..R }) {
    let { payload: _, ..rest } := { payload = payload, ..tail_value };
    let first := rest; let again := rest;
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "rest");
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
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
    let err = match result {
        Err(err) => err,
        Ok(()) => panic!("expected a typecheck error, got a clean typecheck: {source}"),
    };
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
        // Frozen identities are required to retain abstract bodies, exactly as in the
        // compiler pipeline.
        let members = crate::identity::collect_members_for_graph(&graph, &names);
        let allocation = crate::identity::allocate_for_graph(&graph, &names);
        let normalized =
            path_normalization::normalize(graph, names).expect("normalize temp fixture");
        coherence::check(&normalized).expect("coherence temp fixture");
        let typed = type_checking::check_graph_with_report(
            &normalized,
            &type_checking::CorePrelude::default(),
            Some(crate::identity::FrozenIdentity {
                members: &members,
                binding_spans: &allocation.binding_spans,
            }),
        )
        .expect("typecheck temp fixture")
        .graph;
        match check_graph(&typed) {
            Ok(()) => Vec::new(),
            // An incomplete analysis surfaces as I0011; its message is what these
            // tests inspect. Any other error is a real move violation.
            Err(MetelError::Internal {
                code: InternalErrorCode::I0011,
                message,
            }) => vec![message],
            Err(error) => panic!("move-check temp fixture: {error:?}"),
        }
    })();
    let _ = std::fs::remove_file(&path);
    warnings
}

// arch-verifies: ["arch.move-check.requirement-1"]
#[test]
fn symbolic_row_forwarding_closure_is_checked_without_skipping() {
    let source = r#"
fun add<row R: !{token}>(r: { ..R }) -> { token: String, ..R } {
    { ..r, token = "secret" }
}
fun test<row R: !{token}>(r: { ..R }) -> i64 where all R: Copy {
    let f := [r] once || {
        let added := add(r);
        let copy := r;
        7
    };
    f()
}
fun main() { assert(test({ n = 1 }) == 7); assert(test({}) == 7); }
"#;
    assert_no_violations(source);
    let warnings = move_warnings_for_source(source);
    assert!(
        warnings.is_empty(),
        "symbolic rows must not skip ownership: {warnings:#?}"
    );
}

// arch-verifies: ["arch.move-check.requirement-1"]
#[test]
fn symbolic_row_without_all_copy_is_still_move_only() {
    assert_has_violation(
        r#"
fun add<row R: !{token}>(r: { ..R }) -> { token: String, ..R } {
    { ..r, token = "secret" }
}

fun test<row R: !{token}>(r: { ..R }) -> i64 {
    let f := [r] once || {
        let added := add(r);
        let again := r;
        7
    };
    f()
}
fun main() {}
"#,
        "r",
    );
}

#[test]
fn symbolic_row_known_copy_head_and_unknown_tail_are_distinct() {
    let source = r#"
fun duplicate<row R: { count: i64, .. }>(r: { ..R }) -> i64 where all R: Copy {
    let copy := r;
    let again := r;
    7
}
fun main() { assert(duplicate({ count = 3, flag = true }) == 7); }
"#;
    assert_no_violations(source);
    assert!(move_warnings_for_source(source).is_empty());
}

#[test]
fn return_only_generic_parameter_is_checked_symbolically() {
    let source = r#"
fun make<V>() -> [V] { [] }
fun wrapper<U>() -> [U] {
    let out: [U] := make();
    out
}
fun main() { let out: [i64] := wrapper(); }
"#;
    assert!(move_warnings_for_source(source).is_empty());
    assert_no_violations(source);
}

#[test]
fn symbolic_row_closed_bound_has_no_unknown_tail() {
    let source = r#"
fun duplicate<row R: { count: i64 }>(r: { ..R }) -> i64 {
    let copy := r;
    let again := r;
    7
}
fun main() { assert(duplicate({ count = 3 }) == 7); }
"#;
    assert_no_violations(source);
    assert!(move_warnings_for_source(source).is_empty());
}

// arch-verifies: ["arch.move-check.requirement-1"]
#[test]
fn ambiguous_aspect_method_body_is_analyzed_from_its_retained_definition() {
    // Reconstruction could not build this body and reported the ambiguity as an unchecked
    // body. The retained definition-time body carries the resolved facts, so it is analysed
    // completely and nothing is reported as incomplete.
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
    assert!(warnings.is_empty(), "{warnings:#?}");
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
fn abstract_ownership_checks_bounded_method_generic_call_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
aspect GenericSink { fun take<U: Copy>(&self, other: U); }
fun take_copy<T: GenericSink, U: Copy>(value: T, other: U) -> U {
    value.take(other);
    other
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert!(report.abstract_body_fallbacks.is_empty(), "{report:#?}");
    assert!(report.violations.is_empty(), "{report:#?}");
}

#[test]
fn abstract_ownership_checks_blanket_impl_target_without_reconstruction() {
    let report = move_report_for_source_with(
        r#"
aspect Marker { fun mark(self) -> String; }
extend<T> T: Marker {
    fun mark(self) -> String {
        let moved := self;
        let moved_again := self;
        "ok"
    }
}
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        1,
        "{report:#?}"
    );
    assert_eq!(report.skipped_generic_bodies_user, 0, "{report:#?}");
    assert!(report.abstract_body_fallbacks.is_empty(), "{report:#?}");
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "self");
}

#[test]
fn method_generic_bound_body_is_analyzed_from_its_retained_definition() {
    // The method's own `U: Copy` bound is a fact of the declaration, not something a
    // placeholder sample must satisfy, so the caller's unbounded `U` is analysed.
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
    assert!(warnings.is_empty(), "{warnings:#?}");
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
fn destructuring_temporary_consumes_its_non_copy_inputs() {
    assert_has_violation(
        r#"
fun main() {
    let owned := "owned";
    let { pair } := { pair = (owned, "other") };
    println(owned);
}
"#,
        "owned",
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
fun first<T>(items: [T]) -> T {
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
fun first<T: Copy>(items: [T]) -> T {
for (item in items) {
    return item;
}
panic("empty")
}

fun main() {
let values: [i64] := [1, 2, 3];
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

use crate::pipeline::type_checking::type_engine::{InferType, TypeVar};

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

// ── `moved_span` (#1447) ──
//
// An illegal move (out of a reference, out of a borrowed `[T]` view) has no earlier
// move site. The report says so with `None` instead of a placeholder span, and a
// genuine use-after-move still names its real move site.

#[test]
fn illegal_moves_have_no_moved_span_and_use_after_move_has_one() {
    let from_reference = move_violations_for_source(
        r#"
struct Name { value: String }
struct Item { name: Name }
extend Item {
fun peek(&self) -> String {
    let v := self.name.value;
    v
}
}
fun main() {
let item := Item { name = Name { value = "n" } };
let _ := item.peek();
}
"#,
    );
    assert_eq!(from_reference.len(), 1, "{from_reference:#?}");
    assert_eq!(
        from_reference[0].kind,
        MoveViolationKind::MoveOutOfReference
    );
    assert!(
        from_reference[0].moved_span.is_none(),
        "{from_reference:#?}"
    );

    let from_view = move_violations_for_source(
        r#"
record Row { name: String }
fun main() {
    let rows: [Row] := [Row { name = "a".to_string() }];
    for (r in rows) { let n := r.name; }
}
"#,
    );
    assert!(
        from_view.iter().all(|violation| violation.kind
            != MoveViolationKind::BorrowedArrayElementMove
            || violation.moved_span.is_none()),
        "{from_view:#?}"
    );
    assert!(
        from_view
            .iter()
            .any(|violation| violation.kind == MoveViolationKind::BorrowedArrayElementMove),
        "{from_view:#?}"
    );

    let after_move = move_violations_for_source(
        r#"
fun consume(s: String) {}
fun main() {
    let s := "x".to_string();
    consume(s);
    consume(s);
}
"#,
    );
    assert_eq!(after_move.len(), 1, "{after_move:#?}");
    assert_eq!(after_move[0].kind, MoveViolationKind::UseAfterMove);
    let moved = after_move[0].moved_span.as_ref().expect("a real move site");
    assert!(
        moved.line > 0 && !moved.filename.starts_with("<place:"),
        "{moved:?}"
    );
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

// arch-verifies: ["arch.move-check.requirement-6"]
#[test]
fn incomplete_analysis_is_a_distinct_error_and_never_passes() {
    let mut report = None;
    let source = "fun keep<T>(value: T) -> T { value }\nfun main() {}\n";
    let unchecked = move_report_for_source_with(source, |graph| {
        make_generic_bodies_unanalyzable(graph);
        report = Some(check_graph(graph));
    });
    assert!(
        !unchecked.unchecked_generic_bodies.is_empty(),
        "the body must be unanalysable: {unchecked:#?}"
    );
    match report.expect("check_graph ran") {
        Err(MetelError::Internal {
            code: InternalErrorCode::I0011,
            message,
        }) => assert!(
            message.contains("could not analyze 1 generic body"),
            "{message}"
        ),
        other => panic!("expected I0011, got {other:?}"),
    }
}

// arch-verifies: ["arch.move-check.requirement-6"]
#[test]
fn analyzable_generic_bodies_pass_the_completeness_guard() {
    let mut result = None;
    move_report_for_source_with(
        "fun keep<T>(value: T) -> T { value }\nfun main() {}\n",
        |graph| result = Some(check_graph(graph)),
    );
    assert!(matches!(result, Some(Ok(()))), "{result:?}");
}

// arch-verifies: ["arch.move-check.requirement-4", "arch.move-check.requirement-5", "arch.move-check.requirement-10"]
#[test]
fn let_polymorphic_closures_are_analyzed_from_retained_bodies() {
    // Clearing the scheme environment makes reconstruction impossible, so a checked
    // body here can only have come from the retained abstract definition.
    let report = move_report_for_source_with(
        r#"
let pair_up := |a, b| { (b, a) };
let dup := |v| { let first := v; let second := v; first };
fun main() {}
"#,
        |graph| {
            for module in &mut graph.modules {
                module.scheme_env.clear();
            }
        },
    );
    assert_eq!(
        report.checked_abstract_generic_bodies.len(),
        2,
        "{report:#?}"
    );
    assert!(report.abstract_body_fallbacks.is_empty(), "{report:#?}");
    assert!(report.unchecked_generic_bodies.is_empty(), "{report:#?}");
    assert_eq!(report.violations.len(), 1, "{report:#?}");
    assert_eq!(report.violations[0].binding, "v", "{report:#?}");
}
