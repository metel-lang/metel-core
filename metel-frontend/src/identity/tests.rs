//! Adversarial fixtures for the resolved-identity contract (metel-core#1048).
//!
//! The load-bearing properties, per ADR-0054's 2026-09-10 amendment:
//!
//! - identities are structural, so unrelated text edits do not renumber them;
//! - an edit to one body does not disturb identities in another;
//! - shadowing yields distinct identities;
//! - the reference table is total (every use has a `Resolution`);
//! - `ModuleId` interns per canonical path, alias-insensitively;
//! - `PositionIndex` is the only position-keyed structure and answers `None`
//!   off a name.

use std::collections::HashMap;

use crate::identity::symbols::Namespace;
use std::path::PathBuf;

use crate::data::ast::Span;
use crate::pipeline::name_resolution::name_resolver::resolve;
use crate::pipeline::parsing::module_loader::{LoadedModule, ModuleGraph};

use super::allocate::{
    GraphModuleNav, ModuleNav, allocate_for_graph, allocate_graph, allocate_module,
};
use super::position::PositionHit;
use super::{
    Allocation, BindingId, ModuleTable, NameId, NameInterner, Resolution, ResolutionMap,
    UnresolvedCause,
};

// ── harness ─────────────────────────────────────────────────────────────────

#[test]
fn inherited_default_locals_are_distinct_across_implementation_modules() {
    let source = "struct Box { value: i64 } fun body(value: i64) -> i64 { value }";
    let fixture = Fixture::build(source);
    let program = crate::pipeline::parsing::parser::parse(source, "test.mtl").expect("parse");
    let crate::data::ast::Decl::Fun(method) = &program.decls[1] else {
        panic!("function")
    };
    let source_method = fixture.names.symbols[&(vec![], Namespace::Value, "body".to_string())];
    let target = fixture.names.symbols[&(vec![], Namespace::Type, "Box".to_string())];
    let allocate = |module: &str| {
        super::allocate_inherited_body(
            source_method,
            super::InheritedMethodTarget::Nominal(target),
            &[module.to_string()],
            0,
            method,
            &fixture.alloc.binding_spans,
        )
    };
    let (left, left_spans) = allocate("left");
    let (right, right_spans) = allocate("right");
    let (again, again_spans) = allocate("left");
    assert_ne!(left, right);
    assert_eq!(left, again);
    assert_ne!(
        left_spans.get(&method.params[0].span),
        right_spans.get(&method.params[0].span)
    );
    assert_eq!(
        left_spans.get(&method.params[0].span),
        again_spans.get(&method.params[0].span)
    );
    let tail = method.body.tail.as_ref().expect("tail");
    assert_eq!(
        left_spans.get(tail.span()),
        left_spans.get(&method.params[0].span)
    );
    assert_eq!(
        right_spans.get(tail.span()),
        right_spans.get(&method.params[0].span)
    );
}

/// One parsed + resolved + allocated single-module program, with the interner
/// used to build it so tests can turn a [`NameId`] back into a spelling.
struct Fixture {
    alloc: Allocation,
    interner: NameInterner,
    names: std::rc::Rc<crate::pipeline::name_resolution::name_resolver::ResolvedNames>,
}

impl Fixture {
    fn build(source: &str) -> Self {
        let program = crate::pipeline::parsing::parser::parse(source, "test.mtl").expect("parse");
        let graph = ModuleGraph {
            root: PathBuf::from("test.mtl"),
            modules: vec![LoadedModule {
                module_path: vec![],
                file_path: PathBuf::from("test.mtl"),
                program,
            }],
            path_aliases: HashMap::new(),
        };
        let names = resolve(&graph).expect("resolve");
        let decls = &graph.modules[0].program.decls;
        let mut interner = NameInterner::new();
        let mut modules = ModuleTable::new();
        modules.intern(&[], Some(Span::new(0, 0, "test.mtl")));
        let nav = ModuleNav {
            table: &modules,
            aliases: &graph.path_aliases,
            scope: names.scopes.get(&Vec::new()),
            symbols: &names.symbols,
        };
        let alloc = allocate_module(&[], decls, &names, &mut interner, nav);
        Self {
            alloc,
            interner,
            names,
        }
    }

    fn map(&self) -> &ResolutionMap {
        &self.alloc.resolution
    }

    /// Local binding ids whose declared spelling is `spelling`.
    fn bindings_named(&self, spelling: &str) -> Vec<BindingId> {
        let mut v: Vec<_> = self
            .map()
            .definitions
            .iter()
            .filter(|(b, info)| {
                matches!(b, BindingId::Local(_))
                    && self.interner.name_str(info.name) == Some(spelling)
            })
            .map(|(b, _)| *b)
            .collect();
        v.sort_by_key(|b| format!("{b:?}"));
        v
    }

    /// The one local binding named `spelling`; panics if not exactly one.
    fn binding_named(&self, spelling: &str) -> BindingId {
        let v = self.bindings_named(spelling);
        assert_eq!(v.len(), 1, "expected exactly one `{spelling}` binding");
        v[0]
    }
}

/// Sorted local-binding ids.
fn local_ids(map: &ResolutionMap) -> Vec<BindingId> {
    let mut v: Vec<_> = map
        .definitions
        .keys()
        .copied()
        .filter(|b| matches!(b, BindingId::Local(_)))
        .collect();
    v.sort_by_key(|b| format!("{b:?}"));
    v
}

/// Sorted raw reference-id hashes.
fn ref_ids(map: &ResolutionMap) -> Vec<u64> {
    let mut v: Vec<_> = map.references.keys().map(|r| r.0).collect();
    v.sort_unstable();
    v
}

// ── structural stability ────────────────────────────────────────────────────

// arch-verifies: ["arch.resolution.requirement-2"]
#[test]
fn blank_lines_and_reformatting_change_no_identity() {
    let tight = "fun main() { let x := 1; let y := x; y; }";
    let loose = "fun main() {\n\n\n    let x := 1;\n\n    let y :=      x;\n\n\n    y;\n}\n";

    let a = Fixture::build(tight);
    let b = Fixture::build(loose);

    assert_eq!(
        local_ids(a.map()),
        local_ids(b.map()),
        "reformatting must not renumber local bindings"
    );
    assert_eq!(
        ref_ids(a.map()),
        ref_ids(b.map()),
        "reformatting must not renumber reference sites"
    );
}

// metel-core#1570: a binding inside a bare top-level statement gets a lexical identity, and
// shadowing across two such statements yields distinct ones.
// arch-verifies: ["arch.resolution.requirement-5"]
#[test]
fn bindings_in_top_level_statements_have_distinct_identities() {
    let fixture = Fixture::build(
        "var total := 0;\nfor (x in [1, 2]) { total += x; }\nfor (x in [3]) { total += x; }\n",
    );
    let xs = fixture.bindings_named("x");
    assert_eq!(2, xs.len(), "each top-level loop binds its own `x`");
    assert_ne!(xs[0], xs[1]);
    assert!(
        xs.iter().all(|b| matches!(b, BindingId::Local(_))),
        "a top-level statement's binding is a local, not a global"
    );
}

// arch-verifies: ["arch.resolution.requirement-2"]
#[test]
fn inserting_an_earlier_binding_does_not_renumber_a_later_one() {
    let before = Fixture::build("fun main() { let target := 1; target; }");
    let after = Fixture::build("fun main() { let inserted := 0; let target := 1; target; }");

    assert_eq!(
        before.binding_named("target"),
        after.binding_named("target"),
        "an earlier sibling `let` must not renumber `target`"
    );
}

// arch-verifies: ["arch.resolution.requirement-2"]
#[test]
fn editing_one_body_leaves_another_bodys_identities_untouched() {
    let v1 = Fixture::build("fun a() { let keep := 1; keep; }\nfun b() { let x := 1; }");
    let v2 = Fixture::build(
        "fun a() { let keep := 1; keep; }\nfun b() { let x := 1; let y := 2; y + x; }",
    );

    assert_eq!(
        v1.binding_named("keep"),
        v2.binding_named("keep"),
        "editing `b` must not move any identity in `a`"
    );
}

#[test]
fn allocation_is_order_independent_for_the_same_graph() {
    let src = "fun main() { let a := 1; let b := 2; a + b; }";
    let x = Fixture::build(src);
    let y = Fixture::build(src);
    assert_eq!(local_ids(x.map()), local_ids(y.map()));
    assert_eq!(ref_ids(x.map()), ref_ids(y.map()));
}

/// A local's `LocalId` is (owner `BindingId`, lexical path); its owner for a
/// top-level function's locals is `BindingId::Global(SymbolId)`. Before
/// metel-core#1048, `SymbolId` allocation depended on the order modules were
/// first visited, so a local's own resolved identity could silently change
/// with unrelated module load order -- something the test above never caught,
/// since it resolves one single-module fixture twice and so has no module
/// order to vary at all (metel-core#1049).
#[test]
fn local_binding_identity_is_independent_of_module_resolution_order() {
    fn build(order: [(&str, &str); 2]) -> Allocation {
        let graph = ModuleGraph {
            root: PathBuf::from("root.mtl"),
            modules: order
                .iter()
                .map(|(name, src)| LoadedModule {
                    module_path: vec![(*name).to_string()],
                    file_path: PathBuf::from(format!("{name}.mtl")),
                    program: crate::pipeline::parsing::parser::parse(src, &format!("{name}.mtl"))
                        .expect("parses"),
                })
                .collect(),
            path_aliases: HashMap::new(),
        };
        let names = resolve(&graph).expect("resolve");
        allocate_for_graph(&graph, &names)
    }

    let a_src = "fun f() -> i64 { let x := 1; x }";
    let b_src = "fun g() -> i64 { let y := 2; y }";

    let forward = build([("a", a_src), ("b", b_src)]);
    let reversed = build([("b", b_src), ("a", a_src)]);

    let x_at = a_src.rfind('x').expect("x use") + 1;
    let forward_hit = forward
        .positions
        .resolve("a.mtl", x_at)
        .expect("x has a position hit in the forward build");
    let reversed_hit = reversed
        .positions
        .resolve("a.mtl", x_at)
        .expect("x has a position hit in the reversed build");

    let PositionHit::Reference(forward_rid) = forward_hit else {
        panic!("expected a Reference hit for `x`, got {forward_hit:?}");
    };
    let PositionHit::Reference(reversed_rid) = reversed_hit else {
        panic!("expected a Reference hit for `x`, got {reversed_hit:?}");
    };

    assert_eq!(
        forward.resolution.references.get(&forward_rid),
        reversed.resolution.references.get(&reversed_rid),
        "`x`'s resolved binding must not change when module load order is reversed"
    );
}

// ── shadowing ───────────────────────────────────────────────────────────────

#[test]
fn shadowing_produces_distinct_local_ids() {
    let a = Fixture::build("fun main() { let v := 1; if (true) { let v := 2; v; } v; }");
    let vs = a.bindings_named("v");
    assert_eq!(vs.len(), 2, "two distinct `v` bindings");
    assert_ne!(vs[0], vs[1], "shadow and shadowed have distinct ids");
}

#[test]
fn inner_use_resolves_to_the_shadowing_binding() {
    let a = Fixture::build("fun main() { let v := 1; if (true) { let v := 2; v; } }");
    // Inner binding = the `v` with the larger declaration offset.
    let inner = a
        .map()
        .definitions
        .iter()
        .filter(|(b, info)| {
            matches!(b, BindingId::Local(_)) && a.interner.name_str(info.name) == Some("v")
        })
        .max_by_key(|(_, info)| info.span.start)
        .map(|(b, _)| *b)
        .expect("inner v");
    assert!(
        a.map()
            .references
            .values()
            .any(|r| *r == Resolution::Resolved(inner)),
        "the inner use should resolve to the inner binding"
    );
}

#[test]
fn shadowing_at_each_nested_binding_level_resolves_to_the_innermost_binding() {
    let a = Fixture::build(
        "fun main(x) { let initial := x; if (true) { let x := 1; let c := [] |x| { x; }; fun f(x) { x; } for (x in [x]) { x; } match (x) { x => x, }; x; } }",
    );
    let mut ids: Vec<_> = a
        .map()
        .definitions
        .iter()
        .filter_map(|(binding, info)| {
            (matches!(binding, BindingId::Local(_)) && a.interner.name_str(info.name) == Some("x"))
                .then_some(*binding)
        })
        .collect();
    assert_eq!(
        ids.len(),
        6,
        "parameter, let, closure, nested fn, loop, arm"
    );
    for id in &ids {
        assert!(
            a.map()
                .references
                .values()
                .any(|resolution| *resolution == Resolution::Resolved(*id)),
            "each nested x use resolves to its own binding"
        );
    }
    ids.sort_by_key(|b| format!("{b:?}"));
    ids.dedup();
    assert_eq!(ids.len(), 6);
}

// ── totality + unresolved causes ────────────────────────────────────────────

// arch-verifies: ["arch.resolution.requirement-1"]
#[test]
fn reference_table_is_total_and_unknown_names_are_explicit() {
    let a = Fixture::build("fun main() { nonesuch; }");
    assert_eq!(a.map().references.len(), 1, "the one use is recorded");
    match a.map().references.values().next().unwrap() {
        Resolution::Unresolved(u) => assert_eq!(u.cause, UnresolvedCause::NotInScope),
        Resolution::Resolved(_) => panic!("`nonesuch` must not resolve"),
    }
    assert!(a.map().has_unresolved());
}

// arch-verifies: ["arch.resolution.requirement-1"]
#[test]
fn a_body_with_only_bound_names_has_no_unresolved_references() {
    let a = Fixture::build("fun main() { let x := 1; x + x; }");
    assert!(!a.map().has_unresolved(), "all uses are lexically bound");
    let x = a.binding_named("x");
    assert_eq!(
        a.map().references_to(x).count(),
        2,
        "`x` is used twice and both resolve to it"
    );
}

// arch-verifies: ["arch.resolution.requirement-1"]
#[test]
fn a_use_of_a_global_declaration_is_classified_as_global() {
    let a = Fixture::build("fun helper() -> i64 { 1 }\nfun main() { helper(); }");
    let helper_sym = *a
        .names
        .symbols
        .get(&(vec![], Namespace::Value, "helper".to_string()))
        .expect("helper interned");

    // A lexical local shadowing `helper` would still win; here there is none,
    // so the call site is a resolved global, not `Unresolved`.
    let resolved: Vec<_> = a.map().references.values().collect();
    assert_eq!(resolved.len(), 1, "the `helper` call site");
    assert_eq!(
        resolved[0],
        &Resolution::Resolved(BindingId::Global(helper_sym)),
        "a use of a module-level declaration resolves to its SymbolId"
    );
    assert!(!a.map().has_unresolved());
}

#[test]
fn a_local_shadowing_a_global_keeps_the_use_local() {
    let a = Fixture::build("fun helper() -> i64 { 1 }\nfun main() { let helper := 2; helper; }");
    let local_helper = a.binding_named("helper");
    let resolved: Vec<_> = a.map().references.values().collect();
    assert_eq!(resolved.len(), 1);
    assert_eq!(
        resolved[0],
        &Resolution::Resolved(local_helper),
        "the lexical binding shadows the global; classify_globals must not override it"
    );
}

#[test]
fn aspect_default_method_body_gets_local_identities() {
    let a = Fixture::build("aspect Greet {\n  fun greeting(self) -> i64 { let n := 1; n }\n}");
    let n = a.binding_named("n");
    assert_eq!(a.map().references_to(n).count(), 1, "the `n` tail use");
    // `self` is a parameter of the default body.
    assert_eq!(a.bindings_named("self").len(), 1);
}

// ── lexical binding forms ──────────────────────────────────────────────────

#[test]
fn every_lexical_binding_form_is_structural_and_distinct() {
    let tight = r#"
struct Point { sx: i64, sy: i64 }
enum E { V { ex: i64, ey: i64 } }
fun main(param) {
    let let_value := param;
    var mut_value := let_value;
    let closure := [let_value] |closure_param| { closure_param + let_value };
    fun nested(nested_param) { nested(nested_param); }
    for (for_in_value in [let_value]) { for_in_value; }
    for (var for_value := 0; for_value < 1; for_value += 1) { for_value; }
    match (let_value) {
        (tuple_left, tuple_right) => tuple_left,
        Point { sx, sy } => sx,
        { record_left, record_right } => record_left,
        [array_head, ..array_rest] => array_head,
        E::V { ex, ey } => ex,
    };
}
"#;
    let loose = r#"
struct Point { sx: i64, sy: i64 }

enum E { V { ex: i64, ey: i64 } }

fun main( param ) {

 let let_value := param;
 var mut_value := let_value;
 let closure := [let_value] | closure_param | { closure_param + let_value };
 fun nested( nested_param ) { nested(nested_param); }
 for (for_in_value in [let_value]) { for_in_value; }
 for (var for_value := 0; for_value < 1; for_value += 1) { for_value; }
 match (let_value) {
  (tuple_left, tuple_right) => tuple_left,
  Point { sx, sy } => sx,
  { record_left, record_right } => record_left,
  [array_head, ..array_rest] => array_head,
  E::V { ex, ey } => ex,
 };
}
"#;

    let a = Fixture::build(tight);
    let b = Fixture::build(loose);
    let names = [
        "param",
        "let_value",
        "mut_value",
        "closure_param",
        "nested",
        "nested_param",
        "for_in_value",
        "for_value",
        "tuple_left",
        "tuple_right",
        "sx",
        "sy",
        "record_left",
        "record_right",
        "array_head",
        "array_rest",
        "ex",
        "ey",
    ];
    let a_ids: Vec<_> = names.iter().map(|name| a.binding_named(name)).collect();
    let b_ids: Vec<_> = names.iter().map(|name| b.binding_named(name)).collect();
    assert_eq!(a_ids, b_ids, "reformatting preserves every binding form");
    let mut distinct = a_ids.clone();
    distinct.sort_by_key(|b| format!("{b:?}"));
    distinct.dedup();
    assert_eq!(
        distinct.len(),
        names.len(),
        "distinct bindings have distinct ids"
    );

    let nested = a.binding_named("nested");
    assert!(
        a.map()
            .references
            .values()
            .any(|r| *r == Resolution::Resolved(nested)),
        "nested function recursion resolves to the function's own binding"
    );
}

#[test]
fn let_and_mut_rhs_do_not_see_their_own_bindings() {
    let a = Fixture::build("fun main() { let x := x; var y := y; }");
    assert_eq!(a.map().references.len(), 2);
    assert!(
        a.map().references.values().all(Resolution::is_unresolved),
        "a binding is introduced only after its initializer is walked"
    );
}

#[test]
fn nested_closure_capture_uses_resolve_to_the_enclosing_binding() {
    let a = Fixture::build(
        "fun main() { var x := 1; let f := [x, &x, &var x, x.clone()] var |p| { x + p }; }",
    );
    let x = a.binding_named("x");
    assert_eq!(
        a.map().references_to(x).count(),
        5,
        "four capture specifications and the closure-body use resolve to outer x"
    );
}

#[test]
fn impl_method_params_and_locals_are_allocated_under_method_symbols() {
    let tight = "struct Point { value: i64 } extend Point { fun bump(self, amount) { let total := amount; self; total; } }";
    let loose = "struct Point { value: i64 }\n\nextend Point {\n fun bump( self, amount ) {\n  let total := amount;\n  self;\n  total;\n }\n}";
    let a = Fixture::build(tight);
    let b = Fixture::build(loose);
    let self_binding = a.binding_named("self");
    let amount = a.binding_named("amount");
    let total = a.binding_named("total");
    assert_eq!(self_binding, b.binding_named("self"));
    assert_eq!(amount, b.binding_named("amount"));
    assert_eq!(total, b.binding_named("total"));
    assert_ne!(self_binding, amount);
    assert_ne!(amount, total);
    assert_eq!(a.map().references_to(self_binding).count(), 1);
    assert_eq!(a.map().references_to(amount).count(), 1);
    assert_eq!(a.map().references_to(total).count(), 1);
}

#[test]
fn impl_method_body_binder_does_not_index_literals_as_definitions() {
    let source = "struct Holder {} extend Holder { fun probe() { 123; } }";
    let fixture = Fixture::build(source);
    assert!(
        fixture
            .alloc
            .positions
            .resolve("test.mtl", source.find("123").unwrap())
            .is_none()
    );
}

#[test]
fn impl_method_variants_have_distinct_stable_body_and_local_identities() {
    let source = "struct Holder<T> { value: T } extend<T: Copy> Holder<T> { fun probe<U>(self, value: U) { let local := value; local; } } extend<T: !Copy> Holder<T> { fun probe<U>(self, value: U) { let local := value; local; } }";
    let original = Fixture::build(source);
    let edited = Fixture::build(&format!(
        "fun unrelated() {{ let other := 1; }}\n\n{source}"
    ));
    for name in ["probe", "self", "value", "local"] {
        let ids = original.bindings_named(name);
        assert_eq!(ids.len(), 2, "{name}: {ids:?}");
        assert_ne!(ids[0], ids[1]);
        assert_eq!(ids, edited.bindings_named(name), "{name}");
    }
    for id in original.bindings_named("local") {
        assert_eq!(original.map().references_to(id).count(), 1);
    }
}

#[test]
fn graph_allocation_is_module_order_independent_and_module_unique() {
    fn graph() -> ModuleGraph {
        ModuleGraph {
            root: PathBuf::from("root.mtl"),
            modules: vec![
                LoadedModule {
                    module_path: vec!["left".to_string()],
                    file_path: PathBuf::from("left.mtl"),
                    program: crate::pipeline::parsing::parser::parse(
                        "fun main(param) { let x := param; x; }",
                        "left.mtl",
                    )
                    .expect("left parses"),
                },
                LoadedModule {
                    module_path: vec!["right".to_string()],
                    file_path: PathBuf::from("right.mtl"),
                    program: crate::pipeline::parsing::parser::parse(
                        "fun main(param) { let x := param; x; }",
                        "right.mtl",
                    )
                    .expect("right parses"),
                },
            ],
            path_aliases: HashMap::new(),
        }
    }

    let graph = graph();
    let names = resolve(&graph).expect("resolve");
    let modules: Vec<_> = graph
        .modules
        .iter()
        .map(|module| (module.module_path.clone(), module.program.decls.as_slice()))
        .collect();
    let mut module_table = ModuleTable::new();
    for module in &graph.modules {
        module_table.intern(&module.module_path, None);
    }
    let mut forward_interner = NameInterner::new();
    let forward = allocate_graph(
        &modules,
        &names,
        &mut forward_interner,
        GraphModuleNav {
            table: &module_table,
            aliases: &graph.path_aliases,
        },
    );
    let mut reversed_interner = NameInterner::new();
    let mut reversed_modules = modules.clone();
    reversed_modules.reverse();
    let reversed = allocate_graph(
        &reversed_modules,
        &names,
        &mut reversed_interner,
        GraphModuleNav {
            table: &module_table,
            aliases: &graph.path_aliases,
        },
    );

    assert_eq!(
        local_ids(&forward.resolution),
        local_ids(&reversed.resolution)
    );
    assert_eq!(ref_ids(&forward.resolution), ref_ids(&reversed.resolution));
    assert_eq!(
        forward.resolution.definitions.len(),
        4,
        "two parameters and two local x bindings"
    );
    assert_eq!(
        forward.resolution.references.len(),
        4,
        "parameter and local uses from both modules"
    );
    assert_eq!(
        forward.positions.len(),
        8,
        "definitions and uses from both modules"
    );
}

// ── module identity ─────────────────────────────────────────────────────────

#[test]
fn module_id_interns_per_canonical_path_and_is_alias_insensitive() {
    let mut table = ModuleTable::new();
    let canonical = vec!["a".to_string(), "b".to_string()];
    let span = Span::new(0, 3, "a/b.mtl");

    let first = table.intern(&canonical, Some(span.clone()));
    // An alias `x::y -> a::b` is dereferenced before interning, so it lands on
    // the same id; a later call also fills in metadata missed the first time.
    let via_alias = table.intern(&canonical, None);
    assert_eq!(first, via_alias);

    let other = table.intern(&["c".to_string()], None);
    assert_ne!(first, other);
    assert_eq!(
        table.get(first).and_then(|i| i.decl_span.clone()),
        Some(span)
    );
}

#[test]
fn module_qualified_path_segment_resolves_to_its_module() {
    // `app` calls `net::connect()`; the `net` segment of that path is a
    // module-namespace position hit pointing at module `net` (metel-core#1070).
    let graph = ModuleGraph {
        root: PathBuf::from("app.mtl"),
        modules: vec![
            LoadedModule {
                module_path: vec!["net".to_string()],
                file_path: PathBuf::from("net.mtl"),
                program: crate::pipeline::parsing::parser::parse(
                    "fun connect() -> i64 { 0 }",
                    "net.mtl",
                )
                .expect("net parses"),
            },
            LoadedModule {
                module_path: vec![],
                file_path: PathBuf::from("app.mtl"),
                program: crate::pipeline::parsing::parser::parse(
                    "fun main() -> i64 { net::connect() }",
                    "app.mtl",
                )
                .expect("app parses"),
            },
        ],
        path_aliases: HashMap::new(),
    };
    let names = resolve(&graph).expect("resolve");
    let modules: Vec<_> = graph
        .modules
        .iter()
        .map(|m| (m.module_path.clone(), m.program.decls.as_slice()))
        .collect();

    let mut module_table = ModuleTable::new();
    for m in &graph.modules {
        module_table.intern(
            &m.module_path,
            Some(Span::new(0, 0, m.file_path.to_string_lossy())),
        );
    }
    let net_id = module_table
        .lookup(&["net".to_string()])
        .expect("net interned");

    let mut interner = NameInterner::new();
    let alloc = allocate_graph(
        &modules,
        &names,
        &mut interner,
        GraphModuleNav {
            table: &module_table,
            aliases: &graph.path_aliases,
        },
    );

    let app_src = "fun main() -> i64 { net::connect() }";
    let net_at = app_src.find("net").expect("net segment") + 1;
    let connect_at = app_src.rfind("connect").expect("connect segment") + 1;

    assert_eq!(
        alloc.positions.resolve("app.mtl", net_at),
        Some(PositionHit::ModuleSegment(net_id)),
        "the `net` segment jumps to module `net`",
    );
    // The item segment is not a module target...
    assert!(!matches!(
        alloc.positions.resolve("app.mtl", connect_at),
        Some(PositionHit::ModuleSegment(_))
    ));
    // ...it is a value reference to `net::connect` itself (metel-core#1050):
    // qualified-path go-to-definition needs this hit, not just the prefix's.
    let connect_sym = names.symbols[&(
        vec!["net".to_string()],
        Namespace::Value,
        "connect".to_string(),
    )];
    let PositionHit::Reference(rid) = alloc
        .positions
        .resolve("app.mtl", connect_at)
        .expect("connect has a position hit")
    else {
        panic!("expected a Reference hit for the `connect` item segment");
    };
    assert_eq!(
        alloc
            .resolution
            .references
            .get(&rid)
            .and_then(Resolution::binding),
        Some(BindingId::Global(connect_sym)),
        "the `connect` segment resolves to net::connect's own SymbolId"
    );
}

// arch-verifies: ["arch.resolution.requirement-4"]
#[test]
fn module_segment_hit_is_position_stable_under_reformatting() {
    // ADR-0054 / #1048: `ModuleId` interns by canonical path, so an unrelated
    // reformat leaves the module-segment target unchanged.
    fn alloc_for(app_src: &str) -> (super::PositionIndex, super::ModuleId) {
        let graph = ModuleGraph {
            root: PathBuf::from("app.mtl"),
            modules: vec![
                LoadedModule {
                    module_path: vec!["net".to_string()],
                    file_path: PathBuf::from("net.mtl"),
                    program: crate::pipeline::parsing::parser::parse(
                        "fun connect() -> i64 { 0 }",
                        "net.mtl",
                    )
                    .expect("net"),
                },
                LoadedModule {
                    module_path: vec![],
                    file_path: PathBuf::from("app.mtl"),
                    program: crate::pipeline::parsing::parser::parse(app_src, "app.mtl")
                        .expect("app"),
                },
            ],
            path_aliases: HashMap::new(),
        };
        let names = resolve(&graph).expect("resolve");
        let modules: Vec<_> = graph
            .modules
            .iter()
            .map(|m| (m.module_path.clone(), m.program.decls.as_slice()))
            .collect();
        let mut table = ModuleTable::new();
        for m in &graph.modules {
            table.intern(&m.module_path, Some(Span::new(0, 0, "x")));
        }
        let net_id = table.lookup(&["net".to_string()]).unwrap();
        let mut interner = NameInterner::new();
        let alloc = allocate_graph(
            &modules,
            &names,
            &mut interner,
            GraphModuleNav {
                table: &table,
                aliases: &graph.path_aliases,
            },
        );
        (alloc.positions, net_id)
    }

    let tight = "fun main() -> i64 { net::connect() }";
    let loose = "fun main() -> i64 {\n\n    net::connect()\n}\n";
    let (tight_pos, net_a) = alloc_for(tight);
    let (loose_pos, net_b) = alloc_for(loose);
    assert_eq!(net_a, net_b);
    assert_eq!(
        tight_pos.resolve("app.mtl", tight.find("net").unwrap() + 1),
        Some(PositionHit::ModuleSegment(net_a))
    );
    assert_eq!(
        loose_pos.resolve("app.mtl", loose.find("net").unwrap() + 1),
        Some(PositionHit::ModuleSegment(net_b))
    );
}

// ── position index ──────────────────────────────────────────────────────────

// arch-verifies: ["arch.resolution.requirement-4"]
#[test]
fn position_index_finds_a_use_and_misses_whitespace() {
    let src = "fun main() { let value := 1; value; }";
    let a = Fixture::build(src);

    let use_col = src.rfind("value").unwrap();
    match a.alloc.positions.resolve("test.mtl", use_col + 1) {
        Some(PositionHit::Reference(_)) => {}
        other => panic!("expected a reference hit, got {other:?}"),
    }

    let ws = src.rfind("; }").unwrap() + 1; // the space before `}`
    assert_eq!(a.alloc.positions.resolve("test.mtl", ws), None);
    assert_eq!(a.alloc.positions.resolve("other.mtl", use_col + 1), None);
}

// Keep an explicit reference so an unused-import lint never fires if the
// helpers above stop using `NameId` directly.
#[allow(dead_code)]
fn _name_id_is_used(_: NameId) {}

// arch-verifies: ["arch.resolution.requirement-4"]
#[test]
fn the_durable_resolution_map_is_keyed_by_identity_not_position() {
    // Compile-time assertion: if either table's key ever became a `Span` or
    // a `String`, these bindings would stop type-checking.
    use std::collections::HashMap;
    let map = ResolutionMap::default();
    let _definitions: &HashMap<BindingId, crate::identity::DefinitionInfo> = &map.definitions;
    let _references: &HashMap<crate::identity::RefId, Resolution> = &map.references;
}

// ── written generic-parameter names (ADR-0067, metel-core#1612) ─────────────

fn named_span(te: &crate::data::ast::TypeExpr) -> Span {
    let crate::data::ast::TypeExpr::Named(_, _, span) = te else {
        panic!("not a named type: {te:?}")
    };
    span.0.clone()
}

fn parsed_fun(source: &str, index: usize) -> crate::data::ast::FunDecl {
    let program = crate::pipeline::parsing::parser::parse(source, "test.mtl").expect("parse");
    let crate::data::ast::Decl::Fun(fun) = &program.decls[index] else {
        panic!("function at {index}")
    };
    fun.clone()
}

#[test]
fn a_written_generic_parameter_resolves_to_one_identity_across_its_signature() {
    let source = "fun id<T>(x: T) -> T { let y: T := x; y }";
    let fixture = Fixture::build(source);
    let fun = parsed_fun(source, 0);
    let spans = &fixture.alloc.binding_spans;
    let param = spans.type_param_at(&named_span(fun.params[0].type_ann.as_ref().unwrap()));
    let ret = spans.type_param_at(&named_span(fun.return_type.as_ref().unwrap()));
    assert!(param.is_some());
    assert_eq!(param, ret);
    let crate::data::ast::Decl::Let(let_decl) = &fun.body.stmts[0] else {
        panic!("let")
    };
    assert_eq!(
        spans.type_param_at(&named_span(let_decl.type_ann.as_ref().unwrap())),
        param
    );
}

#[test]
fn same_spelled_parameters_of_different_functions_have_distinct_identities() {
    let source = "fun a<T>(x: T) -> T { x } fun b<T>(x: T) -> T { x }";
    let fixture = Fixture::build(source);
    let spans = &fixture.alloc.binding_spans;
    let of = |index| {
        let fun = parsed_fun(source, index);
        spans
            .type_param_at(&named_span(fun.params[0].type_ann.as_ref().unwrap()))
            .expect("T resolves")
    };
    assert_ne!(of(0), of(1));
}

#[test]
fn a_parameters_identity_survives_reformatting() {
    let compact = Fixture::build("fun id<T>(x: T) -> T { x }");
    let spaced = Fixture::build("\n\n// note\nfun   id<T>(\n    x: T,\n) -> T {\n    x\n}\n");
    let id = |fixture: &Fixture, source: &str| {
        let fun = parsed_fun(source, 0);
        fixture
            .alloc
            .binding_spans
            .type_param_at(&named_span(fun.params[0].type_ann.as_ref().unwrap()))
            .expect("T resolves")
    };
    assert_eq!(
        id(&compact, "fun id<T>(x: T) -> T { x }"),
        id(
            &spaced,
            "\n\n// note\nfun   id<T>(\n    x: T,\n) -> T {\n    x\n}\n"
        )
    );
}

#[test]
fn a_name_that_is_not_a_generic_parameter_has_no_parameter_identity() {
    let source = "struct Box { value: i64 } fun f<T>(x: T, n: i64, b: Box) -> i64 { n }";
    let fixture = Fixture::build(source);
    let fun = parsed_fun(source, 1);
    let spans = &fixture.alloc.binding_spans;
    assert!(
        spans
            .type_param_at(&named_span(fun.params[0].type_ann.as_ref().unwrap()))
            .is_some()
    );
    assert!(
        spans
            .type_param_at(&named_span(fun.params[1].type_ann.as_ref().unwrap()))
            .is_none()
    );
    assert!(
        spans
            .type_param_at(&named_span(fun.params[2].type_ann.as_ref().unwrap()))
            .is_none()
    );
}

#[test]
fn a_method_sees_its_impls_parameters_and_its_own() {
    let source =
        "struct W<T> { v: T } extend<T> W<T> { fun map<U>(self, f: |T| -> U) -> U { f(self.v) } }";
    let program = crate::pipeline::parsing::parser::parse(source, "test.mtl").expect("parse");
    let fixture = Fixture::build(source);
    let crate::data::ast::Decl::Impl(impl_block) = &program.decls[1] else {
        panic!("impl")
    };
    let method = &impl_block.methods[0];
    let crate::data::ast::TypeExpr::Fun {
        params,
        return_type,
        ..
    } = method.params[1].type_ann.as_ref().unwrap()
    else {
        panic!("fn type")
    };
    let spans = &fixture.alloc.binding_spans;
    let t = spans
        .type_param_at(&named_span(&params[0]))
        .expect("impl T");
    let u = spans
        .type_param_at(&named_span(return_type.as_ref().unwrap()))
        .expect("method U");
    assert_ne!(t, u);
    assert_eq!(
        spans.type_param_at(&named_span(method.return_type.as_ref().unwrap())),
        Some(u)
    );
}

#[test]
fn a_nested_function_has_its_own_parameter_identities() {
    let source = "fun outer<T>(x: T) -> T { fun inner<T>(y: T) -> T { y } x }";
    let fixture = Fixture::build(source);
    let outer = parsed_fun(source, 0);
    let crate::data::ast::Decl::Fun(inner) = &outer.body.stmts[0] else {
        panic!("nested fun")
    };
    let spans = &fixture.alloc.binding_spans;
    let outer_t = spans
        .type_param_at(&named_span(outer.params[0].type_ann.as_ref().unwrap()))
        .expect("outer T");
    let inner_t = spans
        .type_param_at(&named_span(inner.params[0].type_ann.as_ref().unwrap()))
        .expect("inner T");
    assert_ne!(outer_t, inner_t);
    assert_eq!(spans.declared_type_params(&inner.span).len(), 1);
    assert_eq!(spans.declared_type_params(&inner.span)[0].1, inner_t);
}

#[test]
fn impl_aspect_parameter_types_are_declared_as_synthesised_parameters() {
    let source = "aspect A {} fun both(a: extends A, b: extends A) {}";
    let fixture = Fixture::build(source);
    let fun = parsed_fun(source, 1);
    let spans = &fixture.alloc.binding_spans;
    let declared = spans.declared_type_params(&fun.span);
    let names: Vec<&str> = declared.iter().map(|(name, _)| name.as_str()).collect();
    assert_eq!(names, ["_ImplT0", "_ImplT1"]);
    assert_ne!(declared[0].1, declared[1].1);
}

#[test]
fn a_struct_and_an_enum_declare_their_generic_parameters_in_order() {
    let source = "struct Pair<A, B> { first: A, second: B } enum Either<L, R> { Left { value: L }, Right { value: R } }";
    let fixture = Fixture::build(source);
    let program = crate::pipeline::parsing::parser::parse(source, "test.mtl").expect("parse");
    let spans = &fixture.alloc.binding_spans;
    let symbol = |name: &str| fixture.names.symbols[&(vec![], Namespace::Type, name.to_string())];
    let pair = spans.type_decl_params(symbol("Pair"));
    let either = spans.type_decl_params(symbol("Either"));
    assert_eq!(
        pair.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(),
        ["A", "B"]
    );
    assert_eq!(
        either.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(),
        ["L", "R"]
    );
    assert_ne!(pair[0].1, either[0].1);
    let crate::data::ast::Decl::Struct(decl) = &program.decls[0] else {
        panic!("struct")
    };
    assert_eq!(
        spans.type_param_at(&named_span(&decl.fields[1].type_ann)),
        Some(pair[1].1)
    );
}
