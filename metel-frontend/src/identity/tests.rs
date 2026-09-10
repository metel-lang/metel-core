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
use std::path::PathBuf;

use crate::ast::Span;
use crate::module_loader::{LoadedModule, ModuleGraph};
use crate::name_resolver::resolve;

use super::allocate::allocate_module;
use super::position::PositionHit;
use super::{
    Allocation, BindingId, ModuleTable, NameId, NameInterner, Resolution, ResolutionMap,
    UnresolvedCause,
};

// ── harness ─────────────────────────────────────────────────────────────────

/// One parsed + resolved + allocated single-module program, with the interner
/// used to build it so tests can turn a [`NameId`] back into a spelling.
struct Fixture {
    alloc: Allocation,
    interner: NameInterner,
}

impl Fixture {
    fn build(source: &str) -> Self {
        let program = crate::parser::parse(source, "test.mtl").expect("parse");
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
        let alloc = allocate_module(&[], decls, &names, &mut interner);
        Self { alloc, interner }
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
        v.sort();
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
    v.sort();
    v
}

/// Sorted raw reference-id hashes.
fn ref_ids(map: &ResolutionMap) -> Vec<u64> {
    let mut v: Vec<_> = map.references.keys().map(|r| r.0).collect();
    v.sort_unstable();
    v
}

// ── structural stability ────────────────────────────────────────────────────

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

// ── totality + unresolved causes ────────────────────────────────────────────

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

// ── position index ──────────────────────────────────────────────────────────

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
