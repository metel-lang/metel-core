use crate::pipeline::name_resolution::name_resolver::resolve;
use crate::pipeline::parsing::module_loader::{LoadedModule, ModuleGraph};
use std::collections::HashMap;
use std::path::PathBuf;

/// Build a single-module graph (module path `[]`) from one source string.
fn single_module_graph(source: &str) -> ModuleGraph {
    let program = crate::pipeline::parsing::parser::parse(source, "test.mtl").expect("parse");
    ModuleGraph {
        root: PathBuf::from("test.mtl"),
        modules: vec![LoadedModule {
            module_path: vec![],
            file_path: PathBuf::from("test.mtl"),
            program,
        }],
        path_aliases: HashMap::new(),
    }
}

// arch-verifies: ["arch.name-resolution.requirement-3"]
#[test]
fn resolves_top_level_call_to_its_symbol_id() {
    let graph = single_module_graph(
        "fun helper() -> i64 { 1 }\n\
         fun main() { let x := 1; helper(); }",
    );
    let names = resolve(&graph).unwrap();
    let helper_id = names.symbols[&(vec![], "helper".to_string())];
    // Exactly one bare-Ident reference resolves to a Def: the `helper` call site.
    // The `let x` binding and the `x`/literal sites are locals or non-references.
    let resolved: Vec<_> = names.references.values().copied().collect();
    assert_eq!(
        resolved,
        vec![helper_id],
        "the only resolved reference should be the call to `helper`"
    );
}

// arch-verifies: ["arch.name-resolution.requirement-3"]
#[test]
fn local_binding_shadows_top_level_declaration() {
    let graph = single_module_graph(
        "fun foo() -> i64 { 1 }\n\
         fun main() { let foo := 2; foo; }",
    );
    let names = resolve(&graph).unwrap();
    let foo_id = names.symbols[&(vec![], "foo".to_string())];
    assert!(
        !names.references.values().any(|&id| id == foo_id),
        "a local `foo` must shadow the top-level `foo`, so no reference resolves to it"
    );
}

#[test]
fn overloaded_name_reference_does_not_resolve_to_a_stale_id() {
    // ADR-0042 regression: an overloaded name has no single unambiguous
    // declaration — `symbols[(module, "print")]` is a leftover artifact of the
    // initial interning pass (whichever overload happened to be interned last),
    // never a real identity anything registers a runtime value under. A bare
    // reference to it (here, used as a first-class value, not a call — call
    // sites go through the separate overload-selection path in
    // `typechecker::overload` entirely) must not resolve to that stale id.
    let graph = single_module_graph(
        "fun print(x: i64) {}\n\
         fun print(x: String) {}\n\
         fun main() { let f := print; }",
    );
    let names = resolve(&graph).unwrap();
    let stale_id = names.symbols[&(vec![], "print".to_string())];
    assert!(
        !names.references.values().any(|&id| id == stale_id),
        "a reference to an overloaded name must not resolve to the interning \
         pass's leftover single-declaration id"
    );
}
