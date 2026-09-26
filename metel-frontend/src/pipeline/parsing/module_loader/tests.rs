use super::*;

#[test]
fn std_namespace_is_reserved_for_user_modules() {
    let path = Path::new("std.mtl");
    let err = validate_std_namespace(&["std".to_string()], path)
        .expect_err("a user module named `std` must be rejected");
    assert!(
        err.to_string()
            .contains("reserved for the standard library"),
        "got: {err}"
    );
    // Nested under std is also rejected.
    assert!(validate_std_namespace(&["std".to_string(), "io".to_string()], path).is_err());
}

#[test]
fn non_std_module_paths_are_allowed() {
    let path = Path::new("foo.mtl");
    assert!(validate_std_namespace(&[], path).is_ok());
    assert!(validate_std_namespace(&["foo".to_string()], path).is_ok());
    // `standard` is a different name, not the reserved `std` segment.
    assert!(validate_std_namespace(&["standard".to_string()], path).is_ok());
}

// arch-verifies: ["arch.parsing.requirement-2"]
#[test]
fn source_provider_overlay_supplies_in_memory_source() {
    // Proves the SourceProvider abstraction supports an in-memory overlay
    // (the LSP unsaved-buffer use case) without touching disk.
    struct Overlay;
    impl SourceProvider for Overlay {
        fn read(&self, module_path: &[String], _file: &Path) -> Result<String, MetelError> {
            assert_eq!(module_path, &["greeter".to_string()]);
            Ok("pub fun hi() {}".to_string())
        }
    }
    let provider = Overlay;
    let src = provider
        .read(&["greeter".to_string()], Path::new("ignored.mtl"))
        .unwrap();
    assert!(src.contains("fun hi"));
}

// arch-verifies: ["arch.parsing.requirement-2"]
#[test]
fn multi_file_source_provider_resolves_an_import() {
    // metel-core#1147: the virtual-root path could previously only ever
    // load its single root file -- any import failed, since
    // find_module_file's Path::exists check has no way to see an
    // in-memory sibling. Proves the fix: MultiFileSourceProvider's own
    // canonicalize override is now actually consulted during import
    // discovery, not bypassed by a hardcoded filesystem check.
    let provider = MultiFileSourceProvider::new(
        "editor.mtl",
        "import alpha::helper;\nfun main() -> i64 { helper() }\n",
    )
    .with_file("alpha.mtl", "public fun helper() -> i64 { 42 }\n");

    let graph = load_virtual_root_with("editor.mtl", &provider)
        .expect("the import should resolve through the provider, not the filesystem");
    let module_paths: Vec<&[String]> = graph
        .modules
        .iter()
        .map(|m| m.module_path.as_slice())
        .collect();
    assert!(
        module_paths.contains(&["alpha".to_string()].as_slice()),
        "alpha's module should have loaded: {module_paths:?}"
    );
}

// arch-verifies: ["arch.parsing.requirement-1"]
#[test]
fn modules_load_in_dependency_order() {
    let provider = MultiFileSourceProvider::new(
        "editor.mtl",
        "import b::from_b;\nfun main() -> i64 { from_b() }\n",
    )
    .with_file(
        "b.mtl",
        "import c::from_c;\npublic fun from_b() -> i64 { from_c() }\n",
    )
    .with_file("c.mtl", "public fun from_c() -> i64 { 1 }\n");
    let graph = load_virtual_root_with("editor.mtl", &provider).expect("graph loads");
    let position = |name: &str| {
        graph
            .modules
            .iter()
            .position(|m| m.module_path.last().is_some_and(|seg| seg == name))
            .unwrap_or_else(|| panic!("module `{name}` missing from the graph"))
    };
    assert!(
        position("c") < position("b"),
        "c must precede its importer b"
    );
    assert!(
        position("b") < graph.modules.len() - 1,
        "the root module is last, after everything it imports"
    );
}

// arch-verifies: ["arch.parsing.requirement-1"]
#[test]
fn a_cycle_is_reported_with_its_full_chain() {
    let provider =
        MultiFileSourceProvider::new("editor.mtl", "import a::fa;\nfun main() -> i64 { fa() }\n")
            .with_file("a.mtl", "import b::fb;\npublic fun fa() -> i64 { fb() }\n")
            .with_file("b.mtl", "import a::fa;\npublic fun fb() -> i64 { fa() }\n");
    let err = load_virtual_root_with("editor.mtl", &provider).expect_err("cycle must be rejected");
    let message = err.to_string();
    assert!(
        message.contains("circular module dependency")
            && message.contains("a.mtl -> b.mtl -> a.mtl"),
        "expected the traced cycle `a.mtl -> b.mtl -> a.mtl`, got: {message}"
    );
}

// arch-verifies: ["arch.parsing.requirement-2"]
#[test]
fn multi_file_source_provider_reports_a_missing_sibling() {
    // The other half of the same fix: a genuinely absent sibling must
    // still fail (not silently succeed by falling through to some
    // stale filesystem state), with the same diagnostic shape a real
    // missing file gets.
    let provider = MultiFileSourceProvider::new("editor.mtl", "import alpha::helper;\n");
    let err = load_virtual_root_with("editor.mtl", &provider)
        .expect_err("alpha.mtl was never registered with the provider");
    assert!(
        err.to_string().contains("cannot find module file"),
        "got: {err}"
    );
}

// arch-verifies: ["arch.parsing.requirement-2"]
#[test]
fn virtual_root_loads_without_an_on_disk_root() {
    let provider = InMemorySourceProvider::new("playground.mtl", "fun main() {}");
    let graph = load_virtual_root_with("playground.mtl", &provider)
        .expect("an in-memory root should load without filesystem access");

    assert!(graph.root.ends_with("playground.mtl"));
    assert!(
        graph
            .modules
            .iter()
            .any(|module| module.module_path.is_empty())
    );
}
