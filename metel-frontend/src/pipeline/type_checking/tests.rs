use super::*;

// arch-verifies: ["arch.resolution.requirement-3"]
#[test]
fn typed_ir_threads_member_ids_rather_than_rederiving_them() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/data/typed_ast.rs");
    let source = std::fs::read_to_string(path).expect("data/typed_ast.rs readable");
    assert!(
        source.contains("Option<FieldId>"),
        "typed field access/construction must carry a FieldId"
    );
    assert!(
        source.contains("Option<VariantId>"),
        "typed variant access/construction must carry a VariantId"
    );
}

// arch-verifies: ["arch.type-construction.requirement-6"]
#[test]
fn typed_ir_has_no_ascription_node() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/data/typed_ast.rs");
    let code = std::fs::read_to_string(&path).expect("data/typed_ast.rs readable");
    let code: String = code
        .lines()
        .filter(|line| !line.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        !code.contains("Ascribe"),
        "{} defines an ascription node; ascriptions must be erased during construction",
        path.display()
    );
}

/// The prelude's free-function schemes are derived from the embedded
/// std::core source (METEL-181); this asserts the derivation covers every
/// `native` declaration in core.mtl, so a new stdlib function can never
/// typecheck differently between the graph path (real module) and the
/// single-program path (prelude). Replaces the old hand-list parity test —
/// there is no longer a duplicated set to keep in sync.
#[test]
fn prelude_schemes_cover_embedded_core_natives() {
    let prelude = CorePrelude::default();
    let core_path = ["std".to_string(), "core".to_string()];
    let source = crate::stdlib::lookup(&core_path).expect("std::core is embedded");
    let program = crate::pipeline::parsing::parser::parse(source, "<embedded std::core>")
        .expect("core.mtl parses");

    let mut native_count = 0usize;
    for decl in &program.decls {
        if let Decl::Fun(fun) = decl {
            if fun.native.is_some() {
                native_count += 1;
                // Overloaded core natives (the assert pair) are dispatched
                // by SymbolId via the seeded overload table — they must
                // NOT appear in the name-keyed prelude.
                if overload::core_overload_table().contains_key(&fun.name) {
                    assert!(
                        !prelude.contains(&fun.name),
                        "overloaded std::core native `{}` must not be name-keyed in the prelude",
                        fun.name
                    );
                    assert!(
                        overload::core_native_symbol(fun).is_some(),
                        "overloaded std::core native `{}` must have a canonical SymbolId",
                        fun.name
                    );
                    continue;
                }
                assert!(
                    prelude.contains(&fun.name),
                    "prelude is missing a scheme for std::core native `{}`",
                    fun.name
                );
            }
        }
    }
    assert!(native_count > 0, "core.mtl should declare native functions");
}

// metel-core#1546: block-local ids are unique across the whole module graph. Each module's registry
// starts with a fresh allocator and absorbs its dependencies' definitions through `merge_from`;
// this runs the real pipeline over two modules that each declare a local type with the same name,
// so it also fails if `check_graph` stops threading one registry chain through the modules, which a
// test of `merge_from` alone cannot catch (and which no program output shows, because nothing
// observable depended on the overwritten entry).
// arch-verifies: ["arch.type-inference.requirement-2"]
#[test]
fn block_local_types_in_two_modules_keep_distinct_ids_through_check_graph() {
    use crate::pipeline::coherence;
    use crate::pipeline::name_resolution::name_resolver;
    use crate::pipeline::parsing::module_loader;
    use crate::pipeline::path_normalization;

    let dir = std::env::temp_dir().join(format!("metel_block_local_ids_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    std::fs::write(
        dir.join("helper.mtl"),
        "public fun from_helper() -> i64 {\n    record Handle { pad: i64, fd: i64 }\n    let h := Handle { pad = 100, fd = 3 };\n    h.fd\n}\n",
    )
    .expect("write helper");
    std::fs::write(
        dir.join("main.mtl"),
        "import helper::from_helper;\nfun main() {\n    record Handle { name: String, fd: i64 }\n    let h := Handle { name = \"n\", fd = 42 };\n    assert(from_helper() == 3);\n    assert(h.fd == 42);\n}\n",
    )
    .expect("write main");

    let result = (|| {
        let graph = module_loader::load_root(&dir.join("main.mtl"))?;
        let names = name_resolver::resolve(&graph)?;
        let normalized = path_normalization::normalize(graph, names)?;
        coherence::check(&normalized)?;
        check_graph(&normalized, &CorePrelude::default())
    })();
    let _ = std::fs::remove_dir_all(&dir);
    let typed = result.expect("the two-module program type-checks");

    let ids = typed.type_registry.block_local_ids_named("Handle");
    assert_eq!(
        ids.len(),
        2,
        "each module's local `Handle` needs its own id in the final registry, got {ids:?}"
    );
    let shapes: Vec<_> = ids
        .iter()
        .map(|id| {
            typed
                .type_registry
                .struct_fields_by_id(*id)
                .map(|fields| fields[0].name.clone())
        })
        .collect();
    assert!(
        shapes.contains(&Some("pad".to_string())) && shapes.contains(&Some("name".to_string())),
        "both modules' definitions must survive, got first fields {shapes:?}"
    );
}

// metel-core#1546 (ADR-0065 step 2) / LIMIT-NAME-RESOLUTION-002: an overload definition's id is a
// function of the program, not of what was compiled earlier in the process. Overload ids used to
// come from a process-global counter, so compiling the same program a second time numbered its
// overloads differently; this compiles program A, then an unrelated program B, then A again, and
// requires A's overload ids to come out identical both times.
// arch-verifies: ["arch.type-construction.requirement-10"]
#[test]
fn overload_ids_do_not_depend_on_what_was_compiled_earlier_in_the_process() {
    use crate::pipeline::coherence;
    use crate::pipeline::name_resolution::name_resolver;
    use crate::pipeline::parsing::module_loader;
    use crate::pipeline::path_normalization;
    use std::collections::BTreeMap;
    use std::sync::atomic::{AtomicU64, Ordering};

    static COUNTER: AtomicU64 = AtomicU64::new(0);

    // Every module's overload table, as module path -> function name -> its definitions' ids.
    // The embedded `std::core` ids are included: they must not move either.
    fn overload_ids(files: &[(&str, &str)]) -> BTreeMap<String, BTreeMap<String, Vec<String>>> {
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let dir =
            std::env::temp_dir().join(format!("metel_overload_ids_{}_{n}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("create temp dir");
        for (name, source) in files {
            std::fs::write(dir.join(name), source).expect("write module");
        }
        let result = (|| {
            let graph = module_loader::load_root(&dir.join("main.mtl"))?;
            let names = name_resolver::resolve(&graph)?;
            let normalized = path_normalization::normalize(graph, names)?;
            coherence::check(&normalized)?;
            check_graph(&normalized, &CorePrelude::default())
        })();
        let _ = std::fs::remove_dir_all(&dir);
        let typed = result.expect("the program type-checks");
        typed
            .modules
            .iter()
            .map(|module| {
                let tables = module
                    .overloads
                    .iter()
                    .map(|(name, entries)| {
                        let ids = entries
                            .iter()
                            .map(|e| format!("{:?}", e.symbol_id))
                            .collect();
                        (name.clone(), ids)
                    })
                    .collect();
                (module.module_path.join("::"), tables)
            })
            .collect()
    }

    let program_a = [
        (
            "helper.mtl",
            "public fun render(x: i64) -> i64 { x }\npublic fun render(x: String) -> i64 { 0 }\n",
        ),
        (
            "main.mtl",
            "import helper::render;\nfun describe(x: i64) -> i64 { x }\nfun describe(x: String) -> i64 { 1 }\nfun main() { assert(render(1) == 1); assert(describe(2) == 2); }\n",
        ),
    ];
    let program_b = [(
        "main.mtl",
        "fun other(x: i64) -> i64 { x }\nfun other(x: String) -> i64 { 2 }\nfun main() { assert(other(3) == 3); }\n",
    )];

    let first = overload_ids(&program_a);
    let _ = overload_ids(&program_b);
    let second = overload_ids(&program_a);
    assert_eq!(
        first, second,
        "the same program was numbered differently the second time it was compiled"
    );

    // And the ids really are there to compare: the program's own overloads, an imported group, and
    // the embedded core's `assert`, none of them empty.
    let main = &first[""];
    assert_eq!(main["describe"].len(), 2);
    assert_eq!(
        main["render"].len(),
        2,
        "the imported group keeps the defining module's ids"
    );
    assert_eq!(main["assert"].len(), 2);
    assert!(
        main["assert"]
            .iter()
            .all(|id| id.starts_with("CoreOverload(")),
        "{:?}",
        main["assert"]
    );
    assert!(
        main["describe"]
            .iter()
            .all(|id| id.starts_with("Overload(")),
        "{:?}",
        main["describe"]
    );
    assert_eq!(first["helper"]["render"], main["render"]);
}
