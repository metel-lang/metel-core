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
