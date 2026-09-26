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
