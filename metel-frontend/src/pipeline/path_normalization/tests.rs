//! metel-core#1052: a glob-imported name's module-qualified use gets a
//! real `SymbolId`, the same as an explicitly-imported one already did.

use crate::data::ast::Expr;
use crate::pipeline::parsing::module_loader;

/// Multi-file module resolution needs real files on disk (the loader
/// resolves an import to a sibling file path before reading it) — a
/// dedicated, per-call temp directory, cleaned up on drop.
struct TempProject {
    dir: std::path::PathBuf,
}

impl TempProject {
    fn new(sources: &[(&str, &str)]) -> Self {
        static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let n = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!(
            "metel-path-normalizer-test-{}-{n}",
            std::process::id(),
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create temp project dir");
        for (path, source) in sources {
            std::fs::write(dir.join(path), source).expect("write temp source file");
        }
        Self { dir }
    }
}

impl Drop for TempProject {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

fn resolved_path_symbol_id(
    root: &str,
    sources: &[(&str, &str)],
) -> Option<crate::identity::symbols::SymbolId> {
    let project = TempProject::new(sources);
    let graph = module_loader::load_root(project.dir.join(root)).expect("root loads");
    let names = crate::pipeline::name_resolution::name_resolver::resolve(&graph).expect("resolves");
    let normalized = super::normalize(graph, names).expect("normalizes");
    let root_module = normalized
        .modules()
        .iter()
        .find(|m| m.module_path.is_empty())
        .expect("root module");
    let crate::data::ast::Decl::Fun(main) = root_module
        .program
        .decls
        .iter()
        .find(|d| matches!(d, crate::data::ast::Decl::Fun(f) if f.name == "main"))
        .expect("fun main")
    else {
        unreachable!()
    };
    main.body.tail.as_ref().and_then(|tail| match &**tail {
        Expr::Call { callee, .. } => match &**callee {
            Expr::ResolvedPath { symbol_id, .. } => *symbol_id,
            _ => None,
        },
        _ => None,
    })
}

// arch-verifies: ["arch.path-normalization.requirement-1"]
#[test]
fn glob_imported_qualified_call_carries_a_symbol_id() {
    let id = resolved_path_symbol_id(
        "main.mtl",
        &[
            (
                "main.mtl",
                "import helper::*;\nfun main() -> i64 { helper::answer() }\n",
            ),
            ("helper.mtl", "public fun answer() -> i64 { 42 }\n"),
        ],
    );
    assert!(
        id.is_some(),
        "a glob-imported name's qualified use should carry the exporting \
         module's SymbolId, not resolve by name alone"
    );
}

// arch-verifies: ["arch.path-normalization.requirement-1"]
#[test]
fn explicitly_imported_qualified_call_carries_the_same_symbol_id() {
    // Regression guard: the explicit-import branch already worked before
    // this fix — confirm it still agrees with the glob-import branch for
    // the identical declaration.
    let explicit = resolved_path_symbol_id(
        "main.mtl",
        &[
            (
                "main.mtl",
                "import helper::answer;\nfun main() -> i64 { helper::answer() }\n",
            ),
            ("helper.mtl", "public fun answer() -> i64 { 42 }\n"),
        ],
    );
    let glob = resolved_path_symbol_id(
        "main.mtl",
        &[
            (
                "main.mtl",
                "import helper::*;\nfun main() -> i64 { helper::answer() }\n",
            ),
            ("helper.mtl", "public fun answer() -> i64 { 42 }\n"),
        ],
    );
    assert!(explicit.is_some(), "explicit import carries a SymbolId");
    assert_eq!(
        explicit, glob,
        "the same declaration resolves to the same SymbolId regardless \
         of whether it reached this module via an explicit or a glob import"
    );
}

// arch-verifies: ["arch.path-normalization.requirement-1"]
#[test]
fn self_qualified_call_carries_a_symbol_id() {
    // metel-core#1054: `self::name` (no explicit alias to read a SymbolId
    // off of, unlike an import) previously always normalized to `None`,
    // forcing the call to resolve by name alone.
    let id = resolved_path_symbol_id(
        "main.mtl",
        &[(
            "main.mtl",
            "fun answer() -> i64 { 42 }\nfun main() -> i64 { self::answer() }\n",
        )],
    );
    assert!(
        id.is_some(),
        "a self::-qualified same-module call should carry its own \
         declaration's SymbolId, not resolve by name alone"
    );
}
