use super::*;
use crate::pipeline::parsing::module_loader::{InMemorySourceProvider, LoadedModule, ModuleGraph};
use crate::tooling::analysis::{AnalysisOptions, analyze_graph, analyze_virtual_root_with};

fn analysis(source: &str) -> crate::tooling::analysis::Analysis {
    let provider = InMemorySourceProvider::new("editor.mtl", source);
    analyze_virtual_root_with("editor.mtl", &provider, AnalysisOptions::default())
        .expect("test source should analyze")
}

/// A multi-module analysis, built by hand -- the same approach
/// `identity`'s own cross-module fixtures use (metel-core#1046):
/// `analyze_graph` operates purely over an already-parsed `ModuleGraph`,
/// with no file discovery involved, so import/module-path query coverage
/// doesn't need a real (or virtual) filesystem at all.
fn multi_module_analysis(modules: &[(&str, &str)]) -> crate::tooling::analysis::Analysis {
    let graph = ModuleGraph {
        root: std::path::PathBuf::from(format!("{}.mtl", modules[0].0)),
        modules: modules
            .iter()
            .map(|(name, src)| LoadedModule {
                module_path: if *name == "root" {
                    vec![]
                } else {
                    vec![(*name).to_string()]
                },
                file_path: std::path::PathBuf::from(format!("{name}.mtl")),
                program: crate::pipeline::parsing::parser::parse(src, &format!("{name}.mtl"))
                    .expect("parses"),
            })
            .collect(),
        path_aliases: std::collections::HashMap::new(),
    };
    analyze_graph(graph, AnalysisOptions::default()).expect("multi-module source should analyze")
}

#[test]
fn expr_at_returns_the_innermost_typed_expression() {
    let source = "let value := 1 + 2;";
    let analysis = analysis(source);
    let offset = source.rfind('2').expect("literal is present");

    let expr = expr_at(&analysis.graph, "editor.mtl", offset).expect("typed expression");
    assert!(matches!(expr, TypedExpr::Literal(..)));
}

#[test]
fn definition_at_resolves_a_top_level_identifier_reference() {
    let source = "fun answer() -> i64 { 42 } fun main() -> i64 { answer() }";
    let analysis = analysis(source);
    let offset = source.rfind("answer").expect("call is present");

    let definition = definition_at(&analysis.names, "editor.mtl", offset)
        .expect("top-level reference should resolve");
    assert_eq!(definition.span.filename, "editor.mtl");
    assert!(definition.span.start < offset);
}

// ── identity-based queries (metel-core#1050) ────────────────────────────

#[test]
fn definition_resolves_a_local_binding_use_to_its_let() {
    let source = "fun main() -> i64 { let total := 41; total + 1 }";
    let analysis = analysis(source);
    let let_at = source.find("total").expect("binding");
    let use_at = source.rfind("total").expect("use");

    let site = analysis
        .definition_at("editor.mtl", use_at + 1)
        .expect("a use of a local resolves");
    assert!(
        matches!(site.binding(), Some(BindingId::Local(_))),
        "a local use resolves to a LocalId, not a SymbolId"
    );
    assert!(
        site.span.start <= let_at && let_at < site.span.end,
        "the definition span covers the `let total` binding site"
    );
    assert!(
        site.span.start < use_at,
        "the definition is upstream of the use"
    );
}

#[test]
fn definition_resolves_a_global_use_to_its_declaration() {
    let source = "fun helper() -> i64 { 1 } fun main() -> i64 { helper() }";
    let analysis = analysis(source);
    let decl_at = source.find("helper").expect("decl");
    let use_at = source.rfind("helper").expect("call");

    let site = analysis
        .definition_at("editor.mtl", use_at + 1)
        .expect("a use of a global resolves");
    assert!(matches!(site.binding(), Some(BindingId::Global(_))));
    assert!(
        site.span.start <= decl_at && decl_at < site.span.end,
        "the definition span covers the `fun helper` declaration"
    );
    assert!(site.span.start < use_at);
}

#[test]
fn references_finds_every_use_of_a_local_binding() {
    let source = "fun main() -> i64 { let n := 2; n + n + n }";
    let analysis = analysis(source);
    let use_at = source.find("n +").expect("first use");

    let refs = analysis.references_at("editor.mtl", use_at);
    assert_eq!(refs.len(), 3, "`n` is used three times");
    assert!(refs.iter().all(|s| s.filename == "editor.mtl"));
}

#[test]
fn identity_queries_return_none_off_a_name() {
    let source = "fun main() -> i64 { let x := 1;   x }";
    let analysis = analysis(source);
    let ws = source.find(";   ").expect("gap") + 2; // inside the run of spaces

    assert!(analysis.definition_at("editor.mtl", ws).is_none());
    assert!(analysis.references_at("editor.mtl", ws).is_empty());
}

// ── cross-module coverage (metel-core#1046's own "imports, module paths"
// acceptance-criteria bullet) ────────────────────────────────────────────

#[test]
fn definition_resolves_an_explicitly_imported_name_to_its_declaring_module() {
    let alpha_src = "public fun helper() -> i64 { 42 }";
    let root_src = "import alpha::helper;\nfun main() -> i64 { helper() }";
    let analysis = multi_module_analysis(&[("alpha", alpha_src), ("root", root_src)]);

    let decl_at = alpha_src.find("helper").expect("declaration");
    let use_at = root_src.rfind("helper").expect("call site");

    let site = analysis
        .definition_at("root.mtl", use_at + 1)
        .expect("an imported name's use resolves");
    assert!(
        matches!(site.binding(), Some(BindingId::Global(_))),
        "an imported free function resolves to a global SymbolId"
    );
    assert_eq!(
        site.span.filename, "alpha.mtl",
        "the definition site is in the declaring module, not the importer"
    );
    assert!(
        site.span.start <= decl_at && decl_at < site.span.end,
        "the definition span covers alpha's own `fun helper` declaration"
    );
}

#[test]
fn definition_resolves_a_module_path_segment_to_the_module_not_the_item() {
    let alpha_src = "public fun connect() -> i64 { 1 }";
    let root_src = "import alpha::*;\nfun main() -> i64 { alpha::connect() }";
    let analysis = multi_module_analysis(&[("alpha", alpha_src), ("root", root_src)]);

    let module_seg_at = root_src
        .rfind("alpha")
        .expect("module segment at the call site");
    let item_seg_at = root_src.rfind("connect").expect("item segment");

    let module_site = analysis
        .definition_at("root.mtl", module_seg_at + 1)
        .expect("the module segment resolves");
    assert!(
        matches!(module_site.target, DefinitionTarget::Module(_)),
        "the `alpha` segment resolves to the module itself, not a value binding"
    );
    assert_eq!(module_site.span.filename, "alpha.mtl");
    assert!(
        module_site.binding().is_none(),
        "a module target has no BindingId"
    );

    let item_site = analysis
        .definition_at("root.mtl", item_seg_at + 1)
        .expect("the item segment resolves (metel-core#1050)");
    assert!(
        matches!(item_site.binding(), Some(BindingId::Global(_))),
        "the `connect` segment resolves to alpha::connect's own declaration, not the module"
    );
    assert_eq!(item_site.span.filename, "alpha.mtl");
}
