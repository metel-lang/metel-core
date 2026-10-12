//! ADR-0063: under `--move-check`, every valid generic body must be analysed.
//!
//! Walks the whole integration corpus through the same pipeline `--move-check`
//! uses and asserts completeness, rather than observing that execution succeeded.

use std::fs;
use std::path::{Path, PathBuf};

use metel::pipeline::coherence;
use metel::pipeline::move_check;
use metel::pipeline::name_resolution::name_resolver;
use metel::pipeline::parsing::module_loader;
use metel::pipeline::path_normalization;
use metel::pipeline::type_checking;

fn collect_sources(path: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(path) else {
        return;
    };
    for entry in entries.flatten() {
        let child = entry.path();
        if child.is_dir() {
            let main = child.join("main.mtl");
            if main.is_file() {
                out.push(main);
            } else {
                collect_sources(&child, out);
            }
        } else if child.extension().is_some_and(|ext| ext == "mtl") {
            out.push(child);
        }
    }
}

/// Returns the number of abstract bodies analysed and the incompleteness findings.
fn analyze_fixture(root: &Path, fixture: &Path) -> (usize, Vec<String>) {
    let mut incomplete = Vec::new();
    let Ok(graph) = module_loader::load_root(fixture) else {
        return (0, incomplete);
    };
    let Ok(names) = name_resolver::resolve(&graph) else {
        return (0, incomplete);
    };
    let members = metel::identity::collect_members_for_graph(&graph, &names);
    let allocation = metel::identity::allocate_for_graph(&graph, &names);
    let Ok(normalized) = path_normalization::normalize(graph, names) else {
        return (0, incomplete);
    };
    if coherence::check(&normalized).is_err() {
        return (0, incomplete);
    }
    let Ok(checked) = type_checking::check_graph_with_report(
        &normalized,
        &type_checking::CorePrelude::default(),
        Some(metel::identity::FrozenIdentity {
            members: &members,
            binding_spans: &allocation.binding_spans,
        }),
    ) else {
        return (0, incomplete);
    };
    let report = move_check::collect_graph_violations(&checked.graph);
    let name = fixture
        .strip_prefix(root)
        .unwrap_or(fixture)
        .display()
        .to_string();
    for body in &report.unchecked_generic_bodies {
        incomplete.push(format!(
            "{name}: unchecked body at {}:{}:{}: {}",
            body.span.filename, body.span.line, body.span.col, body.reason
        ));
    }
    for fallback in &report.abstract_body_fallbacks {
        incomplete.push(format!(
            "{name}: abstract fallback at {}:{}:{} ({:?}): {}",
            fallback.span.filename,
            fallback.span.line,
            fallback.span.col,
            fallback.stage,
            fallback.reason
        ));
    }
    // The guard must agree with the report: with no unchecked body it never raises
    // `I0011` (a real violation is `T0019`, a different error).
    if report.unchecked_generic_bodies.is_empty()
        && let Err(error) = move_check::check_graph(&checked.graph)
    {
        assert!(
            !format!("{error:?}").contains("I0011"),
            "{name}: guard fired without an unchecked body: {error:?}"
        );
    }
    (report.checked_abstract_generic_bodies.len(), incomplete)
}

#[test]
fn every_generic_body_in_the_corpus_is_analyzed() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/integration/sources");
    let mut fixtures = Vec::new();
    collect_sources(&root, &mut fixtures);
    fixtures.sort();
    assert!(fixtures.len() > 1000, "corpus not found at {root:?}");

    let workers = std::thread::available_parallelism().map_or(1, usize::from);
    let next = std::sync::atomic::AtomicUsize::new(0);
    let results = std::sync::Mutex::new((0usize, Vec::<String>::new()));
    std::thread::scope(|scope| {
        for _ in 0..workers {
            // The type checker recurses deeply; give each worker generous stack.
            std::thread::Builder::new()
                .stack_size(256 * 1024 * 1024)
                .spawn_scoped(scope, || {
                    loop {
                        let index = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some(fixture) = fixtures.get(index) else {
                            break;
                        };
                        let (analysed, found) = analyze_fixture(&root, fixture);
                        let mut guard = results.lock().expect("results lock");
                        guard.0 += analysed;
                        guard.1.extend(found);
                    }
                })
                .expect("spawn worker");
        }
    });
    let (analysed, mut incomplete) = results.into_inner().expect("results lock");
    incomplete.sort();
    assert!(
        analysed > 500,
        "too few abstract bodies analysed: {analysed}"
    );
    assert!(
        incomplete.is_empty(),
        "move checking left {} generic bod{} unanalysed:\n{}",
        incomplete.len(),
        if incomplete.len() == 1 { "y" } else { "ies" },
        incomplete.join("\n")
    );
}
