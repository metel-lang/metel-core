//! Fixture discovery.
//!
//! `run_discovered_fixture` runs a single fixture at a path relative to the
//! crate root (the generated `register_integration_test!` calls pass these).
//!
//! `discover_all` / `manifest_text` re-derive the full fixture list by walking
//! `tests/integration/sources/`. They exist so that:
//!
//! * `build.rs` can generate one `#[test]` per fixture **from a checked-in
//!   manifest** (`tests/integration/fixtures.manifest`) rather than by watching
//!   the source directories — editing a fixture's contents then rebuilds
//!   nothing (metel-core#873);
//! * a normal test (`fixtures_manifest_is_current`) fails, with the fix command,
//!   whenever a fixture is added / removed / renamed and the manifest wasn't
//!   regenerated — so discovery stays automatic in practice.

use std::path::{Path, PathBuf};

use super::fixture::resolve_fixture_config;
use super::runners::run_fixture;

/// Suites and their roots, relative to `CARGO_MANIFEST_DIR`.
pub const SUITES: &[(&str, &str)] = &[
    ("parsing", "tests/integration/sources/parsing"),
    ("typechecking", "tests/integration/sources/typechecking"),
    ("evaluator", "tests/integration/sources/evaluator"),
    ("module_loading", "tests/integration/sources/module_loading"),
    (
        "module_semantics",
        "tests/integration/sources/module_semantics",
    ),
];

/// One discovered fixture: the suite it belongs to, its sanitized test-function
/// name, and its path relative to the crate root (forward-slashed).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct DiscoveredFixture {
    pub suite: &'static str,
    pub test_name: String,
    pub relative_path: String,
}

pub fn run_discovered_fixture(suite: &str, relative_path: &Path) {
    // metel-core#960 / #965: the tree-walk evaluator recurses per AST node, and
    // in the debug profile `eval_expr` — a `match` over every `TypedExpr`
    // variant — has a ~60 KB frame (the compiler reserves every arm's locals at
    // once). A fixture with even a ~10-deep recursive function (`count_down(10)`)
    // then overflows libtest's ~2 MiB worker-thread stack and aborts the whole
    // binary; `--release` packs the frame small enough to fit, which is why CI
    // stays green. Splitting `eval_expr` into per-arm helpers shrinks the debug
    // frame but measured a ~20% eval-throughput regression in release (#965), so
    // the fix is simply to give the fixture worker the same 8 MiB the shipped
    // `metel` binary's main thread gets — a modest cushion, no runtime cost.
    let suite = suite.to_string();
    let relative_path = relative_path.to_path_buf();
    let worker = std::thread::Builder::new()
        .name("fixture".to_string())
        .stack_size(8 * 1024 * 1024)
        .spawn(move || {
            let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(&relative_path);
            let config = resolve_fixture_config(&suite, &path);
            run_fixture(&path, &config);
        })
        .expect("spawn fixture worker thread");
    if let Err(payload) = worker.join() {
        std::panic::resume_unwind(payload);
    }
}

/// Every fixture under every suite root, sorted by `(suite order, path)`.
#[must_use]
fn discover_all() -> Vec<DiscoveredFixture> {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut out = Vec::new();
    for (suite, rel_root) in SUITES {
        let root = manifest_dir.join(rel_root);
        if !root.exists() {
            continue;
        }
        let mut fixtures = Vec::new();
        discover_dir(&root, &mut fixtures);
        fixtures.sort();
        for fixture in fixtures {
            let test_name = build_test_name(suite, &root, &fixture);
            let relative = fixture
                .strip_prefix(&manifest_dir)
                .expect("fixture path should be under manifest dir");
            out.push(DiscoveredFixture {
                suite,
                test_name,
                relative_path: relative.to_string_lossy().replace('\\', "/"),
            });
        }
    }
    out
}

/// The canonical text of `tests/integration/fixtures.manifest`: one
/// tab-separated `suite<TAB>test_name<TAB>relative_path` line per fixture,
/// trailing newline. `build.rs` parses this; the currency test compares it.
#[must_use]
pub fn manifest_text() -> String {
    let mut s = String::from(
        "# @generated — run `UPDATE_FIXTURES=1 cargo test -p metel --test integration fixtures_manifest_is_current`\n",
    );
    for f in discover_all() {
        s.push_str(f.suite);
        s.push('\t');
        s.push_str(&f.test_name);
        s.push('\t');
        s.push_str(&f.relative_path);
        s.push('\n');
    }
    s
}

/// Path to the checked-in manifest.
#[must_use]
pub fn manifest_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/integration/fixtures.manifest")
}

// ── walk ─────────────────────────────────────────────────────────────────────

fn discover_dir(dir: &Path, fixtures: &mut Vec<PathBuf>) {
    if is_multi_module_fixture(dir) {
        fixtures.push(dir.to_path_buf());
        return;
    }
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", dir.display()))
        .map(|entry| {
            entry.unwrap_or_else(|e| panic!("failed to read dir entry in {}: {e}", dir.display()))
        })
        .collect();
    entries.sort_by_key(std::fs::DirEntry::path);
    for entry in entries {
        let path = entry.path();
        if path.is_dir() {
            discover_dir(&path, fixtures);
            continue;
        }
        if path.extension().and_then(|ext| ext.to_str()) == Some("mtl") {
            fixtures.push(path);
        }
    }
}

fn is_multi_module_fixture(dir: &Path) -> bool {
    dir.join("main.mtl").is_file()
}

fn build_test_name(suite: &str, root: &Path, fixture: &Path) -> String {
    let relative = fixture
        .strip_prefix(root)
        .expect("fixture should live under suite root");
    let mut parts = vec![suite.to_string()];
    if fixture.is_dir() {
        parts.extend(
            relative
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned()),
        );
    } else {
        if let Some(parent) = relative.parent() {
            parts.extend(
                parent
                    .components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned()),
            );
        }
        parts.push(
            relative
                .file_stem()
                .expect("fixture file should have stem")
                .to_string_lossy()
                .into_owned(),
        );
    }
    sanitize_ident(&parts.join("__"))
}

fn sanitize_ident(raw: &str) -> String {
    let mut out = String::new();
    for ch in raw.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push('_');
        }
    }
    if out.is_empty() || out.starts_with(|ch: char| ch.is_ascii_digit()) {
        out.insert_str(0, "case_");
    }
    out
}
