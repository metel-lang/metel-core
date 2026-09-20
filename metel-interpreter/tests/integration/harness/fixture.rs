use std::fs;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RunnerKind {
    Parse,
    Typecheck,
    Evaluate,
    LoadProgram,
    LoadGraph,
    FullPipeline,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CorePreludeMode {
    Empty,
    Default,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExpectStatus {
    Success,
    ParseError,
    TypecheckError,
    RuntimeError,
    LoadError,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expectation {
    pub status: ExpectStatus,
    pub code: Option<String>,
    pub contains: Option<String>,
    pub line: Option<usize>,
    pub col: Option<usize>,
    /// Expected warning fragments, when this fixture exercises a warning.
    /// Existing success fixtures do not implicitly assert that stderr is empty.
    pub warnings: Option<Vec<String>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixtureConfig {
    pub runner: RunnerKind,
    pub prelude: CorePreludeMode,
    pub options: FixtureOptions,
    pub expect: Expectation,
    pub program: ProgramChecks,
    pub graph: GraphChecks,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FixtureOptions {
    pub move_check: bool,
    /// RFC-section citations this fixture demonstrates, e.g. `rfc-0061§7.2`.
    /// See ADR-0049 for the grammar and the coverage checker that will
    /// eventually consume this. Purely informational to the harness today --
    /// parsed and validated, not yet read by anything else.
    pub rfc: Vec<String>,
    /// Spec-block citations this fixture demonstrates, e.g.
    /// `spec.declarations.structs.instantiation-and-field-access.legality-1`.
    /// See ADR-0050 for the grammar and the coverage checker that will
    /// eventually consume this -- same "parsed and validated, not yet read
    /// by anything else" status `rfc` had before `rfc.py` existed. A
    /// citation migrating from `rfc =` to `spec =` (ADR-0050 §7) retires the
    /// `rfc =` entry it supersedes rather than accumulating both; a fixture
    /// mid-migration can carry both fields at once for its still-unmigrated
    /// citations.
    pub spec: Vec<String>,
    /// When set, `run_fixture` reports this fixture skipped instead of
    /// running it -- for a fixture written ahead of the feature it exercises
    /// (checked in against an accepted RFC whose implementation issue hasn't
    /// landed yet). The `.mtl` source is real and checked in, but is not
    /// attempted: it may use syntax the parser doesn't accept yet. Give the
    /// reason a tracking issue, e.g. `skip = "metel-core#926 -- capture-list
    /// syntax not implemented"`, and drop this key (plus add the real
    /// `spec =` citation, if not already present) once the feature lands. A
    /// skipped fixture does not count toward `rfc.py`'s spec-block fixture
    /// coverage.
    pub skip: Option<String>,
    /// Optional human-readable label for this fixture, shown instead of the
    /// `.mtl` filename by the rendered spec's inline fixture viewer
    /// (metel-core#944 / #974). Purely presentational: the harness parses and
    /// stores it but does not act on it, and it has no effect on `spec =`
    /// coverage. `rfc.py` reads it when regenerating the Formal-rules blocks.
    /// An empty / whitespace-only value is treated as unset.
    pub spec_title: Option<String>,
    /// Architecture Spec claim citations this fixture verifies, e.g.
    /// `arch_verifies = ["arch.evaluation.requirement-3"]`. Parallel to
    /// `spec =`, but for `architecture/spec/*.md`'s `arch-*` requirements
    /// (metel-core#1175) rather than the Language Spec's Formal-rules
    /// blocks. `metel-docs/architecture/tools/generate_architecture_evidence.py`
    /// reads this key straight from the `.toml` source (not through this
    /// harness) to render each requirement's `verified by` evidence link.
    pub arch_verifies: Vec<String>,
    /// Error-code citations this fixture demonstrates, e.g. `error =
    /// ["T0003"]` -- a fixture whose own `expect.code` produces that code.
    /// Deliberately a separate key from `spec =`, not a widened form of it:
    /// "evidence for a language rule" and "evidence for a diagnostic" are
    /// different axes even when the same fixture serves both (metel-core#981).
    /// Purely informational to the harness today, same "parsed and
    /// validated, not yet read by anything else" status `rfc =` and `spec =`
    /// had before `rfc.py` read them -- `rfc.py` reads this one to render
    /// `error-codes.md`'s own inline fixture viewers.
    pub error: Vec<String>,
}

#[derive(Default)]
struct PartialConfig {
    runner: Option<RunnerKind>,
    prelude: Option<CorePreludeMode>,
    move_check: Option<bool>,
    rfc: Option<Vec<String>>,
    spec: Option<Vec<String>>,
    skip: Option<String>,
    spec_title: Option<String>,
    arch_verifies: Option<Vec<String>>,
    error: Option<Vec<String>>,
    status: Option<ExpectStatus>,
    code: Option<String>,
    contains: Option<String>,
    line: Option<usize>,
    col: Option<usize>,
    warnings: Option<Vec<String>>,
    program_imports: Option<usize>,
    program_decls: Option<usize>,
    graph_module_count: Option<usize>,
    graph_has_module_paths: Option<Vec<Vec<String>>>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ProgramChecks {
    pub imports: Option<usize>,
    pub decls: Option<usize>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GraphChecks {
    pub module_count: Option<usize>,
    pub has_module_paths: Vec<Vec<String>>,
}

pub fn resolve_fixture_config(suite: &str, fixture_path: &Path) -> FixtureConfig {
    let defaults = suite_defaults(suite);
    let mut partial = PartialConfig::default();

    if let Some(sidecar) = sidecar_path(fixture_path) {
        partial = parse_sidecar(&sidecar);
    } else if let Some(legacy) = parse_legacy_expectation(suite, fixture_path) {
        partial = legacy;
    }

    merge_config(defaults, partial)
}

pub fn main_source_path(fixture_path: &Path) -> PathBuf {
    if fixture_path.is_dir() {
        fixture_path.join("main.mtl")
    } else {
        fixture_path.to_path_buf()
    }
}

fn suite_defaults(suite: &str) -> FixtureConfig {
    match suite {
        "parsing" => FixtureConfig {
            runner: RunnerKind::Parse,
            prelude: CorePreludeMode::Empty,
            options: FixtureOptions::default(),
            expect: Expectation::success(),
            program: ProgramChecks::default(),
            graph: GraphChecks::default(),
        },
        "typechecking" => FixtureConfig {
            runner: RunnerKind::Typecheck,
            prelude: CorePreludeMode::Default,
            options: FixtureOptions::default(),
            expect: Expectation::success(),
            program: ProgramChecks::default(),
            graph: GraphChecks::default(),
        },
        "evaluator" => FixtureConfig {
            runner: RunnerKind::Evaluate,
            prelude: CorePreludeMode::Default,
            options: FixtureOptions::default(),
            expect: Expectation::success(),
            program: ProgramChecks::default(),
            graph: GraphChecks::default(),
        },
        "module_loading" => FixtureConfig {
            runner: RunnerKind::FullPipeline,
            prelude: CorePreludeMode::Empty,
            options: FixtureOptions::default(),
            expect: Expectation::success(),
            program: ProgramChecks::default(),
            graph: GraphChecks::default(),
        },
        "module_semantics" => FixtureConfig {
            runner: RunnerKind::FullPipeline,
            prelude: CorePreludeMode::Empty,
            options: FixtureOptions::default(),
            expect: Expectation::success(),
            program: ProgramChecks::default(),
            graph: GraphChecks::default(),
        },
        other => panic!("unknown integration suite `{other}`"),
    }
}

impl Expectation {
    fn success() -> Self {
        Self {
            status: ExpectStatus::Success,
            code: None,
            contains: None,
            line: None,
            col: None,
            warnings: None,
        }
    }
}

fn merge_config(defaults: FixtureConfig, partial: PartialConfig) -> FixtureConfig {
    FixtureConfig {
        runner: partial.runner.unwrap_or(defaults.runner),
        prelude: partial.prelude.unwrap_or(defaults.prelude),
        options: FixtureOptions {
            move_check: partial.move_check.unwrap_or(defaults.options.move_check),
            rfc: partial.rfc.unwrap_or(defaults.options.rfc),
            spec: partial.spec.unwrap_or(defaults.options.spec),
            skip: partial.skip.or(defaults.options.skip),
            spec_title: partial.spec_title.or(defaults.options.spec_title),
            arch_verifies: partial
                .arch_verifies
                .unwrap_or(defaults.options.arch_verifies),
            error: partial.error.unwrap_or(defaults.options.error),
        },
        expect: Expectation {
            status: partial.status.unwrap_or(defaults.expect.status),
            code: partial.code.or(defaults.expect.code),
            contains: partial.contains.or(defaults.expect.contains),
            line: partial.line.or(defaults.expect.line),
            col: partial.col.or(defaults.expect.col),
            warnings: partial.warnings.or(defaults.expect.warnings),
        },
        program: ProgramChecks {
            imports: partial.program_imports.or(defaults.program.imports),
            decls: partial.program_decls.or(defaults.program.decls),
        },
        graph: GraphChecks {
            module_count: partial.graph_module_count.or(defaults.graph.module_count),
            has_module_paths: partial
                .graph_has_module_paths
                .unwrap_or(defaults.graph.has_module_paths),
        },
    }
}

fn sidecar_path(fixture_path: &Path) -> Option<PathBuf> {
    if fixture_path.is_dir() {
        let sidecar = fixture_path.join("test.toml");
        sidecar.is_file().then_some(sidecar)
    } else {
        let sidecar = fixture_path.with_extension("toml");
        sidecar.is_file().then_some(sidecar)
    }
}

fn parse_sidecar(path: &Path) -> PartialConfig {
    let contents = fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("failed to read sidecar {}: {e}", path.display()));
    let mut partial = PartialConfig::default();
    let mut section = String::new();

    for raw_line in contents.lines() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        if line.starts_with('[') && line.ends_with(']') {
            section = line[1..line.len() - 1].trim().to_string();
            continue;
        }

        let (key, value) = line
            .split_once('=')
            .unwrap_or_else(|| panic!("invalid sidecar line in {}: `{line}`", path.display()));
        let key = key.trim();
        let value = parse_scalar(value.trim());

        match section.as_str() {
            "" => match key {
                "runner" => partial.runner = Some(parse_runner(&value)),
                "prelude" => partial.prelude = Some(parse_prelude(&value)),
                other => panic!(
                    "unknown top-level sidecar key `{other}` in {}",
                    path.display()
                ),
            },
            "options" => match key {
                "move_check" => partial.move_check = Some(parse_bool(&value)),
                "rfc" => partial.rfc = Some(parse_rfc_list(&value, path)),
                "spec" => partial.spec = Some(parse_spec_list(&value, path)),
                "skip" => partial.skip = Some(value),
                "spec_title" => {
                    let trimmed = value.trim();
                    partial.spec_title = (!trimmed.is_empty()).then(|| trimmed.to_string());
                }
                "error" => partial.error = Some(parse_error_code_list(&value, path)),
                "arch_verifies" => {
                    partial.arch_verifies = Some(parse_arch_verifies_list(&value, path));
                }
                other => panic!(
                    "unknown options sidecar key `{other}` in {}",
                    path.display()
                ),
            },
            "expect" => match key {
                "status" => partial.status = Some(parse_status(&value)),
                "code" => partial.code = Some(value),
                "contains" => partial.contains = Some(value),
                "line" => {
                    partial.line = Some(value.parse().unwrap_or_else(|e| {
                        panic!("invalid integer for `line` in {}: {e}", path.display())
                    }))
                }
                "col" => {
                    partial.col = Some(value.parse().unwrap_or_else(|e| {
                        panic!("invalid integer for `col` in {}: {e}", path.display())
                    }))
                }
                "warnings" => partial.warnings = Some(parse_list(&value)),
                other => panic!("unknown expect sidecar key `{other}` in {}", path.display()),
            },
            "program" => match key {
                "imports" => {
                    partial.program_imports = Some(value.parse().unwrap_or_else(|e| {
                        panic!("invalid integer for `imports` in {}: {e}", path.display())
                    }))
                }
                "decls" => {
                    partial.program_decls = Some(value.parse().unwrap_or_else(|e| {
                        panic!("invalid integer for `decls` in {}: {e}", path.display())
                    }))
                }
                other => panic!(
                    "unknown program sidecar key `{other}` in {}",
                    path.display()
                ),
            },
            "graph" => match key {
                "module_count" => {
                    partial.graph_module_count = Some(value.parse().unwrap_or_else(|e| {
                        panic!(
                            "invalid integer for `module_count` in {}: {e}",
                            path.display()
                        )
                    }))
                }
                "has_module_paths" => {
                    partial.graph_has_module_paths = Some(
                        parse_list(&value)
                            .into_iter()
                            .map(|path| path.split("::").map(|seg| seg.to_string()).collect())
                            .collect(),
                    )
                }
                other => panic!("unknown graph sidecar key `{other}` in {}", path.display()),
            },
            other => panic!("unknown sidecar section `[{other}]` in {}", path.display()),
        }
    }

    partial
}

fn parse_scalar(raw: &str) -> String {
    let trimmed = raw.trim();
    if trimmed.starts_with('"') && trimmed.ends_with('"') && trimmed.len() >= 2 {
        trimmed[1..trimmed.len() - 1].to_string()
    } else {
        trimmed.to_string()
    }
}

fn parse_runner(value: &str) -> RunnerKind {
    match value {
        "parse" => RunnerKind::Parse,
        "typecheck" => RunnerKind::Typecheck,
        "evaluate" => RunnerKind::Evaluate,
        "load_program" => RunnerKind::LoadProgram,
        "load_graph" => RunnerKind::LoadGraph,
        "full_pipeline" => RunnerKind::FullPipeline,
        other => panic!("unknown runner `{other}`"),
    }
}

fn parse_prelude(value: &str) -> CorePreludeMode {
    match value {
        "empty" => CorePreludeMode::Empty,
        "default" => CorePreludeMode::Default,
        other => panic!("unknown prelude mode `{other}`"),
    }
}

fn parse_status(value: &str) -> ExpectStatus {
    match value {
        "success" => ExpectStatus::Success,
        "parse_error" => ExpectStatus::ParseError,
        "typecheck_error" => ExpectStatus::TypecheckError,
        "runtime_error" => ExpectStatus::RuntimeError,
        "load_error" => ExpectStatus::LoadError,
        other => panic!("unknown expectation status `{other}`"),
    }
}

fn parse_bool(value: &str) -> bool {
    match value {
        "true" => true,
        "false" => false,
        other => panic!("unknown boolean literal `{other}`"),
    }
}

fn parse_legacy_expectation(suite: &str, fixture_path: &Path) -> Option<PartialConfig> {
    if suite == "parsing" {
        return fixture_path
            .file_stem()
            .and_then(|stem| stem.to_str())
            .filter(|stem| stem.starts_with("neg_"))
            .map(|_| PartialConfig {
                status: Some(ExpectStatus::ParseError),
                ..PartialConfig::default()
            });
    }

    let source_path = main_source_path(fixture_path);
    let source = fs::read_to_string(&source_path).ok()?;

    if suite == "typechecking" {
        for (idx, line) in source.lines().enumerate() {
            if let Some(code) = extract_annotation(line, "// ERROR[") {
                return Some(PartialConfig {
                    status: Some(ExpectStatus::TypecheckError),
                    code: Some(code),
                    line: Some(idx + 1),
                    ..PartialConfig::default()
                });
            }
        }
    }

    if suite == "evaluator" {
        for line in source.lines() {
            if let Some(expected) = extract_annotation(line, "// PARSE_ERROR[") {
                return Some(PartialConfig {
                    status: Some(ExpectStatus::ParseError),
                    contains: Some(expected),
                    ..PartialConfig::default()
                });
            }
            if let Some(expected) = extract_annotation(line, "// TYPECHECK_ERROR[") {
                return Some(PartialConfig {
                    status: Some(ExpectStatus::TypecheckError),
                    contains: Some(expected),
                    ..PartialConfig::default()
                });
            }
            if let Some(expected) = extract_annotation(line, "// RUNTIME_ERROR[") {
                return Some(PartialConfig {
                    status: Some(ExpectStatus::RuntimeError),
                    contains: Some(expected),
                    ..PartialConfig::default()
                });
            }
        }
    }

    None
}

fn extract_annotation(line: &str, marker: &str) -> Option<String> {
    let start = line.find(marker)?;
    let rest = &line[start + marker.len()..];
    let end = rest.find(']')?;
    Some(rest[..end].to_string())
}

/// Parses and validates an `options.rfc` list against ADR-0049's citation
/// grammar: `rfc-NNNN` or `rfc-NNNN§section`, where `section` is
/// `part("."part)?` and `part` is `digit+letter?` (e.g. `7`, `9c`, `3a` --
/// letter-suffixed sections are real, not hypothetical: RFC-0071 §9a-9c,
/// RFC-0082 §3a, RFC-0118 §2a, RFC-0067a §3a, RFC-0110 §1a all exist). The
/// RFC id itself can carry the same optional letter suffix -- `rfc-0067a`
/// is a real, distinct RFC id (Reference Types), not a typo for `rfc-0067`
/// (a different RFC, Lifetime Anchors) -- found the hard way when a
/// migration first cited the wrong one and this validator accepted it
/// anyway, because it only allowed the letter suffix on the section half.
fn parse_rfc_list(raw: &str, path: &Path) -> Vec<String> {
    let citations = parse_list(raw);
    for citation in &citations {
        let lower = citation.to_ascii_lowercase();
        let (id, section) = match lower.split_once('§') {
            Some((id, section)) => (id, Some(section)),
            None => (lower.as_str(), None),
        };
        let id_ok = id.starts_with("rfc-") && {
            let digits_and_letter = &id[4..];
            let digit_end = digits_and_letter
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(digits_and_letter.len());
            let (digits, rest) = digits_and_letter.split_at(digit_end);
            digits.len() == 4
                && matches!(rest.len(), 0 | 1)
                && rest.chars().all(|c| c.is_ascii_lowercase())
        };
        let section_ok = section.is_none_or(|s| {
            !s.is_empty()
                && s.split('.').all(|part| {
                    let digits_end = part
                        .find(|c: char| !c.is_ascii_digit())
                        .unwrap_or(part.len());
                    let (digits, rest) = part.split_at(digits_end);
                    !digits.is_empty()
                        && matches!(rest.len(), 0 | 1)
                        && rest.chars().all(|c| c.is_ascii_lowercase())
                })
        });
        if !id_ok || !section_ok {
            panic!(
                "invalid `rfc` citation `{citation}` in {} -- expected `rfc-NNNN` or \
                 `rfc-NNNN§section` (section like `7`, `9c`, `7.2`), per ADR-0049",
                path.display()
            );
        }
    }
    citations
}

/// Parses and validates an `options.spec` list against ADR-0050's citation
/// grammar: `spec.<file>.<section>.<kind>-<n>`, where `file` is a spec
/// file's stem, `section` is one or more dot-separated kebab-case segments
/// (the heading breadcrumb down to the block's immediate enclosing
/// section), `kind` is `legality` or `dynamics`, and `n` is `digit+letter*`
/// -- `letter*`, not a single optional letter, because a split block can be
/// split again (`legality-1a` splitting into `legality-1aa`/`legality-1ab`,
/// ADR-0050 §3). No colons anywhere in the grammar: ADR-0050 §3 found, by
/// running a real `docusaurus build`, that Docusaurus's `{#custom-id}`
/// heading-attribute mechanism silently corrupts a colon (truncated, and
/// leaked into the visible rendered heading) rather than rejecting it --
/// worse than a build failure, since nothing would flag it -- so the
/// grammar avoids the character entirely and uses `.` as every separator.
fn parse_spec_list(raw: &str, path: &Path) -> Vec<String> {
    let citations = parse_list(raw);
    for citation in &citations {
        let valid = (|| {
            let rest = citation.strip_prefix("spec.")?;
            let segments: Vec<&str> = rest.split('.').collect();
            // At minimum: file, one section segment, kind-n.
            if segments.len() < 3 {
                return None;
            }
            let (file, tail) = segments.split_first()?;
            let (kind_n, section_parts) = tail.split_last()?;
            if section_parts.is_empty() {
                return None;
            }
            let is_kebab = |s: &str| {
                !s.is_empty()
                    && s.chars()
                        .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
            };
            if !is_kebab(file) || !section_parts.iter().all(|part| is_kebab(part)) {
                return None;
            }
            let (kind, n) = kind_n.split_once('-')?;
            if !matches!(kind, "legality" | "dynamics") {
                return None;
            }
            let digit_end = n.find(|c: char| !c.is_ascii_digit()).unwrap_or(n.len());
            let (digits, letters) = n.split_at(digit_end);
            (!digits.is_empty() && letters.chars().all(|c| c.is_ascii_lowercase())).then_some(())
        })()
        .is_some();
        if !valid {
            panic!(
                "invalid `spec` citation `{citation}` in {} -- expected \
                 `spec.<file>.<section>.<kind>-<n>` (kind is `legality` or `dynamics`, `n` is \
                 digits with an optional split-lineage letter suffix, no colons anywhere), \
                 per ADR-0050",
                path.display()
            );
        }
    }
    citations
}

/// Parses and validates an `options.arch_verifies` list against the
/// Architecture Spec's citation grammar (metel-core#1175):
/// `arch.<section>.requirement-<n>`, where `section` is one or more
/// dot-separated kebab-case segments naming an `architecture/spec/*.md`
/// file's `##### Requirement {#arch....}` anchor, and `n` is one or more
/// digits. Mirrors `parse_spec_list`'s shape but for `arch-*` Architecture
/// Spec requirements rather than Language Spec Formal-rules blocks; kept to
/// the exact grammar `generate_architecture_evidence.py`'s `ID` regex
/// expects, since that script reads this key straight from the `.toml`
/// source rather than through this harness.
fn parse_arch_verifies_list(raw: &str, path: &Path) -> Vec<String> {
    let citations = parse_list(raw);
    for citation in &citations {
        let valid = (|| {
            let rest = citation.strip_prefix("arch.")?;
            let (section, n) = rest.rsplit_once(".requirement-")?;
            let is_kebab = |s: &str| {
                !s.is_empty()
                    && s.chars()
                        .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
            };
            (!n.is_empty()
                && n.chars().all(|c| c.is_ascii_digit())
                && !section.is_empty()
                && section.split('.').all(is_kebab))
            .then_some(())
        })()
        .is_some();
        if !valid {
            panic!(
                "invalid `arch_verifies` citation `{citation}` in {} -- expected \
                 `arch.<section>.requirement-<n>` (section is one or more dot-separated \
                 kebab-case segments, n is digits), per metel-core#1175",
                path.display()
            );
        }
    }
    citations
}

/// `error = […]` -- a bare error-code shape (`T0003`, `R0015`, `I0002`, ...),
/// deliberately not the `spec.<file>.<section>.<kind>-<n>` grammar `spec =`
/// citations use (metel-core#981: different axis, different grammar, kept
/// visually and structurally distinct). One uppercase letter, exactly four
/// digits, nothing else.
fn parse_error_code_list(raw: &str, path: &Path) -> Vec<String> {
    let codes = parse_list(raw);
    for code in &codes {
        let bytes = code.as_bytes();
        let valid = bytes.len() == 5
            && bytes[0].is_ascii_uppercase()
            && bytes[1..].iter().all(u8::is_ascii_digit);
        if !valid {
            panic!(
                "invalid `error` citation `{code}` in {} -- expected one uppercase letter \
                 followed by exactly four digits (e.g. `T0003`)",
                path.display()
            );
        }
    }
    codes
}

fn parse_list(raw: &str) -> Vec<String> {
    let trimmed = raw.trim();
    if !(trimmed.starts_with('[') && trimmed.ends_with(']')) {
        panic!("expected list value, got `{trimmed}`");
    }
    let inner = &trimmed[1..trimmed.len() - 1];
    if inner.trim().is_empty() {
        return Vec::new();
    }
    inner
        .split(',')
        .map(|item| parse_scalar(item.trim()))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sources() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/integration/sources")
    }

    #[test]
    fn spec_title_sidecar_key_is_accepted_and_parsed() {
        // metel-core#974: an `[options] spec_title` key must parse (the sidecar
        // parser panics on unknown keys) and land in `FixtureOptions`.
        let cfg = resolve_fixture_config(
            "evaluator",
            &sources().join("evaluator/closures/v0_13_0_move_capture_by_value.mtl"),
        );
        assert_eq!(
            cfg.options.spec_title.as_deref(),
            Some("a non-`Copy` capture is moved into the closure at creation"),
        );
    }

    #[test]
    fn spec_title_absent_is_none() {
        let cfg = resolve_fixture_config(
            "evaluator",
            &sources().join("evaluator/closures/33_closure.mtl"),
        );
        assert_eq!(cfg.options.spec_title, None);
    }
}
