use std::fs;
use std::path::Path;

use metel::error::MetelError;
use metel::{
    coherence, elaborator, evaluator, identity, module_loader, name_resolver, parser,
    path_normalizer, pipeline, typechecker,
};

use super::fixture::{
    main_source_path, CorePreludeMode, ExpectStatus, FixtureConfig, GraphChecks, ProgramChecks,
};

pub fn run_fixture(path: &Path, config: &FixtureConfig) {
    if let Some(reason) = &config.options.skip {
        eprintln!("SKIP {}: {reason}", path.display());
        return;
    }

    let result = match config.runner {
        super::fixture::RunnerKind::Parse => run_parse(path),
        super::fixture::RunnerKind::Typecheck => run_typecheck(path, config),
        super::fixture::RunnerKind::Evaluate => run_evaluate(path, config),
        super::fixture::RunnerKind::LoadProgram => run_load_program(path, &config.program),
        super::fixture::RunnerKind::LoadGraph => run_load_graph(path, &config.graph),
        super::fixture::RunnerKind::FullPipeline => run_full_pipeline(path, config),
    };

    match config.expect.status {
        ExpectStatus::Success => {
            if let Err(err) = result {
                panic!("expected success for {}, got: {err}", path.display());
            }
        }
        ExpectStatus::ParseError => {
            let err = result.expect_err(&format!("expected parse error for {}", path.display()));
            assert_parse_error(path, &err, config);
        }
        ExpectStatus::TypecheckError => {
            let err = result.expect_err(&format!("expected type error for {}", path.display()));
            assert_type_error(path, &err, config);
        }
        ExpectStatus::RuntimeError => {
            let err = result.expect_err(&format!("expected runtime error for {}", path.display()));
            assert_runtime_error(path, &err, config);
        }
        ExpectStatus::LoadError => {
            let err = result.expect_err(&format!("expected load error for {}", path.display()));
            assert_contains(path, &err.to_string(), config.expect.contains.as_deref());
        }
    }
}

fn run_parse(path: &Path) -> Result<(), MetelError> {
    let source_path = main_source_path(path);
    let source = fs::read_to_string(&source_path)
        .unwrap_or_else(|e| panic!("could not read {}: {e}", source_path.display()));
    let filename = source_path
        .file_name()
        .unwrap_or_default()
        .to_string_lossy()
        .to_string();
    parser::parse(&source, &filename).map(|_| ())
}

// Both `run_typecheck` and `run_evaluate` drive the *full module pipeline* (the
// same one `pipeline::run_file` and the shipped binary use), loading std::core
// as a real embedded module. The earlier single-program path (`check_with_ctx` /
// `evaluate_with_ctx`) skipped module loading + elaboration and hand-seeded
// std::core, which drifted from the product path and could not run Metel-bodied
// core free functions (e.g. the print/println Display wrappers, METEL-192). The
// pub single-program API remains for the benchmark binary only.
fn run_typecheck(path: &Path, config: &FixtureConfig) -> Result<(), MetelError> {
    let graph = module_loader::load_root(main_source_path(path))?;
    let names = name_resolver::resolve(&graph)?;
    let members = identity::collect_members_for_graph(&graph, &names);
    let allocation = identity::allocate_for_graph(&graph, &names);
    let normalized = path_normalizer::normalize(graph, &names)?;
    coherence::check(&normalized, &names)?;
    let typed = typechecker::check_graph_with_report(
        &normalized,
        &names,
        &typechecker::CorePrelude::default(),
        Some(identity::FrozenIdentity {
            members: &members,
            binding_spans: &allocation.binding_spans,
        }),
    )?;
    assert_warnings(path, &typed.warnings, config.expect.warnings.as_deref());
    if config.options.move_check {
        for warning in metel::move_check::check_graph(&typed.graph)? {
            eprintln!("warning: {warning}");
        }
    }
    Ok(())
}

fn run_evaluate(path: &Path, config: &FixtureConfig) -> Result<(), MetelError> {
    let report = pipeline::run_evaluator_fixture(
        &main_source_path(path).to_string_lossy(),
        &pipeline::RunOptions {
            move_check: config.options.move_check,
            ..pipeline::RunOptions::default()
        },
    )?;
    assert_warnings(path, &report.warnings, config.expect.warnings.as_deref());
    for warning in report.warnings {
        eprintln!("warning: {warning}");
    }
    Ok(())
}

fn run_load_program(path: &Path, checks: &ProgramChecks) -> Result<(), MetelError> {
    let program = module_loader::load_program(main_source_path(path))?;
    if let Some(expected) = checks.imports {
        assert_eq!(
            program.imports.len(),
            expected,
            "wrong import count for {}",
            path.display()
        );
    }
    if let Some(expected) = checks.decls {
        assert_eq!(
            program.decls.len(),
            expected,
            "wrong decl count for {}",
            path.display()
        );
    }
    Ok(())
}

fn run_load_graph(path: &Path, checks: &GraphChecks) -> Result<(), MetelError> {
    let graph = module_loader::load_root(main_source_path(path))?;
    assert_graph_checks(path, &graph, checks);
    Ok(())
}

fn run_full_pipeline(path: &Path, config: &FixtureConfig) -> Result<(), MetelError> {
    let graph = module_loader::load_root(main_source_path(path))?;
    assert_graph_checks(path, &graph, &config.graph);
    let names = name_resolver::resolve(&graph)?;
    let members = identity::collect_members_for_graph(&graph, &names);
    let allocation = identity::allocate_for_graph(&graph, &names);
    let normalized = path_normalizer::normalize(graph, &names)?;
    coherence::check(&normalized, &names)?;
    let typed = typechecker::check_graph_with_report(
        &normalized,
        &names,
        &std_prelude(config.prelude),
        Some(identity::FrozenIdentity {
            members: &members,
            binding_spans: &allocation.binding_spans,
        }),
    )?;
    assert_warnings(path, &typed.warnings, config.expect.warnings.as_deref());
    if config.options.move_check {
        for warning in metel::move_check::check_graph(&typed.graph)? {
            eprintln!("warning: {warning}");
        }
    }
    let elaborated = elaborator::elaborate(typed.graph, &names)?;
    let runtime_identity = evaluator::RuntimeIdentity {
        members: std::rc::Rc::new(members),
        binding_spans: std::rc::Rc::new(allocation.binding_spans),
    };
    evaluator::evaluate_graph_with_options(
        elaborated,
        evaluator::EvaluationOptions::default(),
        Some(&runtime_identity),
    )
    .map(|_| ())
}

fn assert_warnings(path: &Path, actual: &[String], expected: Option<&[String]>) {
    let Some(expected) = expected else {
        return;
    };
    assert_eq!(
        actual.len(),
        expected.len(),
        "wrong warnings for {}",
        path.display()
    );
    for expected_warning in expected {
        assert!(
            actual
                .iter()
                .any(|warning| warning.contains(expected_warning)),
            "missing warning `{expected_warning}` for {}; got {actual:#?}",
            path.display()
        );
    }
}

fn std_prelude(mode: CorePreludeMode) -> typechecker::CorePrelude {
    match mode {
        CorePreludeMode::Empty => typechecker::CorePrelude::empty(),
        CorePreludeMode::Default => typechecker::CorePrelude::default(),
    }
}

fn assert_parse_error(path: &Path, err: &MetelError, config: &FixtureConfig) {
    match err {
        MetelError::ParseError {
            code, line, col, ..
        } => {
            if let Some(expected) = &config.expect.code {
                assert_eq!(
                    &format!("{code}"),
                    expected,
                    "wrong parse error code in {}",
                    path.display()
                );
            }
            if let Some(expected) = config.expect.line {
                assert_eq!(
                    *line as usize,
                    expected,
                    "wrong parse error line in {}",
                    path.display()
                );
            }
            if let Some(expected) = config.expect.col {
                assert_eq!(
                    *col as usize,
                    expected,
                    "wrong parse error column in {}",
                    path.display()
                );
            }
            assert_contains(path, &err.to_string(), config.expect.contains.as_deref());
        }
        other => panic!("expected parse error for {}, got: {other}", path.display()),
    }
}

fn assert_type_error(path: &Path, err: &MetelError, config: &FixtureConfig) {
    match err {
        MetelError::TypeError {
            code, line, col, ..
        } => {
            if let Some(expected) = &config.expect.code {
                assert_eq!(
                    &format!("{code}"),
                    expected,
                    "wrong type error code in {}",
                    path.display()
                );
            }
            if let Some(expected) = config.expect.line {
                assert_eq!(
                    *line as usize,
                    expected,
                    "wrong type error line in {}",
                    path.display()
                );
            }
            if let Some(expected) = config.expect.col {
                assert_eq!(
                    *col as usize,
                    expected,
                    "wrong type error column in {}",
                    path.display()
                );
            }
            assert_contains(path, &err.to_string(), config.expect.contains.as_deref());
        }
        other => panic!("expected type error for {}, got: {other}", path.display()),
    }
}

fn assert_runtime_error(path: &Path, err: &MetelError, config: &FixtureConfig) {
    match err {
        MetelError::RuntimePanic { code, .. } => {
            if let Some(expected) = &config.expect.code {
                assert_eq!(
                    &format!("{code}"),
                    expected,
                    "wrong runtime error code in {}",
                    path.display()
                );
            }
            assert_contains(path, &err.to_string(), config.expect.contains.as_deref());
        }
        other => panic!(
            "expected runtime error for {}, got: {other}",
            path.display()
        ),
    }
}

fn assert_contains(path: &Path, actual: &str, expected: Option<&str>) {
    if let Some(expected) = expected {
        assert!(
            actual.contains(expected),
            "expected error for {} to contain `{expected}`, got: {actual}",
            path.display(),
        );
    }
}

fn assert_graph_checks(
    path: &Path,
    graph: &metel::module_loader::ModuleGraph,
    checks: &GraphChecks,
) {
    if let Some(expected) = checks.module_count {
        // Count user modules only; the binary-embedded std:: modules (METEL-181)
        // are always present and are not what these fixtures assert about.
        let user_modules = graph
            .modules
            .iter()
            .filter(|m| m.module_path.first().map(String::as_str) != Some("std"))
            .count();
        assert_eq!(
            user_modules,
            expected,
            "wrong module count for {}",
            path.display()
        );
    }
    for expected in &checks.has_module_paths {
        assert!(
            graph
                .modules
                .iter()
                .any(|module| module.module_path == *expected),
            "expected module path `{}` in {}",
            expected.join("::"),
            path.display(),
        );
    }
}
