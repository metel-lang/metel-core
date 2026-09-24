//! RFC-0154 follow-up: drop the written return type from a **closure literal**
//! in expression position — `|x| -> T { … }` becomes `|x| { … }` — leaving the
//! body to infer it (RFC-0041 / RFC-0154). A written function *type*
//! (`|T| -> U`, a `fun` return type, a parameter annotation) keeps its `-> U`
//! and is never touched: only `Rule::closure_expr` nodes are rewritten.
//!
//! AST-driven, not a text substitution. For each `closure_expr` that has a
//! `type_expr` child (its return type), it splices out `[the `->` .. the `{`)`.
//! The `->` located is always the closure's own — `rfind` takes the last one
//! before the return type, so a `->` inside a parameter's own function type
//! (`|inner: || -> i64| -> i64 { … }`) is left alone.
//!
//! Usage: `cargo run -p metel-frontend --example drop_closure_ret -- [--check]
//! <path>...`
//!
//! `<path>` is a file or directory (walked recursively, `*.mtl`). `--check`
//! prints what would change and exits non-zero without writing.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use metel_frontend::pipeline::parsing::parser::MetelParser;
use metel_frontend::pipeline::parsing::parser::Rule;
use pest::Parser;

struct Edit {
    start: usize,
    end: usize,
}

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let check = args.iter().any(|a| a == "--check");
    args.retain(|a| a != "--check");
    if args.is_empty() {
        eprintln!("usage: drop_closure_ret [--check] <path>...");
        return ExitCode::FAILURE;
    }

    let mut files: Vec<PathBuf> = Vec::new();
    for a in &args {
        collect_mtl(Path::new(a), &mut files);
    }
    files.sort();
    files.dedup();

    let mut changed = 0usize;
    let mut parse_failures = 0usize;
    for path in &files {
        let Ok(src) = fs::read_to_string(path) else {
            eprintln!("skip {}", path.display());
            continue;
        };
        let edits = match edits_for(&src) {
            Ok(e) => e,
            Err(e) => {
                eprintln!("PARSE-FAIL {}: {e}", path.display());
                parse_failures += 1;
                continue;
            }
        };
        if edits.is_empty() {
            continue;
        }
        changed += 1;
        if check {
            println!("{}  ({} edit(s))", path.display(), edits.len());
        } else {
            fs::write(path, splice(&src, &edits)).expect("write");
        }
    }

    eprintln!(
        "{} file(s) scanned, {} {}, {} parse failure(s)",
        files.len(),
        changed,
        if check { "would change" } else { "rewritten" },
        parse_failures
    );
    if check && changed > 0 {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn collect_mtl(p: &Path, out: &mut Vec<PathBuf>) {
    if p.is_file() {
        if p.extension().and_then(|e| e.to_str()) == Some("mtl") {
            out.push(p.to_path_buf());
        }
        return;
    }
    if let Ok(rd) = fs::read_dir(p) {
        for e in rd.flatten() {
            let path = e.path();
            if path.file_name().and_then(|n| n.to_str()) == Some("target") {
                continue;
            }
            collect_mtl(&path, out);
        }
    }
}

fn edits_for(src: &str) -> Result<Vec<Edit>, String> {
    let pairs = MetelParser::parse(Rule::program, src).map_err(|e| e.to_string())?;
    let mut edits = Vec::new();
    for pair in pairs {
        walk(pair, src, &mut edits);
    }
    edits.sort_by_key(|e| e.start);
    edits.dedup_by_key(|e| e.start);
    Ok(edits)
}

fn walk(pair: pest::iterators::Pair<Rule>, src: &str, edits: &mut Vec<Edit>) {
    if pair.as_rule() == Rule::closure_expr {
        closure_ret_edit(&pair, src, edits);
    }
    for inner in pair.into_inner() {
        walk(inner, src, edits);
    }
}

fn closure_ret_edit(pair: &pest::iterators::Pair<Rule>, src: &str, edits: &mut Vec<Edit>) {
    let mut ret_start = None;
    let mut block_start = None;
    for inner in pair.clone().into_inner() {
        match inner.as_rule() {
            Rule::type_expr => ret_start = Some(inner.as_span().start()),
            Rule::block => block_start = Some(inner.as_span().start()),
            _ => {}
        }
    }
    let (Some(ret_start), Some(block_start)) = (ret_start, block_start) else {
        return;
    };
    // The closure's own `->` is the last one before the return type — any `->`
    // inside a parameter's function type comes earlier.
    let Some(arrow) = src[..ret_start].rfind("->") else {
        return;
    };
    edits.push(Edit {
        start: arrow,
        end: block_start,
    });
}

fn splice(src: &str, edits: &[Edit]) -> String {
    let mut out = String::with_capacity(src.len());
    let mut last = 0;
    for e in edits {
        assert!(e.start >= last, "overlapping edits");
        out.push_str(&src[last..e.start]);
        last = e.end;
    }
    out.push_str(&src[last..]);
    out
}
