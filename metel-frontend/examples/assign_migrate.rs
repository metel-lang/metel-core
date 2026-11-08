//! RFC-0183 migration: plain reassignment moves from `:=` to `=`, and assignment (plain and
//! compound) becomes a statement.
//!
//! Like `walrus_migrate`, this is a parser-driven rewriter that runs under the OLD grammar (where
//! assignment is an expression and plain reassignment is spelled `:=`): it walks the concrete pest
//! parse tree, so it never mistakes a declaration's `:=` (`let`, `var`, `type`, record-pattern
//! declarations) for a reassignment, and it rewrites by byte offset, never by text substitution.
//!
//! For each assignment it finds, by the grammar rule that holds it:
//! - a statement (`expr_stmt`, a match-arm body, a `for` header's update clause): `:=` becomes `=`;
//! - a block's tail expression: `:=` becomes `=` and a `;` is appended (an assignment is a
//!   statement and needs its `;`, RFC-0183 section 1);
//! - a bare `if`/`else` branch: wrapped in a block, `{ x = 1; }`, since a branch is an expression;
//! - anywhere else (an operand, an argument, an initializer, a condition, a chained assignment):
//!   reported for a hand rewrite, because the new grammar rejects it.
//!
//! Usage:
//!   cargo run -p metel-frontend --example assign_migrate -- [--check] [--md | --rs] <path>...
//!
//! `<path>` may be a file or a directory (walked recursively for `*.mtl`, or `*.md`/`*.mdx` with
//! `--md`, or `*.rs` raw strings with `--rs`). With `--check`, prints what would change and exits
//! non-zero if anything would, without writing.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use metel_frontend::pipeline::parsing::parser::MetelParser;
use metel_frontend::pipeline::parsing::parser::Rule;
use pest::Parser;

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let check = args.iter().any(|a| a == "--check");
    args.retain(|a| a != "--check");
    if args.is_empty() {
        eprintln!("usage: assign_migrate [--check] <path>...");
        return ExitCode::FAILURE;
    }

    let rs = args.iter().any(|a| a == "--rs");
    let md = args.iter().any(|a| a == "--md");
    args.retain(|a| a != "--rs" && a != "--md");

    let mut files: Vec<PathBuf> = Vec::new();
    for a in &args {
        if md {
            for e in ["md", "mdx"] {
                collect_by_ext(Path::new(a), e, &mut files);
            }
        } else {
            collect_by_ext(Path::new(a), if rs { "rs" } else { "mtl" }, &mut files);
        }
    }
    files.sort();
    files.dedup();

    let mut changed = 0usize;
    let mut parse_failures = 0usize;
    for path in &files {
        let src = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("skip {}: {e}", path.display());
                continue;
            }
        };
        let (new_src, n_sites, failed) = if md {
            rewrite_md_metel_fences(&src)
        } else if rs {
            rewrite_rs_raw_strings(&src)
        } else {
            match edits_to_apply(&src) {
                Ok(o) => (splice(&src, &o), o.len(), false),
                Err(e) => {
                    eprintln!("PARSE-FAIL {}: {e}", path.display());
                    (src.clone(), 0, true)
                }
            }
        };
        if failed {
            parse_failures += 1;
            continue;
        }
        if n_sites == 0 {
            continue;
        }
        changed += 1;
        if check {
            println!("{}  ({n_sites} site(s))", path.display());
        } else {
            fs::write(path, new_src).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
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

fn collect_by_ext(p: &Path, ext: &str, out: &mut Vec<PathBuf>) {
    if p.is_file() {
        if p.extension().and_then(|e| e.to_str()) == Some(ext) {
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
            collect_by_ext(&path, ext, out);
        }
    }
}

/// Rewrite Metel `let`/reassignment `=` → `:=` inside every `r#"..."#` /
/// `r##"..."##` raw string literal in a Rust file. Non-raw strings and Rust code
/// outside them are untouched. A raw-string block whose content does not parse as
/// a Metel `program` is skipped (it may be a fragment, or not Metel at all).
fn rewrite_rs_raw_strings(src: &str) -> (String, usize, bool) {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    let mut total_sites = 0usize;
    let mut in_rust_str = false; // inside an ordinary "..." (with \" escapes)
    while i < bytes.len() {
        if in_rust_str {
            if bytes[i] == b'\\' {
                out.push_str(&src[i..(i + 2).min(bytes.len())]);
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_rust_str = false;
            }
            out.push(bytes[i] as char);
            i += 1;
            continue;
        }
        // A raw-string prefix: `r` at a token boundary, then optional `#`s, then `"`.
        let at_boundary = i == 0 || {
            let p = bytes[i - 1];
            !(p.is_ascii_alphanumeric() || p == b'_')
        };
        if bytes[i] == b'"' {
            in_rust_str = true;
            out.push('"');
            i += 1;
            continue;
        }
        if bytes[i] == b'r' && at_boundary {
            let mut j = i + 1;
            let mut hashes = 0;
            while j < bytes.len() && bytes[j] == b'#' {
                hashes += 1;
                j += 1;
            }
            if j < bytes.len() && bytes[j] == b'"' {
                let content_start = j + 1;
                let closing = format!("\"{}", "#".repeat(hashes));
                if let Some(rel) = src[content_start..].find(&closing) {
                    let content_end = content_start + rel;
                    let content = &src[content_start..content_end];
                    out.push_str(&src[i..content_start]); // `r##"` prefix
                    match edits_to_apply(content) {
                        Ok(edits) if !edits.is_empty() => {
                            total_sites += edits.len();
                            out.push_str(&splice(content, &edits));
                        }
                        // A raw-string block that is not a full Metel `program`
                        // (a fragment, or not Metel) is left exactly as-is.
                        _ => out.push_str(content),
                    }
                    out.push_str(&closing);
                    i = content_end + closing.len();
                    continue;
                }
            }
        }
        let ch = src[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    (out, total_sites, false)
}

/// Rewrite Metel `let`/reassignment `=` → `:=` inside every ```` ```metel ```` fenced
/// code block in a Markdown/MDX file. A block that does not parse as a Metel
/// `program` (a fragment, or deliberately not-yet-valid syntax) is left as-is.
fn rewrite_md_metel_fences(src: &str) -> (String, usize, bool) {
    let mut out = String::with_capacity(src.len());
    let mut total = 0usize;
    let mut rest = src;
    while let Some(open_rel) = find_metel_fence_open(rest) {
        let after_open = &rest[open_rel..];
        // `after_open` starts at the newline that ends the ```metel line.
        let content_start = 1; // skip that newline
        let Some(close_rel) = after_open[content_start..].find("\n```") else {
            break;
        };
        let content_end = content_start + close_rel + 1; // include the newline before ```
        let content = &after_open[content_start..content_end];
        out.push_str(&rest[..open_rel + content_start]);
        match edits_to_apply(content) {
            Ok(edits) if !edits.is_empty() => {
                total += edits.len();
                out.push_str(&splice(content, &edits));
            }
            _ => out.push_str(content),
        }
        rest = &after_open[content_end..];
    }
    out.push_str(rest);
    (out, total, false)
}

/// Offset of the newline that terminates the next ```` ```metel ```` fence line.
fn find_metel_fence_open(s: &str) -> Option<usize> {
    let mut search_from = 0;
    loop {
        let rel = s[search_from..].find("```metel")?;
        let abs = search_from + rel;
        let tail = &s[abs + "```metel".len()..];
        // The fence line may carry an info string suffix (` title=…`); it ends at
        // the newline.
        if let Some(nl) = tail.find('\n') {
            // Must be at column 0 (start of line or after a newline).
            if abs == 0 || s.as_bytes()[abs - 1] == b'\n' {
                return Some(abs + "```metel".len() + nl);
            }
        }
        search_from = abs + 1;
    }
}

/// One byte-range edit: replace `len` bytes at `start` with `insert`.
#[derive(Debug, Clone)]
pub struct Edit {
    pub start: usize,
    pub len: usize,
    pub insert: &'static str,
}

/// The edits that migrate every assignment in `src`, sorted by offset. A source that is not a whole
/// program (a documentation fragment of statements) is parsed inside a wrapping `fun main`, and the
/// wrapper's own tail gets no `;`: a fragment's last line is left as the author wrote it. `Err` for a
/// source that parses neither way under the old grammar, and for an assignment the new grammar would
/// reject that needs a hand rewrite.
pub fn edits_to_apply(src: &str) -> Result<Vec<Edit>, String> {
    match edits_for(src) {
        Ok(edits) => Ok(edits),
        Err(program_error) => {
            const PREFIX: &str = "fun main() {\n";
            let wrapped = format!("{PREFIX}{src}\n}}\n");
            let end = src.trim_end().len();
            match edits_for(&wrapped) {
                Ok(edits) => Ok(edits
                    .into_iter()
                    .filter(|e| !(e.insert == ";" && e.len == 0 && e.start - PREFIX.len() >= end))
                    .map(|e| Edit {
                        start: e.start - PREFIX.len(),
                        ..e
                    })
                    .collect()),
                Err(_) => Err(program_error),
            }
        }
    }
}

fn edits_for(src: &str) -> Result<Vec<Edit>, String> {
    let pairs = MetelParser::parse(Rule::program, src).map_err(|e| e.to_string())?;
    let mut edits = Vec::new();
    let mut manual = Vec::new();
    for pair in pairs {
        walk(pair, &[], &mut edits, &mut manual);
    }
    if let Some((line, text)) = manual.first() {
        return Err(format!("hand rewrite needed at line {line}: `{text}`"));
    }
    edits.sort_by_key(|e| (e.start, e.len));
    edits.dedup_by(|a, b| a.start == b.start && a.len == b.len && a.insert == b.insert);
    Ok(edits)
}

fn walk(
    pair: pest::iterators::Pair<Rule>,
    ancestors: &[Rule],
    edits: &mut Vec<Edit>,
    manual: &mut Vec<(usize, String)>,
) {
    if pair.as_rule() == Rule::assign_expr && is_assignment(&pair) {
        classify(&pair, ancestors, edits, manual);
    }
    let mut chain = ancestors.to_vec();
    chain.push(pair.as_rule());
    for inner in pair.into_inner() {
        walk(inner, &chain, edits, manual);
    }
}

/// `assign_expr = { unary_expr ~ assign_op ~ assign_expr | or_expr }`: it is an assignment when it
/// has an `assign_op` child.
fn is_assignment(pair: &pest::iterators::Pair<Rule>) -> bool {
    pair.clone()
        .into_inner()
        .any(|inner| inner.as_rule() == Rule::assign_op)
}

fn classify(
    pair: &pest::iterators::Pair<Rule>,
    ancestors: &[Rule],
    edits: &mut Vec<Edit>,
    manual: &mut Vec<(usize, String)>,
) {
    let span = pair.as_span();
    let text = span.as_str().trim_end();
    let end = span.start() + text.len();
    // The assignment's own position: `expr { assign_expr }`, so the parent is `expr`, and the rule
    // that holds it is the grandparent.
    let holder = match ancestors {
        [.., holder, Rule::expr] => Some(*holder),
        _ => None,
    };
    match holder {
        Some(Rule::expr_stmt | Rule::match_arm) => {}
        Some(Rule::block) => edits.push(Edit {
            start: end,
            len: 0,
            insert: ";",
        }),
        // A `for` header's init is an `expr_stmt`; its update clause is the bare `expr` here. The
        // condition is also a bare `expr`, and the position cannot tell them apart, so any
        // assignment directly under `for_stmt` is taken to be the update, which is the only
        // assignment-shaped clause a program writes there.
        Some(Rule::for_stmt) => {}
        Some(Rule::if_expr) => {
            edits.push(Edit {
                start: span.start(),
                len: 0,
                insert: "{ ",
            });
            edits.push(Edit {
                start: end,
                len: 0,
                insert: "; }",
            });
        }
        _ => {
            let (line, _) = span.start_pos().line_col();
            manual.push((line, text.chars().take(60).collect()));
        }
    }
    // The plain assignment's `:=` becomes `=`.
    for inner in pair.clone().into_inner() {
        if inner.as_rule() == Rule::assign_op && inner.as_span().as_str().trim_end() == ":=" {
            edits.push(Edit {
                start: inner.as_span().start(),
                len: 2,
                insert: "=",
            });
        }
    }
}

fn splice(src: &str, edits: &[Edit]) -> String {
    let mut out = String::with_capacity(src.len() + edits.len());
    let mut last = 0;
    for edit in edits {
        out.push_str(&src[last..edit.start]);
        out.push_str(edit.insert);
        last = edit.start + edit.len;
    }
    out.push_str(&src[last..]);
    out
}
