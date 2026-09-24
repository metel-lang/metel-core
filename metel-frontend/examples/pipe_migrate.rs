//! RFC-0154 migration: rewrite closure literals and function types from the
//! parenthesized form to pipe notation.
//!
//! - Closure literal: `[caps]? once? var? ( params ) -> Ret? { body }`
//!   becomes `[caps]? once? var? | params | (-> Ret)? { body }`. The `->` that
//!   RFC-0041 required before *every* body is dropped when there is no return
//!   type (`(x) -> { … }` → `|x| { … }`, `() -> { … }` → `|| { … }`).
//! - Function type: `once? var? ( T… ) -> U` becomes `once? var? | T… | -> U`.
//!   The `->` and return type stay (mandatory in a written type). Nested types
//!   (`(A) -> (B) -> C`) convert at every level via the recursive walk.
//!
//! AST-driven, run under the OLD grammar (still `"(" ~ … ~ ")" ~ "->"`). It
//! walks the concrete pest parse tree, takes the byte spans of the `(` / `)` /
//! bare-`->` tokens in each `closure_expr` / `fun_type`, and splices — never a
//! text substitution. Named `fun` declarations, grouping, tuples and calls are
//! untouched (different rules).
//!
//! Usage:
//!   cargo run -p metel-frontend --example pipe_migrate -- [--check] [--rs|--md] <path>...
//!
//! `<path>` is a file or a directory (walked recursively). Default `*.mtl`;
//! `--rs` rewrites Metel inside `r#"…"#` raw strings in `*.rs`; `--md` rewrites
//! Metel inside column-0 ```` ```metel ```` fences in `*.md` / `*.mdx`. `--check`
//! prints what would change and exits non-zero without writing.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use metel_frontend::pipeline::parsing::parser::MetelParser;
use metel_frontend::pipeline::parsing::parser::Rule;
use pest::Parser;

/// One splice: replace `src[start..end]` with `repl`.
#[derive(Clone, Debug)]
pub struct Edit {
    start: usize,
    end: usize,
    repl: &'static str,
}

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let check = args.iter().any(|a| a == "--check");
    let rs = args.iter().any(|a| a == "--rs");
    let md = args.iter().any(|a| a == "--md");
    args.retain(|a| !matches!(a.as_str(), "--check" | "--rs" | "--md"));
    if args.is_empty() {
        eprintln!("usage: pipe_migrate [--check] [--rs|--md] <path>...");
        return ExitCode::FAILURE;
    }

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
            match edits_for(&src) {
                Ok(edits) => (splice(&src, &edits), edits.len(), false),
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
            println!("{}  ({n_sites} edit(s))", path.display());
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

/// All edits for a whole Metel `program` source, sorted ascending, non-overlapping.
pub fn edits_for(src: &str) -> Result<Vec<Edit>, String> {
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
    match pair.as_rule() {
        Rule::closure_expr => closure_edits(&pair, src, edits),
        Rule::fun_type => fun_type_edits(&pair, src, edits),
        _ => {}
    }
    for inner in pair.into_inner() {
        walk(inner, src, edits);
    }
}

/// Byte offset (absolute) of the first `(` at or after `from`, within `[from, end)`.
fn first_paren(src: &str, from: usize, end: usize) -> Option<usize> {
    src.as_bytes()[from..end]
        .iter()
        .position(|&b| b == b'(')
        .map(|r| from + r)
}

/// Byte offset (absolute) of the `)` matching the `(` at `open`, scanning `[open, end)`.
fn match_paren(src: &str, open: usize, end: usize) -> Option<usize> {
    let b = src.as_bytes();
    let mut depth = 0i32;
    let mut i = open;
    while i < end {
        match b[i] {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn closure_edits(pair: &pest::iterators::Pair<Rule>, src: &str, edits: &mut Vec<Edit>) {
    let span = pair.as_span();
    // Prefix ends after the last of capture_list / once_kw / mut_kw, if any.
    let mut prefix_end = span.start();
    let mut return_type_present = false;
    for inner in pair.clone().into_inner() {
        match inner.as_rule() {
            Rule::capture_list | Rule::once_kw | Rule::mut_kw => {
                prefix_end = prefix_end.max(inner.as_span().end());
            }
            Rule::type_expr => return_type_present = true,
            _ => {}
        }
    }
    let Some(open) = first_paren(src, prefix_end, span.end()) else {
        return;
    };
    let Some(close) = match_paren(src, open, span.end()) else {
        return;
    };
    edits.push(Edit {
        start: open,
        end: open + 1,
        repl: "|",
    });
    edits.push(Edit {
        start: close,
        end: close + 1,
        repl: "|",
    });

    // The old grammar always has `->` after `)`. Keep it only if a return type
    // follows; otherwise drop `->` and one trailing space.
    if !return_type_present {
        let b = src.as_bytes();
        let mut i = close + 1;
        while i < span.end() && b[i].is_ascii_whitespace() {
            i += 1;
        }
        if src[i..span.end()].starts_with("->") {
            let mut del_end = i + 2;
            if b.get(del_end) == Some(&b' ') {
                del_end += 1;
            }
            edits.push(Edit {
                start: i,
                end: del_end,
                repl: "",
            });
        }
    }
}

fn fun_type_edits(pair: &pest::iterators::Pair<Rule>, src: &str, edits: &mut Vec<Edit>) {
    let span = pair.as_span();
    let mut prefix_end = span.start();
    for inner in pair.clone().into_inner() {
        if inner.as_rule() == Rule::fun_type_qualifier {
            prefix_end = prefix_end.max(inner.as_span().end());
        }
    }
    let Some(open) = first_paren(src, prefix_end, span.end()) else {
        return;
    };
    let Some(close) = match_paren(src, open, span.end()) else {
        return;
    };
    edits.push(Edit {
        start: open,
        end: open + 1,
        repl: "|",
    });
    edits.push(Edit {
        start: close,
        end: close + 1,
        repl: "|",
    });
}

fn splice(src: &str, edits: &[Edit]) -> String {
    let mut out = String::with_capacity(src.len() + edits.len());
    let mut last = 0;
    for e in edits {
        assert!(e.start >= last, "overlapping edits");
        out.push_str(&src[last..e.start]);
        out.push_str(e.repl);
        last = e.end;
    }
    out.push_str(&src[last..]);
    out
}

/// Rewrite Metel inside every `r#"…"#` / `r##"…"##` raw string in a Rust file.
/// A block that does not parse as a Metel `program` is left as-is.
fn rewrite_rs_raw_strings(src: &str) -> (String, usize, bool) {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    let mut total = 0usize;
    let mut in_rust_str = false;
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
                    out.push_str(&src[i..content_start]);
                    match edits_for(content) {
                        Ok(edits) if !edits.is_empty() => {
                            total += edits.len();
                            out.push_str(&splice(content, &edits));
                        }
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
    (out, total, false)
}

/// Rewrite Metel inside every column-0 ```` ```metel ```` fence in a Markdown/MDX
/// file. A block that does not parse as a Metel `program` is left as-is.
fn rewrite_md_metel_fences(src: &str) -> (String, usize, bool) {
    let mut out = String::with_capacity(src.len());
    let mut total = 0usize;
    let mut rest = src;
    while let Some(open_rel) = find_metel_fence_open(rest) {
        let after_open = &rest[open_rel..];
        let content_start = 1; // skip the newline that ends the ```metel line
        let Some(close_rel) = after_open[content_start..].find("\n```") else {
            break;
        };
        let content_end = content_start + close_rel + 1;
        let content = &after_open[content_start..content_end];
        out.push_str(&rest[..open_rel + content_start]);
        match edits_for(content) {
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

fn find_metel_fence_open(s: &str) -> Option<usize> {
    let mut search_from = 0;
    loop {
        let rel = s[search_from..].find("```metel")?;
        let abs = search_from + rel;
        let tail = &s[abs + "```metel".len()..];
        if let Some(nl) = tail.find('\n') {
            if abs == 0 || s.as_bytes()[abs - 1] == b'\n' {
                return Some(abs + "```metel".len() + nl);
            }
        }
        search_from = abs + 1;
    }
}
