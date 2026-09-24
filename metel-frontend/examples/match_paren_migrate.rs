//! RFC-0156 migration: parenthesize every `match` scrutinee — `match x { … }`
//! becomes `match (x) { … }` — leaving a scrutinee that is *already* a single
//! balanced parenthesized group (`match (a, b) { … }`, `match (x) { … }`,
//! `match () { … }`) untouched.
//!
//! Run under the OLD grammar (still `"match" ~ expr ~ "{"`). It walks the
//! concrete pest parse tree, and for each `match_expr` takes the byte span of
//! the scrutinee sub-expression; if that span's source is not already a single
//! balanced `( … )` / `()`, it splices a `(` at the span start and a `)` at the
//! span end. Never a text substitution, and double-wrapping is impossible
//! because the balance check recognises an existing wrap.
//!
//! Usage:
//!   cargo run -p metel-frontend --example match_paren_migrate -- [--check] [--rs|--md] <path>...
//!
//! `<path>` may be a file or a directory (walked recursively). Default targets
//! `*.mtl`; `--rs` rewrites Metel inside `r#"…"#` raw strings in `*.rs`; `--md`
//! rewrites Metel inside column-0 ```` ```metel ```` fences in `*.md`/`*.mdx`.
//! With `--check`, prints what would change and exits non-zero if anything would.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use metel_frontend::pipeline::parsing::parser::MetelParser;
use metel_frontend::pipeline::parsing::parser::Rule;
use pest::Parser;

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let check = args.iter().any(|a| a == "--check");
    let rs = args.iter().any(|a| a == "--rs");
    let md = args.iter().any(|a| a == "--md");
    args.retain(|a| a != "--check" && a != "--rs" && a != "--md");
    if args.is_empty() {
        eprintln!("usage: match_paren_migrate [--check] [--rs|--md] <path>...");
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
            match scrutinee_wraps(&src) {
                Ok(w) => (splice(&src, &w), w.len(), false),
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
            println!("{}  ({n_sites} scrutinee(s))", path.display());
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

/// Rewrite Metel `match` scrutinees inside every `r#"…"#` / `r##"…"##` raw string
/// literal in a Rust file. Non-raw strings and Rust code outside them are
/// untouched. A raw-string block whose content does not parse as a Metel
/// `program` is skipped.
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
                    match scrutinee_wraps(content) {
                        Ok(w) if !w.is_empty() => {
                            total += w.len();
                            out.push_str(&splice(content, &w));
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

/// Rewrite Metel `match` scrutinees inside every column-0 ```` ```metel ```` fenced
/// block in a Markdown/MDX file. A block that does not parse as a Metel `program`
/// (a fragment, or deliberately-invalid syntax) is left as-is.
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
        let content_end = content_start + close_rel + 1; // include the newline before ```
        let content = &after_open[content_start..content_end];
        out.push_str(&rest[..open_rel + content_start]);
        match scrutinee_wraps(content) {
            Ok(w) if !w.is_empty() => {
                total += w.len();
                out.push_str(&splice(content, &w));
            }
            _ => out.push_str(content),
        }
        rest = &after_open[content_end..];
    }
    out.push_str(rest);
    (out, total, false)
}

/// Offset of the newline that terminates the next column-0 ```` ```metel ```` fence line.
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

/// A splice: insert `text` at byte offset `at` (a point insertion, never a
/// replacement).
struct Ins {
    at: usize,
    text: &'static str,
}

/// For every `match_expr` in `src` (parsed under the OLD grammar), the pair of
/// `(` / `)` insertions needed to parenthesize its scrutinee — empty when the
/// scrutinee is already a single balanced parenthesized group. Sorted ascending.
fn scrutinee_wraps(src: &str) -> Result<Vec<Ins>, String> {
    let pairs = MetelParser::parse(Rule::program, src).map_err(|e| e.to_string())?;
    let mut ins = Vec::new();
    for pair in pairs {
        walk(pair, src, &mut ins);
    }
    ins.sort_by_key(|i| i.at);
    Ok(ins)
}

fn walk(pair: pest::iterators::Pair<Rule>, src: &str, ins: &mut Vec<Ins>) {
    if pair.as_rule() == Rule::match_expr {
        if let Some(scrut) = pair.clone().into_inner().next() {
            let sp = scrut.as_span();
            let b = src.as_bytes();
            // pest can fold the implicit whitespace between `expr` and `"{"` into
            // the scrutinee span; trim it so `)` lands tight against the last
            // real token (and `(` against the first).
            let mut start = sp.start();
            let mut end = sp.end();
            while start < end && b[start].is_ascii_whitespace() {
                start += 1;
            }
            while end > start && b[end - 1].is_ascii_whitespace() {
                end -= 1;
            }
            if !is_single_balanced_paren_group(&src[start..end]) {
                ins.push(Ins {
                    at: start,
                    text: "(",
                });
                ins.push(Ins { at: end, text: ")" });
            }
        }
    }
    for inner in pair.into_inner() {
        walk(inner, src, ins);
    }
}

/// True when `s`, trimmed, is exactly one parenthesised group: it starts with
/// `(`, and the `)` that matches that opening `(` is its final character. `()`
/// qualifies; `(x).f` and `(a) + (b)` do not (the first `)` is not the last
/// char). String and char literals are skipped so a `)` inside `")"` never
/// counts.
fn is_single_balanced_paren_group(s: &str) -> bool {
    let t = s.trim();
    let b = t.as_bytes();
    if b.first() != Some(&b'(') {
        return false;
    }
    let mut depth = 0i32;
    let mut in_str: Option<u8> = None;
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if let Some(q) = in_str {
            if c == b'\\' {
                i += 2;
                continue;
            }
            if c == q {
                in_str = None;
            }
            i += 1;
            continue;
        }
        match c {
            b'"' | b'\'' => in_str = Some(c),
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return i == b.len() - 1;
                }
            }
            _ => {}
        }
        i += 1;
    }
    false
}

fn splice(src: &str, ins: &[Ins]) -> String {
    let mut out = String::with_capacity(src.len() + ins.len());
    let mut last = 0;
    for i in ins {
        out.push_str(&src[last..i.at]);
        out.push_str(i.text);
        last = i.at;
    }
    out.push_str(&src[last..]);
    out
}
