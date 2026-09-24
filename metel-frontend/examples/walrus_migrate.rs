//! RFC-0136 migration: rewrite the `=` separator to `:=` in the four kept-binding
//! grammar sites — `let_decl`, `let_mut_decl`, `assoc_type_def`, and `assign_op`'s
//! plain-`=` alternative — leaving `field_init`, `assoc_binding`, `keyword_arg`,
//! `==`, and the compound assignment operators untouched.
//!
//! This is an AST-driven rewriter, run under the OLD grammar (still `=`), per
//! RFC-0136 Open Questions #4. It walks the concrete pest parse tree, finds the
//! byte span of each `=` token in a target rule, and splices `:=` at those
//! offsets — never a text substitution.
//!
//! Usage:
//!   cargo run -p metel-frontend --example walrus_migrate -- [--check] <path>...
//!
//! `<path>` may be a file or a directory (walked recursively for *.mtl). With
//! `--check`, prints what would change and exits non-zero if anything would,
//! without writing.

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
        eprintln!("usage: walrus_migrate [--check] <path>...");
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
            match eq_offsets_to_rewrite(&src) {
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
                    match eq_offsets_to_rewrite(content) {
                        Ok(offsets) if !offsets.is_empty() => {
                            total_sites += offsets.len();
                            out.push_str(&splice(content, &offsets));
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
        match eq_offsets_to_rewrite(content) {
            Ok(offsets) if !offsets.is_empty() => {
                total += offsets.len();
                out.push_str(&splice(content, &offsets));
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

/// Byte offsets of every `=` token, in a target rule, that must become `:=`.
/// Sorted ascending, de-duplicated.
pub fn eq_offsets_to_rewrite(src: &str) -> Result<Vec<usize>, String> {
    let pairs = MetelParser::parse(Rule::program, src).map_err(|e| e.to_string())?;
    let mut offsets = Vec::new();
    for pair in pairs {
        walk(pair, &mut offsets);
    }
    offsets.sort_unstable();
    offsets.dedup();
    Ok(offsets)
}

fn walk(pair: pest::iterators::Pair<Rule>, offsets: &mut Vec<usize>) {
    match pair.as_rule() {
        // `let NAME [: T] = expr ;` and `[let] var NAME [: T] = expr ;`
        // `type NAME = type_expr ;`
        Rule::let_decl | Rule::let_mut_decl | Rule::assoc_type_def => {
            let span = pair.as_span();
            if let Some(rel) = find_bare_eq(span.as_str()) {
                offsets.push(span.start() + rel);
            }
        }
        // `assign_op` is `+= | -= | *= | /= | %= | ("=" ~ !"=")`. Only the last
        // alternative — a lone `=` — moves. pest folds the trailing implicit
        // whitespace of `"=" ~ !"="` into the span, so it reads as `"= "`; the
        // `=` is always the first byte.
        Rule::assign_op => {
            let s = pair.as_span();
            if s.as_str().trim_end() == "=" {
                offsets.push(s.start());
            }
        }
        _ => {}
    }
    for inner in pair.into_inner() {
        walk(inner, offsets);
    }
}

/// The relative offset of the first `=` that is not part of `==`, `<=`, `>=`,
/// `!=`, `:=`, `+=`, `-=`, `*=`, `/=`, `%=`, and is not inside a string or char
/// literal. For `let`/`var`/`type` the initializer `=` is always the first such
/// token (the LHS is `NAME` or `NAME: type_expr`, and a `type_expr` never
/// contains a bare `=` — `assoc_binding`'s `=` lives in a `named_type`'s
/// `type_args`, which the LHS type annotation cannot reach without an unbalanced
/// `<`).
fn find_bare_eq(s: &str) -> Option<usize> {
    let b = s.as_bytes();
    let mut i = 0;
    let mut in_str: Option<u8> = None;
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
            b'=' => {
                let prev = if i > 0 { b[i - 1] } else { 0 };
                let next = if i + 1 < b.len() { b[i + 1] } else { 0 };
                if next != b'='
                    && !matches!(
                        prev,
                        b'=' | b'<' | b'>' | b'!' | b':' | b'+' | b'-' | b'*' | b'/' | b'%'
                    )
                {
                    return Some(i);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn splice(src: &str, eq_offsets: &[usize]) -> String {
    let mut out = String::with_capacity(src.len() + eq_offsets.len());
    let mut last = 0;
    for &off in eq_offsets {
        out.push_str(&src[last..off]);
        out.push_str(":="); // replaces the single `=` byte at `off`
        last = off + 1;
    }
    out.push_str(&src[last..]);
    out
}
