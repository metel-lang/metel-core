//! RFC-0100 section 3 migration (metel-core#2200): rewrite every nominal brace literal
//! that sits outside an `extend` block of its own type into the equivalent call-form
//! construction — `Point { x = 1, y }` becomes `Point(x = 1, y = y)`, and
//! `Shape::Circle { radius = r }` becomes `Shape::Circle(radius = r)`.
//!
//! A brace literal stays as written when it is lexically inside an `extend` block whose
//! target is the literal's own type: its path is `Self`/`Self::Variant`, ends in the
//! target's name (a struct, possibly module-qualified), or names a variant of it
//! (`Target::Variant`). That is the only place the literal remains legal.
//!
//! AST-driven, like `walrus_migrate`: it walks the pest parse tree and splices at exact
//! byte offsets — the literal's braces and its shorthand fields — never a text
//! substitution. A file (or Markdown fence, or Rust raw string) that does not parse as a
//! Metel `program` is left untouched.
//!
//! Usage:
//!   cargo run -p metel-frontend --example construct_migrate -- [--check] [--md|--rs] <path>...
//!
//! `<path>` may be a file or a directory (walked recursively for *.mtl, or *.md/*.mdx
//! with `--md`, or *.rs with `--rs`). With `--check`, prints what would change and exits
//! non-zero if anything would, without writing.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use metel_frontend::pipeline::parsing::parser::MetelParser;
use metel_frontend::pipeline::parsing::parser::Rule;
use pest::Parser;
use pest::iterators::Pair;

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let check = args.iter().any(|a| a == "--check");
    let rs = args.iter().any(|a| a == "--rs");
    let md = args.iter().any(|a| a == "--md");
    args.retain(|a| a != "--check" && a != "--rs" && a != "--md");
    if args.is_empty() {
        eprintln!("usage: construct_migrate [--check] [--md|--rs] <path>...");
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
    let mut sites = 0usize;
    let mut parse_failures = 0usize;
    for path in &files {
        let Ok(src) = fs::read_to_string(path) else {
            eprintln!("skip {}: unreadable", path.display());
            continue;
        };
        let (new_src, n_sites) = if md {
            rewrite_md_metel_fences(&src)
        } else if rs {
            rewrite_rs_raw_strings(&src)
        } else {
            match rewrite_program(&src) {
                Ok(r) => r,
                Err(e) => {
                    eprintln!(
                        "PARSE-FAIL {}: {}",
                        path.display(),
                        e.lines().next().unwrap_or("")
                    );
                    parse_failures += 1;
                    continue;
                }
            }
        };
        if n_sites == 0 {
            continue;
        }
        changed += 1;
        sites += n_sites;
        if check {
            println!("{}  ({n_sites} site(s))", path.display());
        } else {
            fs::write(path, new_src).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        }
    }

    eprintln!(
        "{} file(s) scanned, {} {} ({} literal(s)), {} parse failure(s)",
        files.len(),
        changed,
        if check { "would change" } else { "rewritten" },
        sites,
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

/// One splice: replace `src[start..end]` with `text` (an insertion when `start == end`).
struct Edit {
    start: usize,
    end: usize,
    text: String,
}

/// Rewrite one whole Metel program. Returns the new source and the number of literals
/// rewritten.
pub fn rewrite_program(src: &str) -> Result<(String, usize), String> {
    let pairs = MetelParser::parse(Rule::program, src).map_err(|e| e.to_string())?;
    let mut edits = Vec::new();
    let mut count = 0usize;
    for pair in pairs {
        walk(pair, src, None, &mut edits, &mut count);
    }
    edits.sort_by_key(|e| (e.start, e.end));
    let mut out = String::with_capacity(src.len() + edits.len() * 4);
    let mut last = 0;
    for e in &edits {
        out.push_str(&src[last..e.start]);
        out.push_str(&e.text);
        last = e.end;
    }
    out.push_str(&src[last..]);
    Ok((out, count))
}

fn walk(
    pair: Pair<Rule>,
    src: &str,
    target: Option<&str>,
    edits: &mut Vec<Edit>,
    count: &mut usize,
) {
    match pair.as_rule() {
        Rule::extend_impl_block => {
            let name = extend_target_name(&pair);
            for inner in pair.into_inner() {
                walk(inner, src, name.as_deref(), edits, count);
            }
            return;
        }
        Rule::struct_literal => {
            // A field-less literal (`Empty {}`, `Flag::On {}`) is privileged like any other and
            // becomes `Empty()` / `Flag::On()`.
            if !is_own_type_literal(&pair, target) {
                rewrite_literal(&pair, src, edits);
                *count += 1;
            }
        }
        _ => {}
    }
    for inner in pair.into_inner() {
        walk(inner, src, target, edits, count);
    }
}

/// The bare name of an `extend` block's target: `extend<T> Pair<T>: Show { .. }` gives
/// `Pair`. `None` for a row-tailed record target, which has no nominal brace literal.
fn extend_target_name(pair: &Pair<Rule>) -> Option<String> {
    let target = pair
        .clone()
        .into_inner()
        .find(|p| matches!(p.as_rule(), Rule::type_expr | Rule::open_record_type))?;
    if target.as_rule() != Rule::type_expr {
        return None;
    }
    let text = target.as_str();
    let base = text.split('<').next().unwrap_or(text).trim();
    let last = base.rsplit("::").next().unwrap_or(base).trim();
    (!last.is_empty()).then(|| last.to_string())
}

fn literal_path(pair: &Pair<Rule>) -> Vec<String> {
    pair.clone()
        .into_inner()
        .find(|p| p.as_rule() == Rule::type_path)
        .map(|p| {
            p.as_str()
                .split("::")
                .map(|s| s.trim().to_string())
                .collect()
        })
        .unwrap_or_default()
}

fn is_own_type_literal(pair: &Pair<Rule>, target: Option<&str>) -> bool {
    let Some(target) = target else {
        return false;
    };
    let path = literal_path(pair);
    let Some(last) = path.last() else {
        return false;
    };
    let names_target = |seg: &str| seg == target || seg == "Self";
    // `Self { .. }`, `Point { .. }`, `geo::Point { .. }`: the target struct itself.
    // `Self::Circle { .. }`, `Shape::Circle { .. }`: a variant of the target enum.
    names_target(last) || (path.len() >= 2 && names_target(&path[path.len() - 2]))
}

/// Splice `Path { a = x, b }` into `Path(a = x, b = b)`: the opening brace (and the
/// whitespace between it and the path) becomes `(`, the closing brace becomes `)`, a
/// single padding space just inside single-line braces is dropped, and each shorthand
/// field `b` gains its ` = b`.
fn rewrite_literal(pair: &Pair<Rule>, src: &str, edits: &mut Vec<Edit>) {
    let span = pair.as_span();
    let path_end = pair
        .clone()
        .into_inner()
        .find(|p| p.as_rule() == Rule::type_path)
        // pest folds the whitespace its `("::" ~ ident)*` repetition skipped into the
        // span, so a single-segment path's span runs up to the brace; trim it.
        .map_or(span.start(), |p| {
            p.as_span().start() + p.as_str().trim_end().len()
        });
    let bytes = src.as_bytes();
    let Some(open) = src[path_end..span.end()].find('{').map(|r| path_end + r) else {
        return;
    };
    let close = span.end() - 1;
    debug_assert_eq!(bytes[close], b'}');
    let single_line = !src[open..close].contains('\n');

    let mut open_end = open + 1;
    let mut close_start = close;
    if single_line {
        while open_end < close && bytes[open_end] == b' ' {
            open_end += 1;
        }
        while close_start > open_end && bytes[close_start - 1] == b' ' {
            close_start -= 1;
        }
    }
    edits.push(Edit {
        start: path_end,
        end: open_end,
        text: "(".into(),
    });
    edits.push(Edit {
        start: close_start,
        end: close + 1,
        text: ")".into(),
    });

    for field in pair
        .clone()
        .into_inner()
        .filter(|p| p.as_rule() == Rule::struct_field_init)
    {
        let mut inner = field.clone().into_inner();
        let Some(name) = inner.next() else { continue };
        if inner.next().is_none() {
            let end = name.as_span().end();
            edits.push(Edit {
                start: end,
                end,
                text: format!(" = {}", name.as_str()),
            });
        }
    }
}

/// Rewrite inside every ```` ```metel ```` fence of a Markdown/MDX file. A fence that does
/// not parse as a Metel `program` (a fragment, or deliberately invalid code) is left as-is.
fn rewrite_md_metel_fences(src: &str) -> (String, usize) {
    let mut out = String::with_capacity(src.len());
    let mut total = 0usize;
    let mut rest = src;
    while let Some(open_rel) = find_metel_fence_open(rest) {
        let after_open = &rest[open_rel..];
        let content_start = 1;
        let Some(close_rel) = after_open[content_start..].find("\n```") else {
            break;
        };
        let content_end = content_start + close_rel + 1;
        let content = &after_open[content_start..content_end];
        out.push_str(&rest[..open_rel + content_start]);
        match rewrite_program(content) {
            Ok((new, n)) if n > 0 => {
                total += n;
                out.push_str(&new);
            }
            _ => out.push_str(content),
        }
        rest = &after_open[content_end..];
    }
    out.push_str(rest);
    (out, total)
}

fn find_metel_fence_open(s: &str) -> Option<usize> {
    let mut search_from = 0;
    loop {
        let rel = s[search_from..].find("```metel")?;
        let abs = search_from + rel;
        let tail = &s[abs + "```metel".len()..];
        if let Some(nl) = tail.find('\n')
            && (abs == 0 || s.as_bytes()[abs - 1] == b'\n')
        {
            return Some(abs + "```metel".len() + nl);
        }
        search_from = abs + 1;
    }
}

/// Rewrite inside every `r#"..."#`-style raw string of a Rust file whose content parses
/// as a Metel `program`; everything else is left exactly as-is.
fn rewrite_rs_raw_strings(src: &str) -> (String, usize) {
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
            // Whole characters, not bytes: pushing a byte as a `char` would re-encode a multi-byte
            // UTF-8 character as several Latin-1 ones.
            let ch = src[i..].chars().next().unwrap();
            out.push(ch);
            i += ch.len_utf8();
            continue;
        }
        let at_boundary = i == 0 || !(bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_');
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
                    match rewrite_program(content) {
                        Ok((new, n)) if n > 0 => {
                            total += n;
                            out.push_str(&new);
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
    (out, total)
}
