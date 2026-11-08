//! RFC-0100 migration: the brace literal becomes a construction call.
//!
//! `Type { f = v }` becomes `Type(f = v)`, the shorthand `Type { x, y }` becomes `Type(x = x, y = y)`,
//! `Empty {}` becomes `Empty()`, and an enum struct-variant `Enum::Variant { f = v }` becomes
//! `Enum::Variant(f = v)`. Patterns keep their braces, and so do anonymous record literals.
//!
//! Like `walrus_migrate` and `assign_migrate`, this is a parser-driven rewriter that runs under the OLD
//! grammar (where `struct_literal` is an expression): it walks the concrete pest parse tree, so it
//! never mistakes a block, a record literal or a pattern for a construction, and it rewrites by byte
//! offset, never by text substitution.
//!
//! Usage:
//!   cargo run -p metel-frontend --example construct_migrate -- [--check] [--md | --rs] <path>...
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
        eprintln!("usage: construct_migrate [--check] <path>...");
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

/// The edits that migrate every struct literal in `src`, sorted by offset. A source that is not a
/// whole program (a documentation fragment) is parsed inside a wrapping `fun main`. `Err` for a source
/// that parses neither way under the old grammar.
pub fn edits_to_apply(src: &str) -> Result<Vec<Edit>, String> {
    match edits_for(src) {
        Ok(edits) => Ok(edits),
        Err(program_error) => {
            const PREFIX: &str = "fun main() {\n";
            let wrapped = format!("{PREFIX}{src}\n}}\n");
            match edits_for(&wrapped) {
                Ok(edits) => Ok(edits
                    .into_iter()
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
    for pair in pairs {
        walk(pair, src, &mut edits);
    }
    edits.sort_by_key(|e| (e.start, e.len));
    Ok(edits)
}

fn walk(pair: pest::iterators::Pair<Rule>, src: &str, edits: &mut Vec<Edit>) {
    if pair.as_rule() == Rule::struct_literal {
        migrate_literal(&pair, src, edits);
    }
    for inner in pair.into_inner() {
        walk(inner, src, edits);
    }
}

/// `struct_literal = { type_path ~ "{" ~ (field_init ~ ("," ~ field_init)* ~ ","?)? ~ "}" }`.
fn migrate_literal(pair: &pest::iterators::Pair<Rule>, src: &str, edits: &mut Vec<Edit>) {
    let span = pair.as_span();
    let Some(path) = pair
        .clone()
        .into_inner()
        .find(|p| p.as_rule() == Rule::type_path)
    else {
        return;
    };
    let after_path = path.as_span().end();
    let Some(open_rel) = src[after_path..span.end()].find('{') else {
        return;
    };
    let open = after_path + open_rel;
    let close = span.end() - 1;
    debug_assert_eq!(src.as_bytes()[close], b'}');
    // A call's `(` follows the type name directly: drop the whitespace the literal had before `{`.
    let name_end = path.as_span().start() + path.as_str().trim_end().len();
    if open > name_end {
        edits.push(Edit {
            start: name_end,
            len: open - name_end,
            insert: "",
        });
    }
    // `{` and `}` become the call's parentheses; same-line padding inside them is dropped.
    edits.push(Edit {
        start: open,
        len: 1,
        insert: "(",
    });
    let bytes = src.as_bytes();
    let mut after_open = open + 1;
    while after_open < close && matches!(bytes[after_open], b' ' | b'\t') {
        after_open += 1;
    }
    if after_open < close && !matches!(bytes[after_open], b'\n' | b'\r') && after_open > open + 1 {
        edits.push(Edit {
            start: open + 1,
            len: after_open - (open + 1),
            insert: "",
        });
    }
    let mut before_close = close;
    while before_close > open + 1 && matches!(bytes[before_close - 1], b' ' | b'\t') {
        before_close -= 1;
    }
    if before_close > open + 1
        && !matches!(bytes[before_close - 1], b'\n' | b'\r')
        && before_close < close
    {
        edits.push(Edit {
            start: before_close,
            len: close - before_close,
            insert: "",
        });
    }
    edits.push(Edit {
        start: close,
        len: 1,
        insert: ")",
    });
    // The shorthand `x` is the keyword argument `x = x`.
    for field in pair
        .clone()
        .into_inner()
        .filter(|p| p.as_rule() == Rule::field_init)
    {
        let mut parts = field.clone().into_inner();
        let name = parts.next();
        if parts.next().is_none()
            && let Some(name) = name
        {
            let text = name.as_str();
            let end = name.as_span().end();
            edits.push(Edit {
                start: end,
                len: 0,
                insert: Box::leak(format!(" = {text}").into_boxed_str()),
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
