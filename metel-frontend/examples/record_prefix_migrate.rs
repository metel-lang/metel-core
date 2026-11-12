//! RFC-0225 migration: every anonymous record opens with `.{`.
//!
//! The opening brace of an anonymous record literal, record pattern, record type, open record type and row
//! bound gets a dot: `{ .x = 1 }` becomes `.{ .x = 1 }`, `{ .x }` as a pattern becomes `.{ .x }`,
//! `{ .x: i64, ..R }` becomes `.{ .x: i64, ..R }`, and `{}` that the parser reads as an empty record becomes
//! `.{}` (a `{}` it reads as a block stays). A literal-row argument keeps `..{` (its whitespace, if any, is
//! removed), a whole-row negative bound keeps `!{`, and projections, struct and enum declarations, nominal
//! patterns and blocks are untouched. Nested records inside those forms still gain their own dot.
//!
//! Like `label_migrate`, this is a parser-driven rewriter that runs under the OLD grammar: it walks the
//! concrete pest parse tree and edits at byte offsets, never by text substitution, so the classification of
//! `{}` and of blocks comes from the old parser. It is removed in the commit that moves the grammar.
//!
//! Usage:
//!   cargo run -p metel-frontend --example record_prefix_migrate -- [--check] [--md | --rs] <path>...

use std::cell::RefCell;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use metel_frontend::pipeline::parsing::parser::MetelParser;
use metel_frontend::pipeline::parsing::parser::Rule;
use pest::Parser;

thread_local! {
    /// Problems the tool refuses to guess about: a comment in an introducer gap, an interpolation it cannot
    /// map back to the source. A file with any problem is not written, and the run fails.
    static PROBLEMS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
    static CURRENT: RefCell<String> = const { RefCell::new(String::new()) };
}

fn problem(msg: String) {
    let file = CURRENT.with(|c| c.borrow().clone());
    eprintln!("MANUAL {file}: {msg}");
    PROBLEMS.with(|p| p.borrow_mut().push(msg));
}

fn problem_count() -> usize {
    PROBLEMS.with(|p| p.borrow().len())
}

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let check = args.iter().any(|a| a == "--check");
    args.retain(|a| a != "--check");
    if args.is_empty() {
        eprintln!("usage: label_migrate [--check] <path>...");
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
    let mut manual_files = 0usize;
    for path in &files {
        let src = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("skip {}: {e}", path.display());
                continue;
            }
        };
        CURRENT.with(|c| *c.borrow_mut() = path.display().to_string());
        let problems_before = problem_count();
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
        if problem_count() > problems_before {
            manual_files += 1;
            continue; // never write a half-migrated file
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
        "{} file(s) scanned, {} {}, {} parse failure(s), {} file(s) need manual migration",
        files.len(),
        changed,
        if check { "would change" } else { "rewritten" },
        parse_failures,
        manual_files
    );
    if parse_failures > 0 || manual_files > 0 || (check && changed > 0) {
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
    let mut str_start = 0usize;
    while i < bytes.len() {
        if in_rust_str {
            if bytes[i] == b'\\' {
                let next = src[i + 1..].chars().next().map_or(0, char::len_utf8);
                out.push_str(&src[i..i + 1 + next]);
                i += 1 + next;
                continue;
            }
            if bytes[i] == b'"' {
                in_rust_str = false;
                if looks_like_old_record(&src[str_start..i]) {
                    problem(format!(
                        "an ordinary Rust string (byte {str_start}) holds an old-form record; migrate it by hand"
                    ));
                }
            }
            let ch = src[i..].chars().next().unwrap();
            out.push(ch);
            i += ch.len_utf8();
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
            str_start = i;
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

/// The edits that dot every label in `src`, sorted by offset. A source that is not a whole program (a
/// documentation fragment) is parsed inside a wrapping `fun main`.
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
    edits.sort_by_key(|e| e.start);
    edits.dedup_by_key(|e| e.start);
    Ok(edits)
}

/// Insert a dot before the `{` that opens each anonymous record form. `src` is the text the pairs were
/// parsed from, so that the gap between an introducer's tokens can be read.
fn walk(pair: pest::iterators::Pair<Rule>, src: &str, edits: &mut Vec<Edit>) {
    let rule = pair.as_rule();
    let opens_record = matches!(
        rule,
        Rule::record_lit
            | Rule::record_pattern
            | Rule::record_type
            | Rule::open_record_type
            | Rule::row_bound
    );
    if opens_record && pair.as_str().starts_with('{') {
        edits.push(Edit {
            start: pair.as_span().start(),
            len: 0,
            insert: ".",
        });
    }
    // A record inside a string interpolation `"${ ... }"`: the compiler parses each interpolation separately
    // (after unescaping), so the walk never sees it. Parse each balanced body on its own, through an offset
    // map back to the source, and edit there.
    if rule == Rule::string_lit {
        let start = pair.as_span().start();
        let text = pair.as_str();
        for (open, close) in interpolations(text) {
            let inner = &text[open + 2..close];
            let (unescaped, map) = unescape_mapped(inner);
            match MetelParser::parse(Rule::interp_expr_entry, &unescaped) {
                Ok(pairs) => {
                    let mut sub = Vec::new();
                    for p in pairs {
                        walk(p, &unescaped, &mut sub);
                    }
                    for e in sub {
                        let from = map[e.start];
                        let len = if e.len > 0 {
                            map[e.start + e.len] - from
                        } else {
                            0
                        };
                        edits.push(Edit {
                            start: start + open + 2 + from,
                            len,
                            insert: e.insert,
                        });
                    }
                }
                Err(_) if looks_like_old_record(inner) => problem(format!(
                    "an interpolation at byte {} holds an old-form record the tool cannot parse on its own",
                    start + open
                )),
                Err(_) => {}
            }
        }
    }
    // `..{ ... }`: the introducer is contiguous, and the record shape inside it takes no dot of its own.
    if rule == Rule::row_literal {
        let start = pair.as_span().start();
        let mut children = pair.clone().into_inner();
        if let Some(body) = children.next() {
            let brace = body.as_span().start();
            if brace > start + 2 {
                let gap = &src[start + 2..brace];
                if gap_is_blank(gap) {
                    edits.push(Edit {
                        start: start + 2,
                        len: brace - (start + 2),
                        insert: "",
                    });
                } else {
                    problem(format!(
                        "a comment between `..` and `{{` at byte {start}; make the introducer `..{{` by hand"
                    ));
                }
            }
            for inner in body.into_inner() {
                walk(inner, src, edits);
            }
        }
        return;
    }
    // `!{ ... }`: a whole-row negative bound keeps its introducer, contiguous.
    if rule == Rule::bound {
        let mut children = pair.clone().into_inner();
        let first = children.next();
        if let Some(bang) = first.filter(|f| f.as_rule() == Rule::bang) {
            if let Some(head) = children.next() {
                for inner in head.into_inner() {
                    if inner.as_rule() == Rule::row_bound {
                        let bang_end = bang.as_span().end();
                        let brace = inner.as_span().start();
                        if brace > bang_end {
                            let gap = &src[bang_end..brace];
                            if gap_is_blank(gap) {
                                edits.push(Edit {
                                    start: bang_end,
                                    len: brace - bang_end,
                                    insert: "",
                                });
                            } else {
                                problem(format!(
                                    "a comment between `!` and `{{` at byte {bang_end}; make the introducer `!{{` by hand"
                                ));
                            }
                        }
                        for entry in inner.into_inner() {
                            walk(entry, src, edits);
                        }
                    } else {
                        walk(inner, src, edits);
                    }
                }
            }
            return;
        }
    }
    for inner in pair.into_inner() {
        walk(inner, src, edits);
    }
}

/// Whether an ordinary Rust string's text holds a bare `{` followed by a dotted label: an old-form record
/// that the raw-string scanner does not rewrite. It is reported, not edited.
fn looks_like_old_record(text: &str) -> bool {
    // Only text that reads as Metel source: a diagnostic message that quotes a record is not an example.
    if !(text.contains("fun ") || text.contains("let ") || text.contains("struct ")) {
        return false;
    }
    let bytes = text.as_bytes();
    for (i, b) in bytes.iter().enumerate() {
        if *b != b'{' {
            continue;
        }
        if i > 0 && matches!(bytes[i - 1], b'.' | b'$' | b'!' | b'{' | b'}') {
            continue;
        }
        let rest = text[i + 1..].trim_start();
        let dotted = rest.starts_with("..") || {
            let mut cs = rest.chars();
            cs.next() == Some('.') && cs.next().is_some_and(|c| c.is_alphanumeric() || c == '_')
        };
        if dotted {
            return true;
        }
    }
    false
}

/// `Some(true)` when `gap` is only whitespace, `Some(false)` when it holds a comment.
fn gap_is_blank(gap: &str) -> bool {
    gap.trim().is_empty()
}

/// Apply the compiler's string unescape to an interpolation body, with a map from each byte of the result
/// back to its byte offset in the source text.
fn unescape_mapped(s: &str) -> (String, Vec<usize>) {
    let mut out = String::with_capacity(s.len());
    let mut map = Vec::with_capacity(s.len() + 1);
    let mut chars = s.char_indices().peekable();
    let push = |out: &mut String, map: &mut Vec<usize>, ch: char, at: usize| {
        out.push(ch);
        for _ in 0..ch.len_utf8() {
            map.push(at);
        }
    };
    while let Some((at, c)) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some((_, 'n')) => push(&mut out, &mut map, '\n', at),
                Some((_, 't')) => push(&mut out, &mut map, '\t', at),
                Some((_, 'r')) => push(&mut out, &mut map, '\r', at),
                Some((_, '\\')) | None => push(&mut out, &mut map, '\\', at),
                Some((_, '"')) => push(&mut out, &mut map, '"', at),
                Some((_, '$')) => push(&mut out, &mut map, '$', at),
                Some((_, c2)) => {
                    push(&mut out, &mut map, '\\', at);
                    push(&mut out, &mut map, c2, at + 1);
                }
            }
        } else {
            push(&mut out, &mut map, c, at);
        }
    }
    map.push(s.len());
    (out, map)
}

/// Byte ranges of the `${` and matching `}` of each top-level interpolation in a string literal's text,
/// skipping braces inside nested string literals.
fn interpolations(text: &str) -> Vec<(usize, usize)> {
    let bytes = text.as_bytes();
    let mut out = Vec::new();
    let mut i = 1; // past the opening quote
    while i < bytes.len() {
        if bytes[i] == b'\\' {
            i += 2;
            continue;
        }
        if bytes[i] == b'$' && bytes.get(i + 1) == Some(&b'{') {
            let open = i;
            let mut depth = 1;
            let mut j = i + 2;
            let mut in_str = false;
            while j < bytes.len() && depth > 0 {
                match bytes[j] {
                    b'\\' => j += 1, // an escaped character, inside a nested string or not
                    b'"' => in_str = !in_str,
                    b'{' if !in_str => depth += 1,
                    b'}' if !in_str => depth -= 1,
                    _ => {}
                }
                j += 1;
            }
            if depth == 0 {
                out.push((open, j - 1));
                i = j;
                continue;
            }
            problem(format!(
                "an unterminated or unbalanced `${{` interpolation at byte {open}; check it by hand"
            ));
        }
        i += 1;
    }
    out
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
