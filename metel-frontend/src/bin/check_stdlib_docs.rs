//! metel-core#718: checks `docs/reference/spec/runtime.md`'s builtin/method
//! tables against `stdlib/*.mtl`'s real declarations, in both directions --
//! a documented row with no matching declaration (a phantom, #717's
//! `string_concat`), and a real public declaration missing from its table,
//! both fail. Also checks each row's *signature* renders identically to the
//! real declaration's, computed the same way the doc's own convention
//! already writes it (#714's `string_len` bug: the native exists, the
//! method exists, only the *documented calling form* -- free function vs.
//! method -- was fictional; a name-only check would have missed it).
//!
//! This is the "cheaper first step" #718 itself names as an acceptable
//! alternative to full table generation: `stdlib/*.mtl` has no structured
//! place for the prose "Description" column to come from (most native
//! declarations have no doc comment at all), so generating the tables
//! wholesale would mean inventing descriptions from nothing or authoring a
//! large per-declaration sidecar. A targeted correspondence check gets the
//! actual acceptance criterion -- no more `string_len`/`string_concat`-shaped
//! bugs -- without that cost.
//!
//! Scope is deliberately narrow, not "every public declaration everywhere":
//! `stdlib/core.mtl` has dozens of near-identical numeric `From<X>` impls
//! documented only narratively (Built-in Aspects), never as an exhaustive
//! per-pair table -- a blanket completeness sweep would flag all of them as
//! "undocumented." Each checked surface below names exactly which
//! `extend`/aspect block backs which table, the same judgment call
//! `grammar-doc.toml` makes explicit per-rule for #720's grammar generation.
//!
//! Array Methods is not checked: `T[]::len` is a receiver-shape pattern
//! method registered directly in Rust (`array_method_scheme_variants_for`),
//! not a `stdlib/*.mtl` declaration -- nothing here to parse it against.
//!
//! Usage: `cargo run --bin check_stdlib_docs` from `metel-frontend/`.
//! Always read-only (unlike `gen_grammar`, nothing here regenerates
//! `runtime.md`) -- a failure names the mismatch and exits non-zero.

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::ExitCode;

use metel_frontend::data::ast::{Decl, FunDecl, ImplBlock, ReceiverKind, TypeExpr, Visibility};
use metel_frontend::pipeline::parsing::parser;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("metel-frontend has a parent directory")
        .to_path_buf()
}

fn stdlib_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("stdlib")
        .join(name)
}

fn runtime_md_path() -> PathBuf {
    workspace_root().join("docs/reference/spec/runtime.md")
}

fn parse_stdlib(file: &str) -> metel_frontend::data::ast::Program {
    let path = stdlib_path(file);
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("reading {file}: {e}"));
    parser::parse(&text, file).unwrap_or_else(|e| panic!("parsing {file}: {e}"))
}

/// One real declaration, reduced to exactly what the doc's own signature
/// convention renders: whether the receiver becomes a leading `&var self`
/// (only `RefMut` -- `self`/`&self` both render receiver-less, matching
/// e.g. `.yolo()` -> `() -> T` and `.get(i)` -> `(i64) -> Perhaps<T>` in the
/// existing table), the non-receiver params (with names, for the one table
/// that shows them), the return type, and any method-level (not
/// receiver-type-level) generics.
struct RealFn {
    name: String,
    generics: Vec<String>,
    receiver: Option<ReceiverKind>,
    params: Vec<(String, TypeExpr)>,
    return_type: Option<TypeExpr>,
}

fn render_type(t: &TypeExpr) -> String {
    match t {
        // RFC-0078's `!` and the plain `Never` identifier lower to the exact
        // same AST node (grammar.pest's own never_type comment says so) --
        // the doc always spells it `!`, so that's what's rendered here
        // regardless of which the source used.
        TypeExpr::Named(name, args) if name == "Never" && args.is_empty() => "!".to_string(),
        TypeExpr::Named(name, args) if args.is_empty() => name.clone(),
        TypeExpr::Named(name, args) => {
            format!(
                "{name}<{}>",
                args.iter().map(render_type).collect::<Vec<_>>().join(", ")
            )
        }
        TypeExpr::Unit => "()".to_string(),
        TypeExpr::Tuple(items) => {
            format!(
                "({})",
                items.iter().map(render_type).collect::<Vec<_>>().join(", ")
            )
        }
        TypeExpr::Array(inner) => format!("{}[]", render_type(inner)),
        TypeExpr::SizedArray(inner, n) => format!("[{}; {n}]", render_type(inner)),
        TypeExpr::Reference(inner) => format!("&{}", render_type(inner)),
        TypeExpr::MutReference(inner) => format!("&var {}", render_type(inner)),
        // The doc's own convention for a function-type parameter uses
        // ordinary parens (`(T) -> U`), not the real `|T| -> U` written-type
        // syntax (RFC-0154) -- e.g. `.map(f)`'s documented signature is
        // `<U>((T) -> U) -> Perhaps<U>`. Matched here, not the literal
        // source spelling, since that's what a correct row actually reads.
        TypeExpr::Fun {
            params,
            return_type,
            ..
        } => {
            let p = params
                .iter()
                .map(render_type)
                .collect::<Vec<_>>()
                .join(", ");
            match return_type {
                Some(rt) => format!("({p}) -> {}", render_type(rt)),
                None => format!("({p})"),
            }
        }
        other => format!("{other:?}"),
    }
}

/// `include_names`: only the "Built-in Functions" table spells
/// out `(cond: boolean)`; every method table in runtime.md is type-only
/// (`(i64) -> Perhaps<T>`) -- a real, if inconsistent, distinction in the
/// hand-written doc today, matched here rather than judged.
fn render_sig(f: &RealFn, include_names: bool) -> String {
    let mut out = String::new();
    if !f.generics.is_empty() {
        out.push('<');
        out.push_str(&f.generics.join(", "));
        out.push('>');
    }
    out.push('(');
    let mut parts = Vec::new();
    if matches!(&f.receiver, Some(ReceiverKind::RefMut)) {
        parts.push("&var self".to_string());
    }
    parts.extend(f.params.iter().map(|(name, ty)| {
        if include_names {
            format!("{name}: {}", render_type(ty))
        } else {
            render_type(ty)
        }
    }));
    out.push_str(&parts.join(", "));
    out.push(')');
    // A `-> ()` explicit source return and no `->` at all both mean "no
    // return value" to the doc's own convention (`.push(x)` -> `(&var
    // self, T)`, no arrow, and `print<T>(x: T) -> ()` -> `<T>(v: T)`, also
    // no arrow) -- normalized identically here.
    match &f.return_type {
        Some(TypeExpr::Unit) | None => {}
        Some(rt) => {
            out.push_str(" -> ");
            out.push_str(&render_type(rt));
        }
    }
    out
}

fn fun_to_real(f: &FunDecl) -> RealFn {
    let (receiver, params): (Option<ReceiverKind>, Vec<(String, TypeExpr)>) =
        match f.params.split_first() {
            Some((first, rest)) if first.receiver.is_some() => (
                first.receiver.clone(),
                rest.iter()
                    .map(|p| {
                        (
                            p.name.clone(),
                            p.type_ann.clone().expect("non-receiver param has a type"),
                        )
                    })
                    .collect(),
            ),
            _ => (
                None,
                f.params
                    .iter()
                    .map(|p| {
                        (
                            p.name.clone(),
                            p.type_ann.clone().expect("non-receiver param has a type"),
                        )
                    })
                    .collect(),
            ),
        };
    RealFn {
        name: f.name.clone(),
        generics: f.generics.iter().map(|g| g.name.clone()).collect(),
        receiver,
        params,
        return_type: f.return_type.clone(),
    }
}

/// Every public `fun` directly in `decls` (top level -- not inside any
/// `extend`/`aspect` block).
fn top_level_public(decls: &[Decl]) -> Vec<RealFn> {
    decls
        .iter()
        .filter_map(|d| match d {
            Decl::Fun(f) if f.visibility == Visibility::Public => Some(fun_to_real(f)),
            _ => None,
        })
        .collect()
}

/// Every method inside `extend <type_name> { ... }` (no aspect --
/// `aspect_name.is_none()`) or, when `aspect_name` is `Some`, inside
/// `extend <type_name>: <aspect_name> { ... }` specifically. Not filtered
/// by `Visibility` -- `stdlib/core.mtl`'s native methods (`.len()`,
/// `.push()`, ...) carry no `public` keyword at all despite being exactly
/// the language's own public surface (only the free-standing ergonomics
/// methods added later, `map`/`filter`/`fold`/`find`/`concat`, use
/// `public fun`) -- visibility on an extend-block method isn't a reliable
/// signal here the way it is for a top-level declaration.
fn extend_methods(decls: &[Decl], type_name: &str, aspect_name: Option<&str>) -> Vec<RealFn> {
    decls
        .iter()
        .filter_map(|d| match d {
            Decl::Impl(ImplBlock {
                target_type: TypeExpr::Named(name, _),
                aspect_name: a,
                methods,
                ..
            }) if name == type_name && a.as_deref() == aspect_name => {
                Some(methods.iter().map(fun_to_real))
            }
            _ => None,
        })
        .flatten()
        .collect()
}

/// One row parsed out of a runtime.md table: the callable name (stripped of
/// its `.`/`Type::` prefix and argument-placeholder parens) and the
/// signature column's literal text.
struct DocRow {
    name: String,
    signature: String,
}

/// Every markdown pipe-table found within the section headed `heading`
/// (from that `#`-line to the next `#`-line at any level), as a list of
/// tables in source order -- a section can hold more than one table
/// (`## String Methods` has an instance-method table and a separate
/// `Associated function` table for the static `String::join`; `## Core Sum
/// Types` has one table for `Perhaps<T>` and one for `Result<T, E>`, with
/// no sub-heading between them at all, just a bold prose line). A blank
/// line ends whatever table is in progress so the next pipe-line-run is
/// treated as a fresh header + separator, not a data row of the previous
/// table -- without this, a second table's own header row reads as a
/// garbage data row of the first.
fn parse_doc_tables(text: &str, heading: &str) -> Vec<Vec<DocRow>> {
    let mut tables: Vec<Vec<DocRow>> = Vec::new();
    let mut in_section = false;
    // None: between tables / before any table's header has been seen.
    // Some(false): saw a header row, waiting for its separator row.
    // Some(true): past the separator, collecting data rows.
    let mut table_state: Option<bool> = None;
    for line in text.lines() {
        if line.trim_start().starts_with('#') {
            let text = line.trim_start_matches('#').trim().replace('\\', "");
            in_section = text == heading;
            table_state = None;
            continue;
        }
        if !in_section {
            continue;
        }
        let trimmed = line.trim();
        if !trimmed.starts_with('|') {
            table_state = None; // blank/prose line: any table in progress has ended
            continue;
        }
        if trimmed.chars().all(|c| "|-: ".contains(c)) {
            if table_state == Some(false) {
                table_state = Some(true);
            }
            continue;
        }
        match table_state {
            None => {
                // A fresh header row -- start a new table.
                tables.push(Vec::new());
                table_state = Some(false);
            }
            Some(false) => {} // a second header-shaped line before its separator: ignore
            Some(true) => {
                let cols: Vec<&str> = trimmed
                    .trim_matches('|')
                    .split('|')
                    .map(str::trim)
                    .collect();
                if cols.len() < 2 {
                    continue;
                }
                // Column 1 is e.g. "`.get(i)`", "`String::join(parts, sep)`",
                // "[`u32::from(c)`](#anchor)" -- strip markdown link/code
                // fencing, then take the identifier between the last
                // `.`/`::` and the `(`.
                let raw = cols[0]
                    .trim_start_matches('[')
                    .split(']')
                    .next()
                    .unwrap_or(cols[0]);
                let raw = raw.trim_matches('`');
                let before_paren = raw.split('(').next().unwrap_or(raw);
                let name = before_paren
                    .rsplit("::")
                    .next()
                    .unwrap_or(before_paren)
                    .trim_start_matches('.');
                if name.is_empty() {
                    continue;
                }
                let signature = cols[1].trim_matches('`').to_string();
                tables
                    .last_mut()
                    .expect("a data row implies its table was already pushed")
                    .push(DocRow {
                        name: name.to_string(),
                        signature,
                    });
            }
        }
    }
    tables
}

struct Surface {
    /// The heading in runtime.md whose table(s) this checks -- compared
    /// with markdown escaping (`\<`/`\>`) stripped, so `"List<T>"` matches
    /// a real `## List\<T\>` heading.
    heading: &'static str,
    /// `Some(n)`: only that table (0-indexed, in source order) within the
    /// section counts -- needed when one heading covers multiple types
    /// whose method names overlap (`Core Sum Types`' `Perhaps<T>` table and
    /// `Result<T, E>` table both have `.map()`/`.and_then()`/...; checking
    /// them pooled could match a row against the *other* type's
    /// declaration and miss a real mismatch). `None`: pool every table in
    /// the section (safe when names don't collide, e.g. String's instance
    /// methods + its one static `join`).
    table_index: Option<usize>,
    include_param_names: bool,
    real: Vec<RealFn>,
}

fn check_surface(runtime_md: &str, surface: &Surface, problems: &mut Vec<String>) {
    let tables = parse_doc_tables(runtime_md, surface.heading);
    let doc_rows: Vec<&DocRow> = match surface.table_index {
        Some(i) => match tables.get(i) {
            Some(t) => t.iter().collect(),
            None => {
                problems.push(format!(
                    "runtime.md: heading `{}` has no table at index {i} -- \
                     check_stdlib_docs.rs's Surface list is stale",
                    surface.heading
                ));
                return;
            }
        },
        None => tables.iter().flatten().collect(),
    };
    if doc_rows.is_empty() {
        problems.push(format!(
            "runtime.md: no table found under heading `{}` (or it has zero rows) -- \
             check_stdlib_docs.rs's Surface list is stale",
            surface.heading
        ));
        return;
    }

    let real_names: BTreeSet<&str> = surface.real.iter().map(|f| f.name.as_str()).collect();
    let doc_names: BTreeSet<&str> = doc_rows.iter().map(|r| r.name.as_str()).collect();

    for name in doc_names.difference(&real_names) {
        problems.push(format!(
            "{}: `{name}` is documented but has no matching public declaration in stdlib/*.mtl",
            surface.heading
        ));
    }
    for name in real_names.difference(&doc_names) {
        problems.push(format!(
            "{}: `{name}` is a real public declaration in stdlib/*.mtl but isn't documented",
            surface.heading
        ));
    }

    for row in &doc_rows {
        // A name can be overloaded (`assert`'s one- and two-argument
        // forms) -- accept the row if it matches *any* candidate with that
        // name, not just the first found.
        let candidates: Vec<&RealFn> = surface.real.iter().filter(|f| f.name == row.name).collect();
        if candidates.is_empty() {
            continue; // already reported above
        }
        let rendered: Vec<String> = candidates
            .iter()
            .map(|f| render_sig(f, surface.include_param_names))
            .collect();
        let actual = row.signature.replace(' ', "");
        if !rendered.iter().any(|r| r.replace(' ', "") == actual) {
            problems.push(format!(
                "{}: `{}` documented as `{}`, but stdlib/*.mtl's real declaration(s) render as {}",
                surface.heading,
                row.name,
                row.signature,
                rendered
                    .iter()
                    .map(|r| format!("`{r}`"))
                    .collect::<Vec<_>>()
                    .join(" or ")
            ));
        }
    }
}

fn main() -> ExitCode {
    let core = parse_stdlib("core.mtl");
    let env = parse_stdlib("env.mtl");
    let fs = parse_stdlib("fs.mtl");
    let process = parse_stdlib("process.mtl");

    let surfaces = vec![
        Surface {
            heading: "Built-in Functions",
            table_index: None,
            include_param_names: true,
            real: top_level_public(&core.decls),
        },
        Surface {
            heading: "String Methods",
            table_index: None, // pools the instance-method table + the static `join` table
            include_param_names: false,
            real: {
                // `.to_string()` comes from `extend String: Display`, an
                // aspect impl, not the inherent block the rest of this
                // table's rows come from.
                let mut v = extend_methods(&core.decls, "String", None);
                v.extend(extend_methods(&core.decls, "String", Some("Display")));
                v
            },
        },
        Surface {
            heading: "Char Methods",
            table_index: None,
            include_param_names: false,
            real: {
                let mut v = extend_methods(&core.decls, "Char", Some("From"));
                v.extend(extend_methods(&core.decls, "Char", Some("Display")));
                // The table's `u32::from(c)` row is `u32`'s own
                // `From<Char>` impl, documented alongside Char's methods
                // (the two conversions are each other's inverse) even
                // though it isn't a Char declaration at all. `u32` has many
                // other `From<X>` impls (numeric conversions, documented
                // narratively elsewhere, not in this table) -- adding them
                // all as extra candidates for the name "from" is harmless:
                // the check accepts a row if *any* same-named candidate's
                // signature matches, so unrelated candidates never cause a
                // false positive, they just widen the pool.
                v.extend(extend_methods(&core.decls, "u32", Some("From")));
                v
            },
        },
        Surface {
            heading: "Core Sum Types",
            table_index: Some(0), // Perhaps<T> -- see the table_index doc comment
            include_param_names: false,
            real: extend_methods(&core.decls, "Perhaps", None),
        },
        Surface {
            heading: "Core Sum Types",
            table_index: Some(1), // Result<T, E>
            include_param_names: false,
            real: extend_methods(&core.decls, "Result", None),
        },
        Surface {
            heading: "List<T>",
            table_index: None,
            include_param_names: false,
            real: extend_methods(&core.decls, "List", None),
        },
        Surface {
            heading: "OsError",
            table_index: None,
            include_param_names: false,
            real: extend_methods(&core.decls, "OsError", None),
        },
        Surface {
            heading: "std::env",
            table_index: None,
            include_param_names: false,
            real: top_level_public(&env.decls),
        },
        Surface {
            heading: "std::fs",
            table_index: None,
            include_param_names: false,
            real: top_level_public(&fs.decls),
        },
        Surface {
            heading: "std::process",
            table_index: None,
            include_param_names: false,
            real: top_level_public(&process.decls),
        },
    ];

    let runtime_md = std::fs::read_to_string(runtime_md_path())
        .unwrap_or_else(|e| panic!("reading runtime.md: {e}"));

    let mut problems = Vec::new();
    for surface in &surfaces {
        check_surface(&runtime_md, surface, &mut problems);
    }

    if problems.is_empty() {
        println!("check_stdlib_docs: runtime.md matches stdlib/*.mtl's real declarations.");
        ExitCode::SUCCESS
    } else {
        eprintln!("check_stdlib_docs: {} mismatch(es):", problems.len());
        for p in &problems {
            eprintln!("  - {p}");
        }
        ExitCode::FAILURE
    }
}
