//! RFC-0193 §2: when a private free function has no return type and a non-unit body, the
//! mismatch diagnostic also offers the equivalent `let`-bound closure, but only when the
//! rewrite keeps the program's meaning. The conditions are syntactic over the module's
//! top-level declarations and are conservative: a function that cannot be shown to satisfy
//! all of them gets the written-type help only. The suggestion is advice; the rewrite is
//! not type-checked.

use super::closure_uses::collect_closure_body_uses;
use crate::data::ast::{Decl, FunDecl, Program, TypeExpr, Visibility};
use std::collections::{BTreeSet, HashMap, HashSet};

/// Whether a parameter type mentions a record, an open record or a row: a closure cannot state
/// the row facts (`!{ label }`) such a body may need (condition 5, kept conservative).
fn mentions_record_or_row(te: &TypeExpr) -> bool {
    match te {
        TypeExpr::Record(_)
        | TypeExpr::OpenRecord(..)
        | TypeExpr::OpenRecordProjection { .. }
        | TypeExpr::RecordProjection { .. }
        | TypeExpr::RowArg(_)
        | TypeExpr::RowArgLiteral(_) => true,
        TypeExpr::Named(_, args, _) => args.iter().any(mentions_record_or_row),
        TypeExpr::Tuple(items) => items.iter().any(mentions_record_or_row),
        TypeExpr::Array(inner)
        | TypeExpr::SizedArray(inner, _)
        | TypeExpr::Reference(inner)
        | TypeExpr::MutReference(inner) => mentions_record_or_row(inner),
        TypeExpr::Fun {
            params,
            return_type,
            ..
        } => {
            params.iter().any(mentions_record_or_row)
                || return_type.as_deref().is_some_and(mentions_record_or_row)
        }
        _ => false,
    }
}

/// The top-level functions a body names, as a set of function names.
fn called_functions(fun: &FunDecl, names: &HashSet<&str>) -> BTreeSet<String> {
    let mut bound: BTreeSet<String> = fun.params.iter().map(|p| p.name.clone()).collect();
    let mut reads = BTreeSet::new();
    let mut writes = BTreeSet::new();
    let mut spans = HashMap::new();
    collect_closure_body_uses(&fun.body, &mut bound, &mut reads, &mut writes, &mut spans);
    reads
        .into_iter()
        .chain(writes)
        .filter(|name| names.contains(name.as_str()))
        .collect()
}

/// Whether `from` reaches `target` through calls among the module's top-level functions.
fn reaches(from: &str, target: &str, uses: &HashMap<&str, BTreeSet<String>>) -> bool {
    let mut seen: HashSet<&str> = HashSet::new();
    let mut stack = vec![from];
    while let Some(current) = stack.pop() {
        let Some(callees) = uses.get(current) else {
            continue;
        };
        for callee in callees {
            if callee == target {
                return true;
            }
            if seen.insert(callee.as_str()) {
                stack.push(callee.as_str());
            }
        }
    }
    false
}

/// The private top-level functions for which RFC-0193's closure rewrite is safe to suggest.
pub(super) fn closure_rewrite_candidates(program: &Program) -> HashSet<String> {
    let funs: Vec<(usize, &FunDecl)> = program
        .decls
        .iter()
        .enumerate()
        .filter_map(|(i, d)| match d {
            Decl::Fun(fd) => Some((i, fd)),
            _ => None,
        })
        .collect();
    let names: HashSet<&str> = funs.iter().map(|(_, fd)| fd.name.as_str()).collect();
    let uses: HashMap<&str, BTreeSet<String>> = funs
        .iter()
        .map(|(_, fd)| (fd.name.as_str(), called_functions(fd, &names)))
        .collect();
    funs.iter()
        .filter(|(index, fd)| {
            fd.visibility == Visibility::Private
                && fd.native.is_none()
                && fd.generics.is_empty()
                && fd.where_clause.is_none()
                && fd.return_type.is_none()
                && fd.params.iter().all(|p| {
                    p.receiver.is_none()
                        && p.type_ann.as_ref().is_some_and(|te| !mentions_record_or_row(te))
                })
                // 3. does not call itself, directly or through other functions
                && !reaches(&fd.name, &fd.name, &uses)
                // 4. every use follows the declaration
                && !funs.iter().any(|(j, other)| {
                    j < index && uses.get(other.name.as_str()).is_some_and(|u| u.contains(&fd.name))
                })
        })
        .map(|(_, fd)| fd.name.clone())
        .collect()
}
