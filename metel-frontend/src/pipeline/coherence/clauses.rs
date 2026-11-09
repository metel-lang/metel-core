//! The colon list and the `derives` clause of a struct or enum declaration (RFC-0207, metel-core#1800).
//!
//! The parser turns each entry into the marker impl it stands for, so the impls are checked like any
//! other (obligations of the aspect's super-aspects, `T0015` against a written `extend` of the same
//! aspect, the `Copy` field rule). What is checked here is the entry itself (`T0003`, `T0046`):
//! - a colon-list entry is a `declared` aspect with no methods: a user marker is an unchecked promise;
//!   an aspect whose derivation brings a super-aspect (`Copy`) is granted through `derives` or its class
//!   keyword, and a method-bearing aspect through `derives` or `extend`;
//! - a `derives` entry is an aspect that has a derivation (the `derivable` property, std only).

use std::collections::HashMap;

use crate::data::ast::{AspectDecl, AspectProperty, ClauseEntry, Decl, DeclClauses, Span};
use crate::data::error::{MetelError, TypeErrorCode};
use crate::identity::symbols::SymbolId;
use crate::pipeline::name_resolution::name_resolver::ResolvedNames;
use crate::pipeline::path_normalization::NormalizedModuleGraph;

/// What a declaration clause needs to know about the aspect an entry names.
struct AspectFacts {
    name: String,
    declared: bool,
    derivable: bool,
    method_count: usize,
    /// Its derivation brings a super-aspect (`aspect Copy: deriving Clone`).
    brings_super: bool,
}

fn facts_of(ad: &AspectDecl) -> AspectFacts {
    let has = |property: AspectProperty| ad.properties.iter().any(|(p, _)| *p == property);
    AspectFacts {
        name: ad.name.clone(),
        declared: has(AspectProperty::Declared),
        derivable: has(AspectProperty::Derivable),
        method_count: ad.methods.len(),
        brings_super: ad.supers.iter().any(|entry| entry.deriving),
    }
}

/// Check the entries of every struct and enum declaration's clauses.
pub(super) fn check(graph: &NormalizedModuleGraph) -> Result<(), MetelError> {
    let names = &graph.names;
    let mut aspects: HashMap<SymbolId, AspectFacts> = HashMap::new();
    for module in graph.modules() {
        for decl in &module.program.decls {
            if let Decl::Aspect(ad) = decl
                && let Some(id) = super::declared_symbol(names, &module.module_path, &ad.name)
            {
                aspects.insert(id, facts_of(ad));
            }
        }
    }
    for module in graph.modules() {
        for decl in &module.program.decls {
            let (name, clauses) = match decl {
                Decl::Struct(sd) => (&sd.name, &sd.clauses),
                Decl::Enum(ed) => (&ed.name, &ed.clauses),
                _ => continue,
            };
            check_clauses(names, &module.module_path, name, clauses, &aspects)?;
        }
    }
    Ok(())
}

fn check_clauses(
    names: &ResolvedNames,
    module: &[String],
    type_name: &str,
    clauses: &DeclClauses,
    aspects: &HashMap<SymbolId, AspectFacts>,
) -> Result<(), MetelError> {
    for entry in &clauses.colon {
        let facts = lookup(names, module, entry, aspects)?;
        if facts.brings_super || facts.derivable {
            return Err(error(
                format!(
                    "`{0}` is granted by derivation, so the colon list cannot grant it: write `struct {1} derives {0}`{2}",
                    facts.name,
                    type_name,
                    if facts.name == crate::pipeline::type_checking::type_engine::COPY_ASPECT {
                        format!(" or `copy struct {type_name}`")
                    } else {
                        String::new()
                    }
                ),
                &entry.span,
            ));
        }
        if facts.method_count > 0 {
            return Err(error(
                format!(
                    "`{0}` has methods, so the colon list cannot grant it: write `struct {1} derives {0}` if it is derivable, or `extend {1}: {0} {{ ... }}`",
                    facts.name, type_name
                ),
                &entry.span,
            ));
        }
        if !facts.declared {
            return Err(error(
                format!(
                    "`{0}` is not a `declared` aspect, so the colon list cannot grant it: write `extend {1}: {0};`",
                    facts.name, type_name
                ),
                &entry.span,
            ));
        }
    }
    for entry in &clauses.derives {
        let facts = lookup(names, module, entry, aspects)?;
        if !facts.derivable {
            return Err(error(
                format!(
                    "`{}` has no derivation, so `derives` cannot generate it: write `extend {type_name}: {} {{ ... }}`",
                    facts.name, facts.name
                ),
                &entry.span,
            ));
        }
    }
    Ok(())
}

/// The facts of the aspect `entry` names, or `T0003` when it names no aspect.
fn lookup<'a>(
    names: &ResolvedNames,
    module: &[String],
    entry: &ClauseEntry,
    aspects: &'a HashMap<SymbolId, AspectFacts>,
) -> Result<&'a AspectFacts, MetelError> {
    super::resolve_id(names, module, &entry.name)
        .and_then(|id| aspects.get(&id))
        .ok_or_else(|| {
            MetelError::type_error(
                TypeErrorCode::T0003,
                format!("unknown aspect `{}` in a declaration clause", entry.name),
                &entry.span,
            )
        })
}

fn error(message: String, span: &Span) -> MetelError {
    MetelError::type_error(TypeErrorCode::T0046, message, span)
}
