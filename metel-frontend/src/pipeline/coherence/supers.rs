//! Super-aspects (RFC-0213, metel-core#1801): the declared relation `aspect A: B, deriving C, !D` and
//! what it demands of impls.
//!
//! - Every entry names an aspect (`T0003` otherwise); a cycle, a self-exclusion and a `deriving` mark
//!   on a user aspect are `T0044`. Only std aspects may carry the mark in v0.16.0.
//! - An impl of `A` for a type needs a coherent positive impl of every direct and transitive positive
//!   super-aspect for that type (`T0012`, naming the missing one) and may not sit beside a negative
//!   impl of one (`T0015`).
//! - A negative entry is a grant-time exclusion: granting both `A` and the excluded aspect to one
//!   type is `T0015`, naming both. It is evidence for nothing else (RFC-0213 section 3).

use std::collections::{HashMap, HashSet};

use super::{CollectedImpl, canonical_types_compatible, resolve_id};
use crate::data::ast::{Decl, Polarity, Span};
use crate::data::error::{MetelError, TypeErrorCode};
use crate::identity::symbols::{Namespace, SymbolId};
use crate::pipeline::name_resolution::name_resolver::ResolvedNames;
use crate::pipeline::path_normalization::NormalizedModuleGraph;

/// One resolved entry of an aspect's super-aspect list.
pub(super) struct Super {
    pub id: SymbolId,
    pub negative: bool,
    pub name: String,
}

/// The resolved super-aspect lists of every aspect in the program, keyed by the aspect's identity.
pub(super) struct SuperTable {
    direct: HashMap<SymbolId, Vec<Super>>,
    names: HashMap<SymbolId, String>,
    spans: HashMap<SymbolId, Span>,
}

impl SuperTable {
    /// Resolve and validate every aspect's list (`T0003`, `T0044`).
    pub(super) fn build(graph: &NormalizedModuleGraph) -> Result<Self, MetelError> {
        let names = &graph.names;
        let mut aspects: HashMap<SymbolId, String> = HashMap::new();
        let mut spans: HashMap<SymbolId, Span> = HashMap::new();
        for module in graph.modules() {
            for decl in &module.program.decls {
                if let Decl::Aspect(ad) = decl
                    && let Some(id) = declared_id(names, &module.module_path, &ad.name)
                {
                    aspects.insert(id, ad.name.clone());
                    spans.insert(id, ad.span.clone());
                }
            }
        }
        let mut direct: HashMap<SymbolId, Vec<Super>> = HashMap::new();
        for module in graph.modules() {
            for decl in &module.program.decls {
                let Decl::Aspect(ad) = decl else { continue };
                let Some(id) = declared_id(names, &module.module_path, &ad.name) else {
                    continue;
                };
                let in_std = module.module_path.first().is_some_and(|m| m == "std");
                let mut entries = Vec::new();
                for entry in &ad.supers {
                    if entry.deriving && !in_std {
                        return Err(error(
                            TypeErrorCode::T0044,
                            format!(
                                "`deriving` marks a super-aspect of a std aspect only; `{}` is a user aspect, so `{}` is an obligation its impls write by hand",
                                ad.name, entry.name
                            ),
                            &entry.span,
                        ));
                    }
                    let Some(super_id) = resolve_id(names, &module.module_path, &entry.name) else {
                        return Err(error(
                            TypeErrorCode::T0003,
                            format!(
                                "unknown aspect `{}` in the super-aspect list of `{}`",
                                entry.name, ad.name
                            ),
                            &entry.span,
                        ));
                    };
                    if !aspects.contains_key(&super_id) {
                        return Err(error(
                            TypeErrorCode::T0003,
                            format!(
                                "`{}` is not an aspect, so it cannot be a super-aspect of `{}`",
                                entry.name, ad.name
                            ),
                            &entry.span,
                        ));
                    }
                    if entry.negative && super_id == id {
                        return Err(error(
                            TypeErrorCode::T0044,
                            format!("aspect `{}` cannot exclude itself", ad.name),
                            &entry.span,
                        ));
                    }
                    entries.push(Super {
                        id: super_id,
                        negative: entry.negative,
                        name: entry.name.clone(),
                    });
                }
                direct.insert(id, entries);
            }
        }
        let table = Self {
            direct,
            names: aspects,
            spans,
        };
        table.reject_cycles()?;
        Ok(table)
    }

    /// The aspects in source order, so the first error reported does not depend on hash order.
    fn in_source_order(&self) -> Vec<SymbolId> {
        let mut ids: Vec<SymbolId> = self.direct.keys().copied().collect();
        ids.sort_by_key(|id| {
            self.spans
                .get(id)
                .map(|span| (span.filename.clone(), span.line, span.col))
        });
        ids
    }

    fn reject_cycles(&self) -> Result<(), MetelError> {
        for start in self.in_source_order() {
            let mut seen = HashSet::new();
            let mut stack: Vec<SymbolId> = self.positive_supers(start);
            while let Some(next) = stack.pop() {
                if next == start {
                    let Some(span) = self.spans.get(&start) else {
                        continue;
                    };
                    return Err(error(
                        TypeErrorCode::T0044,
                        format!(
                            "aspect `{}` is its own super-aspect, directly or through another",
                            self.name(start)
                        ),
                        span,
                    ));
                }
                if seen.insert(next) {
                    stack.extend(self.positive_supers(next));
                }
            }
        }
        Ok(())
    }

    fn name(&self, id: SymbolId) -> &str {
        self.names.get(&id).map_or("?", String::as_str)
    }

    fn positive_supers(&self, id: SymbolId) -> Vec<SymbolId> {
        self.direct
            .get(&id)
            .map(|entries| {
                entries
                    .iter()
                    .filter(|entry| !entry.negative)
                    .map(|entry| entry.id)
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Every direct and transitive positive super-aspect of `id`, each once.
    pub(super) fn positive_closure(&self, id: SymbolId) -> Vec<SymbolId> {
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        let mut stack = self.positive_supers(id);
        while let Some(next) = stack.pop() {
            if seen.insert(next) {
                out.push(next);
                stack.extend(self.positive_supers(next));
            }
        }
        out
    }

    /// Check the impls against the relation: obligations (`T0012`, `T0015`) and exclusions (`T0015`).
    pub(super) fn check_impls(&self, impls: &[CollectedImpl]) -> Result<(), MetelError> {
        let positive = |id: SymbolId| {
            impls
                .iter()
                .filter(move |imp| imp.polarity == Polarity::Positive && imp.aspect_id == Some(id))
        };
        for imp in impls {
            let (Polarity::Positive, Some(aspect)) = (imp.polarity, imp.aspect_id) else {
                continue;
            };
            for required in self.positive_closure(aspect) {
                let has = |polarity: Polarity| {
                    impls.iter().any(|other| {
                        other.polarity == polarity
                            && other.aspect_id == Some(required)
                            && canonical_types_compatible(
                                &other.canonical_key.1,
                                &imp.canonical_key.1,
                            )
                    })
                };
                if has(Polarity::Negative) {
                    return Err(error(
                        TypeErrorCode::T0015,
                        format!(
                            "`{}` requires `{}`, but this type has a negative impl of `{}`",
                            imp.aspect_name,
                            self.name(required),
                            self.name(required)
                        ),
                        imp.span,
                    ));
                }
                if !has(Polarity::Positive) {
                    return Err(error(
                        TypeErrorCode::T0012,
                        format!(
                            "`{}` is a super-aspect of `{}` and has no impl for this type; write `extend ...: {}` first",
                            self.name(required),
                            imp.aspect_name,
                            self.name(required)
                        ),
                        imp.span,
                    ));
                }
            }
        }
        for aspect in self.in_source_order() {
            let Some(entries) = self.direct.get(&aspect) else {
                continue;
            };
            for excluded in entries.iter().filter(|entry| entry.negative) {
                for granted in positive(aspect) {
                    for other in positive(excluded.id) {
                        if !canonical_types_compatible(
                            &granted.canonical_key.1,
                            &other.canonical_key.1,
                        ) {
                            continue;
                        }
                        let later = if (granted.span.line, granted.span.col)
                            > (other.span.line, other.span.col)
                        {
                            granted
                        } else {
                            other
                        };
                        return Err(error(
                            TypeErrorCode::T0015,
                            format!(
                                "`{}` and `{}` cannot both be granted to one type: `aspect {}: !{}` excludes the pair",
                                self.name(aspect),
                                excluded.name,
                                self.name(aspect),
                                excluded.name
                            ),
                            later.span,
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}

fn declared_id(names: &ResolvedNames, module: &[String], name: &str) -> Option<SymbolId> {
    names
        .symbols
        .get(&(module.to_vec(), Namespace::Type, name.to_string()))
        .copied()
}

fn error(code: TypeErrorCode, message: String, span: &Span) -> MetelError {
    MetelError::type_error(code, message, span)
}
