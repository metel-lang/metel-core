//! Aspect declaration properties (RFC-0212, metel-core#1803): `declared`, `implicit` and `auto`.
//!
//! Properties are read from the aspect's declaration by identity, so an import, alias or re-export
//! carries them unchanged. A violation is `T0045`:
//! - `implicit` and `auto` are accepted only on an aspect declared in the standard library;
//! - an `implicit` aspect refines `Clone` through a `deriving` super-aspect, and a program has at
//!   most one (the first, in source order, is the one that stands);
//! - a property is written once on one declaration;
//! - an `extend T: A` of a `declared` aspect `A` is rejected for a named type (its declaration grants
//!   `A`, RFC-0207), and for a type without a declaration only in the aspect's defining module.

use std::collections::{HashMap, HashSet};

use super::{CanonicalType, CollectedImpl};
use crate::data::ast::{AspectProperty, Decl, Polarity, Span};
use crate::data::error::{MetelError, TypeErrorCode};
use crate::identity::symbols::{Namespace, SymbolId};
use crate::pipeline::name_resolution::name_resolver::ResolvedNames;
use crate::pipeline::path_normalization::NormalizedModuleGraph;

struct Declared {
    name: String,
    module: Vec<String>,
}

/// Check every aspect declaration's properties and every impl of a `declared` aspect.
pub(super) fn check(
    graph: &NormalizedModuleGraph,
    impls: &[CollectedImpl],
) -> Result<(), MetelError> {
    let declared = check_declarations(graph)?;
    if declared.is_empty() {
        return Ok(());
    }
    let named_types = named_type_ids(graph);
    for imp in impls {
        let (Polarity::Positive, Some(aspect)) = (imp.polarity, imp.aspect_id) else {
            continue;
        };
        let Some(info) = declared.get(&aspect) else {
            continue;
        };
        let has_declaration = matches!(
            &imp.canonical_key.1,
            CanonicalType::Resolved(id, _) if named_types.contains(id)
        );
        if has_declaration {
            return Err(error(
                format!(
                    "`{}` is a `declared` aspect: grant it in the declaration of `{}` (`struct {}: {}` or `derives {}`), not with `extend`",
                    info.name, imp.target_head, imp.target_head, info.name, info.name
                ),
                imp.span,
            ));
        }
        if imp.module != info.module.as_slice() {
            return Err(error(
                format!(
                    "`{}` is a `declared` aspect: a type without a declaration of its own can be granted it only in the module that declares the aspect",
                    info.name
                ),
                imp.span,
            ));
        }
    }
    Ok(())
}

/// Validate the properties written on each aspect; the `declared` aspects, keyed by identity.
fn check_declarations(
    graph: &NormalizedModuleGraph,
) -> Result<HashMap<SymbolId, Declared>, MetelError> {
    let names = &graph.names;
    let clone_id = names
        .symbols
        .get(&(
            vec!["std".to_string(), "core".to_string()],
            Namespace::Type,
            "Clone".to_string(),
        ))
        .copied();
    let mut declared = HashMap::new();
    let mut first_implicit: Option<String> = None;
    for module in graph.modules() {
        let in_std = module.module_path.first().is_some_and(|m| m == "std");
        for decl in &module.program.decls {
            let Decl::Aspect(ad) = decl else { continue };
            let Some(id) = names
                .symbols
                .get(&(module.module_path.clone(), Namespace::Type, ad.name.clone()))
                .copied()
            else {
                continue;
            };
            let mut seen: HashSet<AspectProperty> = HashSet::new();
            for (property, span) in &ad.properties {
                if !seen.insert(*property) {
                    return Err(error(
                        format!(
                            "`{}` is written twice on aspect `{}`",
                            property.keyword(),
                            ad.name
                        ),
                        span,
                    ));
                }
                if matches!(property, AspectProperty::Implicit | AspectProperty::Auto) && !in_std {
                    return Err(error(
                        format!(
                            "`{}` is accepted only on an aspect declared in the standard library; `{}` is a user aspect",
                            property.keyword(),
                            ad.name
                        ),
                        span,
                    ));
                }
                if *property == AspectProperty::Declared {
                    declared.insert(
                        id,
                        Declared {
                            name: ad.name.clone(),
                            module: module.module_path.clone(),
                        },
                    );
                }
            }
            if let Some((_, span)) = ad
                .properties
                .iter()
                .find(|(property, _)| *property == AspectProperty::Implicit)
            {
                check_implicit(
                    names,
                    &module.module_path,
                    ad,
                    clone_id,
                    span,
                    &mut first_implicit,
                )?;
            }
        }
    }
    Ok(declared)
}

fn check_implicit(
    names: &ResolvedNames,
    module: &[String],
    ad: &crate::data::ast::AspectDecl,
    clone_id: Option<SymbolId>,
    span: &Span,
    first_implicit: &mut Option<String>,
) -> Result<(), MetelError> {
    let refines_clone = ad.supers.iter().any(|entry| {
        entry.deriving
            && !entry.negative
            && super::resolve_id(names, module, &entry.name).is_some_and(|id| Some(id) == clone_id)
    });
    if !refines_clone {
        return Err(error(
            format!(
                "an `implicit` aspect must refine `Clone` through a `deriving` super-aspect (`aspect {}: deriving Clone`)",
                ad.name
            ),
            span,
        ));
    }
    if let Some(first) = first_implicit {
        return Err(error(
            format!(
                "a program has at most one `implicit` aspect, and `{first}` already is one; `{}` cannot be a second",
                ad.name
            ),
            span,
        ));
    }
    *first_implicit = Some(ad.name.clone());
    Ok(())
}

/// The identities of every struct and enum: the types that have a declaration of their own.
fn named_type_ids(graph: &NormalizedModuleGraph) -> HashSet<SymbolId> {
    let mut out = HashSet::new();
    for module in graph.modules() {
        for decl in &module.program.decls {
            let name = match decl {
                Decl::Struct(sd) => &sd.name,
                Decl::Enum(ed) => &ed.name,
                _ => continue,
            };
            if let Some(id) = graph.names.symbols.get(&(
                module.module_path.clone(),
                Namespace::Type,
                name.clone(),
            )) {
                out.insert(*id);
            }
        }
    }
    out
}

fn error(message: String, span: &Span) -> MetelError {
    MetelError::type_error(TypeErrorCode::T0045, message, span)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::ast::AspectDecl;
    use crate::pipeline::parsing::module_loader::{self, MultiFileSourceProvider};

    /// The aspect declarations of `source`, with the names resolved for its root module. The std
    /// check of `check_declarations` is the caller's; here the rules for an `implicit` aspect are
    /// judged on their own, which no `.mtl` fixture can reach outside the standard library.
    fn check_all(source: &str) -> Result<(), MetelError> {
        let provider = MultiFileSourceProvider::new("main.mtl", source);
        let graph = module_loader::load_virtual_root_with("main.mtl", &provider).expect("loads");
        let names =
            crate::pipeline::name_resolution::name_resolver::resolve(&graph).expect("resolves");
        let clone_id = names
            .symbols
            .get(&(
                vec!["std".to_string(), "core".to_string()],
                Namespace::Type,
                "Clone".to_string(),
            ))
            .copied();
        assert!(clone_id.is_some(), "std::core::Clone is in the graph");
        let root = graph
            .modules
            .iter()
            .find(|module| module.module_path.is_empty())
            .expect("root module");
        let mut first = None;
        for decl in &root.program.decls {
            let Decl::Aspect(ad) = decl else { continue };
            let Some((_, span)) = implicit_of(ad) else {
                continue;
            };
            check_implicit(&names, &root.module_path, ad, clone_id, span, &mut first)?;
        }
        Ok(())
    }

    fn implicit_of(ad: &AspectDecl) -> Option<&(AspectProperty, Span)> {
        ad.properties
            .iter()
            .find(|(property, _)| *property == AspectProperty::Implicit)
    }

    #[test]
    fn an_implicit_aspect_that_derives_clone_is_accepted() {
        check_all("implicit aspect Dup: deriving Clone;\nfun main() {}").expect("accepted");
    }

    #[test]
    fn an_implicit_aspect_without_a_super_is_rejected() {
        let error = check_all("implicit aspect Bare;\nfun main() {}").expect_err("rejected");
        assert!(error.to_string().contains("must refine `Clone`"), "{error}");
    }

    #[test]
    fn an_implicit_aspect_whose_clone_super_is_not_derived_is_rejected() {
        let error = check_all("implicit aspect Weak: Clone;\nfun main() {}").expect_err("rejected");
        assert!(error.to_string().contains("must refine `Clone`"), "{error}");
    }

    #[test]
    fn an_implicit_aspect_deriving_another_aspect_is_rejected() {
        let error = check_all("aspect Other;\nimplicit aspect Odd: deriving Other;\nfun main() {}")
            .expect_err("rejected");
        assert!(error.to_string().contains("must refine `Clone`"), "{error}");
    }

    #[test]
    fn a_second_implicit_aspect_is_rejected() {
        let error = check_all(
            "implicit aspect One: deriving Clone;\nimplicit aspect Two: deriving Clone;\nfun main() {}",
        )
        .expect_err("rejected");
        assert!(
            error.to_string().contains("at most one `implicit` aspect"),
            "{error}"
        );
    }
}
