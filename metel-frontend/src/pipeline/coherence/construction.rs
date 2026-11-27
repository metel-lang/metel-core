//! Privileged representation construction (RFC-0100 section 3, metel-core#2200): a nominal brace
//! literal -- `Point { x = 1, y = 2 }`, `Shape::Circle { radius = 1 }` -- is legal only inside an
//! `extend` block of its own type, inherent or aspect impl. Everywhere else a value is built with the
//! call form, `Point(x = 1, y = 2)`. It is an ergonomics rule, not an invariant boundary: what it
//! guarantees is that code outside a type's impls constructs through the call form.
//!
//! Checked here, on the program as written and before type checking, for two reasons: the literals
//! type checking synthesizes from construction calls do not exist yet, so a written literal cannot be
//! confused with one; and a generic function's body is checked once, ahead of time, rather than when
//! it is reconstructed. `Self` at a literal's head was already rewritten to the type its `extend`
//! block names (`parsing::type_alias`), so a literal is compared by identity like any other.

use std::collections::{HashMap, HashSet};

use crate::data::ast::{Block, Decl, Expr, Span, TypeExpr};
use crate::data::decl_walk::{
    for_each_block, for_each_declaration, for_each_expression, for_each_expression_in_expr,
};
use crate::data::error::{MetelError, TypeErrorCode};
use crate::identity::symbols::SymbolId;
use crate::pipeline::name_resolution::name_resolver::ResolvedNames;
use crate::pipeline::path_normalization::NormalizedModuleGraph;

/// Which type a name denotes where it is written: a module-level declaration by its identity, or a
/// block-local one by where it is declared.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum TypeIdentity {
    Module(SymbolId),
    Local { filename: String, start: usize },
}

/// Reject every brace literal written outside an `extend` block of its own type.
///
/// # Errors
/// `T0048` for the first such literal.
pub(super) fn check(graph: &NormalizedModuleGraph) -> Result<(), MetelError> {
    let names = &graph.names;
    for module in graph.modules() {
        let checker = Checker {
            names,
            module: &module.module_path,
            variants: enum_variants(names, &module.module_path, &module.program.decls),
        };
        for decl in &module.program.decls {
            checker.declaration(decl)?;
        }
    }
    Ok(())
}

/// Every module-level enum of a module's declarations and the names of its variants.
fn enum_variants(
    names: &ResolvedNames,
    module: &[String],
    decls: &[Decl],
) -> HashMap<TypeIdentity, HashSet<String>> {
    decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::Enum(declaration) => {
                let id = super::resolve_id(names, module, &declaration.name)?;
                Some((
                    TypeIdentity::Module(id),
                    declaration
                        .variants
                        .iter()
                        .map(|v| v.name.clone())
                        .collect(),
                ))
            }
            _ => None,
        })
        .collect()
}

struct Checker<'a> {
    names: &'a ResolvedNames,
    module: &'a [String],
    variants: HashMap<TypeIdentity, HashSet<String>>,
}

impl Checker<'_> {
    fn declaration(&self, decl: &Decl) -> Result<(), MetelError> {
        match decl {
            Decl::Impl(impl_block) => {
                let target = match &impl_block.target_type {
                    TypeExpr::Named(name, _, _) => self.module_type(name),
                    _ => None,
                };
                for method in &impl_block.methods {
                    self.body(&method.body, target.as_ref())?;
                }
            }
            Decl::Fun(function) => self.body(&function.body, None)?,
            Decl::Aspect(aspect) => {
                for method in &aspect.methods {
                    if let Some(body) = &method.default_body {
                        self.body(body, None)?;
                    }
                }
            }
            Decl::Let(binding) => self.expression_tree(&binding.value, &[], None)?,
            Decl::Mut(binding) => self.expression_tree(&binding.value, &[], None)?,
            Decl::LetPattern(binding) => self.expression_tree(&binding.value, &[], None)?,
            Decl::Struct(_) | Decl::Enum(_) | Decl::TypeAlias(_) | Decl::Stmt(_) => {}
        }
        Ok(())
    }

    /// Check a body whose brace literals may build `target` (an `extend` method's) or nothing (any
    /// other body), and the `extend` blocks declared inside it, each with its own target.
    fn body(&self, body: &Block, target: Option<&TypeIdentity>) -> Result<(), MetelError> {
        let mut blocks: Vec<&Block> = Vec::new();
        for_each_block(body, &mut |block| blocks.push(block));
        let mut literals = Vec::new();
        for_each_expression(body, &mut |expression| {
            if matches!(expression, Expr::StructLiteral { .. }) {
                literals.push(expression);
            }
        });
        for literal in literals {
            self.literal(literal, &blocks, target)?;
        }
        let mut nested = Vec::new();
        for_each_declaration(body, &mut |decl| {
            if let Decl::Impl(impl_block) = decl {
                nested.push(impl_block);
            }
        });
        for impl_block in nested {
            let target = match &impl_block.target_type {
                TypeExpr::Named(name, _, _) => self.resolve(name, &impl_block.span, &blocks),
                _ => None,
            };
            for method in &impl_block.methods {
                self.body(&method.body, target.as_ref())?;
            }
        }
        Ok(())
    }

    fn expression_tree(
        &self,
        root: &Expr,
        blocks: &[&Block],
        target: Option<&TypeIdentity>,
    ) -> Result<(), MetelError> {
        let mut literals = Vec::new();
        for_each_expression_in_expr(root, &mut |expression| {
            if matches!(expression, Expr::StructLiteral { .. }) {
                literals.push(expression);
            }
        });
        for literal in literals {
            self.literal(literal, blocks, target)?;
        }
        Ok(())
    }

    fn literal(
        &self,
        literal: &Expr,
        blocks: &[&Block],
        target: Option<&TypeIdentity>,
    ) -> Result<(), MetelError> {
        let Expr::StructLiteral {
            path,
            fields,
            symbol_id,
            span,
        } = literal
        else {
            return Ok(());
        };
        // A literal that initializes no field -- `Flag::On {}`, `Empty {}` -- builds nothing from
        // fields: it is the same value as the bare `Flag::On` or `Empty` (RFC-0106), legal anywhere,
        // and path normalization represents a qualified unit variant this way. Only a literal that
        // builds a value from its fields is privileged.
        if fields.is_empty() {
            return Ok(());
        }
        // `Self` that survived to here was written outside any `extend` block.
        let builds_target = match (path.as_slice(), symbol_id) {
            ([head, ..], _) if head == "Self" => false,
            (_, Some(id)) => target == Some(&TypeIdentity::Module(*id)),
            ([name], None) => match self.resolve(name, span, blocks) {
                Some(identity) => target == Some(&identity),
                // An unqualified variant (`Circle { .. }`, resolved by its expected type):
                // legal in an impl of an enum that has such a variant.
                None if self.is_variant_name(name, blocks) => {
                    target.is_some_and(|target| self.has_variant(target, name, blocks))
                }
                // Names no type at all: type checking reports it.
                None => return Ok(()),
            },
            ([enum_name, _], None) => match self.resolve(enum_name, span, blocks) {
                Some(identity) => target == Some(&identity),
                None => return Ok(()),
            },
            _ => return Ok(()),
        };
        if builds_target {
            return Ok(());
        }
        let written = path.join("::");
        Err(MetelError::type_error(
            TypeErrorCode::T0048,
            format!(
                "`{written} {{ .. }}` builds the value directly, which only an `extend` block of its \
                 own type may do; construct it here with the call form, `{written}(..)`"
            ),
            span,
        ))
    }

    /// The type `name` denotes at `at`: the innermost block-local declaration of it that encloses
    /// `at`, else the module-level one.
    fn resolve(&self, name: &str, at: &Span, blocks: &[&Block]) -> Option<TypeIdentity> {
        blocks
            .iter()
            .filter(|block| encloses(&block.span, at))
            .filter_map(|block| local_declaration(block, name).map(|span| (block.span.start, span)))
            .max_by_key(|(start, _)| *start)
            .map(|(_, span)| TypeIdentity::Local {
                filename: span.filename.clone(),
                start: span.start,
            })
            .or_else(|| self.module_type(name))
    }

    fn module_type(&self, name: &str) -> Option<TypeIdentity> {
        let last = name.rsplit("::").next().unwrap_or(name);
        super::resolve_id(self.names, self.module, last).map(TypeIdentity::Module)
    }

    fn is_variant_name(&self, name: &str, blocks: &[&Block]) -> bool {
        self.variants
            .values()
            .any(|variants| variants.contains(name))
            || blocks.iter().any(|block| {
                block.stmts.iter().any(|decl| {
                    matches!(decl, Decl::Enum(declaration)
                        if declaration.variants.iter().any(|v| v.name == name))
                })
            })
    }

    fn has_variant(&self, target: &TypeIdentity, name: &str, blocks: &[&Block]) -> bool {
        match target {
            TypeIdentity::Module(_) => self
                .variants
                .get(target)
                .is_some_and(|variants| variants.contains(name)),
            TypeIdentity::Local { filename, start } => blocks.iter().any(|block| {
                block.stmts.iter().any(|decl| {
                    matches!(decl, Decl::Enum(declaration)
                        if declaration.span.start == *start
                            && &declaration.span.filename == filename
                            && declaration.variants.iter().any(|v| v.name == name))
                })
            }),
        }
    }
}

fn encloses(outer: &Span, inner: &Span) -> bool {
    outer.filename == inner.filename && outer.start <= inner.start && inner.end <= outer.end
}

fn local_declaration<'b>(block: &'b Block, name: &str) -> Option<&'b Span> {
    block.stmts.iter().find_map(|decl| match decl {
        Decl::Struct(declaration) if declaration.name == name => Some(&declaration.span),
        Decl::Enum(declaration) if declaration.name == name => Some(&declaration.span),
        _ => None,
    })
}
