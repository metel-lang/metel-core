//! [`MemberTable`] — identity for the nominal fields and variants of struct and
//! enum types (ADR-0054 step 3).
//!
//! This is the interning milestone of the resolution freeze: every declared
//! field and enum variant gets a [`FieldId`] / [`VariantId`], keyed
//! structurally by `(owning type `[`SymbolId`]`, declared member name)`. It is
//! built from the parsed type declarations, before inference — so a
//! type-directed selection that is undecidable mid-inference can still carry an
//! interned member id and be resolved to a declaration id at the freeze,
//! rather than reopening a textual lookup.
//!
//! What this milestone does *not* do: rekey the inference context's
//! `struct_env` / variant registries off `String`, or thread `FieldId` /
//! `VariantId` onto the typed IR. Those are the freeze proper (the next #1051
//! increment).
//!
//! [`FieldId`]: super::FieldId
//! [`VariantId`]: super::VariantId
//! [`SymbolId`]: super::SymbolId

use std::collections::HashMap;

use crate::data::ast::Span;

use super::{FieldId, NameId, NameInterner, SymbolId, VariantId};

/// What is known about one nominal member (a struct field or an enum variant).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemberInfo {
    /// The `SymbolId` of the struct or enum that declares this member.
    pub owner: SymbolId,
    /// The interned member spelling, for rendering and diagnostics.
    pub name: NameId,
    /// The declaration site.
    pub span: Span,
}

/// Interns struct fields to [`FieldId`] and enum variants to [`VariantId`],
/// keyed by `(owner SymbolId, member name)`.
///
/// Owned by the resolver, handed to the frozen artifact by value, immutable
/// thereafter. Equal `(owner, name)` pairs intern equal, so this is
/// deterministic for one resolved module graph and independent of iteration
/// order. Two same-named fields on different types get different ids because
/// the owner is part of the key.
#[derive(Debug, Clone, Default)]
pub struct MemberTable {
    fields: HashMap<(SymbolId, String), FieldId>,
    variants: HashMap<(SymbolId, String), VariantId>,
    field_info: HashMap<FieldId, MemberInfo>,
    variant_info: HashMap<VariantId, MemberInfo>,
    next_field: u32,
    next_variant: u32,
}

impl MemberTable {
    /// A fresh, empty table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern a field of `owner`, recording its declaration site the first time
    /// it is seen. Repeated calls with the same `(owner, name)` return the same
    /// id.
    pub fn intern_field(
        &mut self,
        owner: SymbolId,
        name: &str,
        span: &Span,
        interner: &mut NameInterner,
    ) -> FieldId {
        if let Some(&id) = self.fields.get(&(owner, name.to_string())) {
            return id;
        }
        let id = FieldId(self.next_field);
        self.next_field += 1;
        self.fields.insert((owner, name.to_string()), id);
        self.field_info.insert(
            id,
            MemberInfo {
                owner,
                name: interner.name(name),
                span: span.clone(),
            },
        );
        id
    }

    /// Intern a variant of `owner` (an enum `SymbolId`).
    pub fn intern_variant(
        &mut self,
        owner: SymbolId,
        name: &str,
        span: &Span,
        interner: &mut NameInterner,
    ) -> VariantId {
        if let Some(&id) = self.variants.get(&(owner, name.to_string())) {
            return id;
        }
        let id = VariantId(self.next_variant);
        self.next_variant += 1;
        self.variants.insert((owner, name.to_string()), id);
        self.variant_info.insert(
            id,
            MemberInfo {
                owner,
                name: interner.name(name),
                span: span.clone(),
            },
        );
        id
    }

    /// The id a field was interned under, if any.
    #[must_use]
    pub fn field(&self, owner: SymbolId, name: &str) -> Option<FieldId> {
        self.fields.get(&(owner, name.to_string())).copied()
    }

    /// The id a variant was interned under, if any.
    #[must_use]
    pub fn variant(&self, owner: SymbolId, name: &str) -> Option<VariantId> {
        self.variants.get(&(owner, name.to_string())).copied()
    }

    /// Metadata for an interned field.
    #[must_use]
    pub fn field_info(&self, id: FieldId) -> Option<&MemberInfo> {
        self.field_info.get(&id)
    }

    /// Metadata for an interned variant.
    #[must_use]
    pub fn variant_info(&self, id: VariantId) -> Option<&MemberInfo> {
        self.variant_info.get(&id)
    }

    /// Number of interned fields.
    #[must_use]
    pub fn field_count(&self) -> usize {
        self.fields.len()
    }

    /// Number of interned variants.
    #[must_use]
    pub fn variant_count(&self) -> usize {
        self.variants.len()
    }
}

/// Build the whole-graph member table in one deterministic pass: modules in
/// dependency order, declarations in source order, members in declaration
/// order. `names` supplies the owning type's `SymbolId`.
#[must_use]
// arch-implements: ["arch.resolution.requirement-3"]
pub fn collect_members(
    modules: &[(Vec<String>, &[crate::data::ast::Decl])],
    names: &crate::pipeline::name_resolution::name_resolver::ResolvedNames,
    interner: &mut NameInterner,
) -> MemberTable {
    use crate::data::ast::Decl;

    let mut table = MemberTable::new();
    for (module_path, decls) in modules {
        for decl in *decls {
            match decl {
                Decl::Struct(sd) => {
                    let Some(&owner) = names.symbols.get(&(module_path.clone(), sd.name.clone()))
                    else {
                        continue;
                    };
                    for field in &sd.fields {
                        table.intern_field(owner, &field.name, &field.span, interner);
                    }
                }
                Decl::Enum(ed) => {
                    let Some(&owner) = names.symbols.get(&(module_path.clone(), ed.name.clone()))
                    else {
                        continue;
                    };
                    for variant in &ed.variants {
                        table.intern_variant(owner, &variant.name, &variant.span, interner);
                        // A fieldful variant's own fields are members of the
                        // enum, keyed by the *variant-qualified* name so
                        // `V.x` and `W.x` on the same enum stay distinct.
                        for field in &variant.fields {
                            let qualified = format!("{}::{}", variant.name, field.name);
                            table.intern_field(owner, &qualified, &field.span, interner);
                        }
                    }
                }
                _ => {}
            }
        }
    }
    table
}

/// Convenience wrapper around [`collect_members`] that takes a loaded
/// (pre-normalization) [`ModuleGraph`] directly. The `analyze_*` path builds
/// the member table from its own `identity_modules` slice (shared with
/// [`allocate_graph`]); the interpreter pipeline has no `Analysis` to hang the
/// table on, so it calls this right before `path_normalizer::normalize`
/// consumes the graph. The `NameId`s in the resulting [`MemberInfo`]s are
/// interned into a throwaway interner — the pipeline never resolves them — but
/// [`FieldId`] / [`VariantId`] assignment is a plain declaration-order counter,
/// so the ids match what `analyze_*` produces for the same graph.
///
/// [`ModuleGraph`]: crate::pipeline::parsing::module_loader::ModuleGraph
/// [`allocate_graph`]: super::allocate_graph
#[must_use]
pub fn collect_members_for_graph(
    graph: &crate::pipeline::parsing::module_loader::ModuleGraph,
    names: &crate::pipeline::name_resolution::name_resolver::ResolvedNames,
) -> MemberTable {
    let modules: Vec<(Vec<String>, &[crate::data::ast::Decl])> = graph
        .modules
        .iter()
        .map(|module| (module.module_path.clone(), module.program.decls.as_slice()))
        .collect();
    collect_members(&modules, names, &mut NameInterner::new())
}

#[cfg(test)]
mod tests;
