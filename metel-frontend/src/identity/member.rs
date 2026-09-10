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

use crate::ast::Span;

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
pub fn collect_members(
    modules: &[(Vec<String>, &[crate::ast::Decl])],
    names: &crate::name_resolver::ResolvedNames,
    interner: &mut NameInterner,
) -> MemberTable {
    use crate::ast::Decl;

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

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::path::PathBuf;

    use crate::module_loader::{LoadedModule, ModuleGraph};
    use crate::name_resolver::resolve;

    use super::super::NameInterner;
    use super::collect_members;

    fn members(source: &str) -> (super::MemberTable, crate::name_resolver::ResolvedNames) {
        let program = crate::parser::parse(source, "test.mtl").expect("parse");
        let graph = ModuleGraph {
            root: PathBuf::from("test.mtl"),
            modules: vec![LoadedModule {
                module_path: vec![],
                file_path: PathBuf::from("test.mtl"),
                program,
            }],
            path_aliases: HashMap::new(),
        };
        let names = resolve(&graph).expect("resolve");
        let modules = vec![(vec![], graph.modules[0].program.decls.as_slice())];
        let mut interner = NameInterner::new();
        let table = collect_members(&modules, &names, &mut interner);
        (table, names)
    }

    fn sym(names: &crate::name_resolver::ResolvedNames, name: &str) -> super::SymbolId {
        *names
            .symbols
            .get(&(vec![], name.to_string()))
            .unwrap_or_else(|| panic!("`{name}` interned"))
    }

    #[test]
    fn struct_fields_get_distinct_ids_owned_by_the_struct() {
        let (t, names) = members("struct Point { x: i64, y: i64 }");
        let p = sym(&names, "Point");
        let x = t.field(p, "x").expect("x");
        let y = t.field(p, "y").expect("y");
        assert_ne!(x, y);
        assert_eq!(t.field_count(), 2);
        assert_eq!(t.field_info(x).map(|i| i.owner), Some(p));
    }

    #[test]
    fn same_field_name_on_different_types_is_a_different_id() {
        let (t, names) = members("struct A { v: i64 }\nstruct B { v: i64 }");
        let a = sym(&names, "A");
        let b = sym(&names, "B");
        assert_ne!(
            t.field(a, "v").unwrap(),
            t.field(b, "v").unwrap(),
            "the owner is part of the key"
        );
    }

    #[test]
    fn enum_variants_and_their_fields_are_interned() {
        let (t, names) = members("enum E { A { x: i64 }, B { x: i64 } }");
        let e = sym(&names, "E");
        let a = t.variant(e, "A").expect("A");
        let b = t.variant(e, "B").expect("B");
        assert_ne!(a, b);
        // Variant-qualified field names keep `A.x` and `B.x` distinct.
        assert_ne!(
            t.field(e, "A::x").unwrap(),
            t.field(e, "B::x").unwrap(),
            "variant-qualified field keys stay distinct"
        );
        assert_eq!(t.variant_count(), 2);
    }

    #[test]
    fn interning_is_reformat_stable_and_order_independent() {
        let tight = "struct S { a: i64, b: i64 } enum E { V { c: i64 } }";
        let loose = "struct S {\n\n a: i64,\n\n  b: i64,\n}\n\nenum E {\n V { c: i64 },\n}\n";
        let (t1, n1) = members(tight);
        let (t2, n2) = members(loose);

        let s1 = sym(&n1, "S");
        let s2 = sym(&n2, "S");
        assert_eq!(t1.field(s1, "a"), t2.field(s2, "a"));
        assert_eq!(t1.field(s1, "b"), t2.field(s2, "b"));

        // Two runs over the same source produce identical ids.
        let (t3, n3) = members(tight);
        let s3 = sym(&n3, "S");
        assert_eq!(t1.field(s1, "a"), t3.field(s3, "a"));
        assert_eq!(t1.field(s1, "b"), t3.field(s3, "b"));
    }

    #[test]
    fn absent_members_report_none_not_a_fabricated_id() {
        let (t, names) = members("struct Point { x: i64 }");
        let p = sym(&names, "Point");
        assert!(t.field(p, "nonesuch").is_none());
        assert!(t.variant(p, "Nope").is_none());
    }
}
