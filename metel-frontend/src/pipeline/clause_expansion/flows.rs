//! The flow sets of derived impls (RFC-0224 sections 1 and 2): the type parameters each derived `Copy`, and each
//! derived `Clone` that is not brought by a `Copy`, depends on.
//!
//! A stated `derives Copy via A + B` set is the interface as written. An unstated one is computed here, from
//! the fields, by substituting the flow of every type a field names: a parameter depends on itself, a nominal
//! application on the arguments at the positions in its own flow, a tuple, record or sized array on its
//! components, a reference and the borrowed view on nothing. Declarations are solved together by a monotone
//! fixed point over finitely many parameters, which is also the answer for a declaration that names itself
//! through a reference, whatever the source order and the module it is declared in. A declaration inside a
//! function body is solved with the others of its block, the enclosing blocks and the module in view, and a
//! local name shadows an outer one.
//!
//! A `Clone` that a `Copy` brings has the `Copy` flow (RFC-0224 section 3); a `derives Clone` without `Copy` is
//! computed the same way and reads, for a field type that derives `Copy`, that type's `Copy` flow.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::data::ast::{Decl, GenericParam, TypeExpr};
use crate::identity::symbols::{Namespace, SymbolId};
use crate::pipeline::name_resolution::name_resolver::ResolvedNames;
use crate::pipeline::parsing::module_loader::ModuleGraph;

/// Which derivation a flow belongs to.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Kind {
    Copy,
    Clone,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) enum Key {
    /// A module-level declaration.
    Id(SymbolId),
    /// A declaration inside a function body, by name within its block.
    Local(String),
}

pub(super) struct Entry {
    /// Every generic parameter of the declaration in order: the position of an argument is its index.
    generics: Vec<String>,
    /// The parameters the declaration's derivation depends on.
    set: BTreeSet<String>,
}

impl Entry {
    pub(super) fn set(&self) -> &BTreeSet<String> {
        &self.set
    }
}

/// The flows of one scope: the module's declarations, or the declarations of one function body.
#[derive(Default)]
pub(super) struct Table {
    copy: HashMap<Key, Entry>,
    clone: HashMap<Key, Entry>,
    /// Every type name this scope declares, whether or not it has a flow: it shadows an outer name.
    declared: HashSet<String>,
}

impl Table {
    fn lookup(&self, key: &Key, kind: Kind) -> Option<&Entry> {
        match kind {
            Kind::Copy => self.copy.get(key),
            // A `Copy` type's `Clone` is the provided one, with the `Copy` flow.
            Kind::Clone => self.copy.get(key).or_else(|| self.clone.get(key)),
        }
    }
}

/// The tables in view, outermost (the module's) first.
#[derive(Clone, Copy)]
pub(super) struct Scope<'a> {
    tables: &'a [&'a Table],
}

impl<'a> Scope<'a> {
    pub(super) fn new(tables: &'a [&'a Table]) -> Self {
        Self { tables }
    }

    /// The flow entry of the type `name` as written in `module`, or none: the type derives neither `Copy` nor
    /// `Clone`, or it is not declared in the program.
    fn entry(
        &self,
        name: &str,
        module: &[String],
        names: &ResolvedNames,
        kind: Kind,
    ) -> Option<&'a Entry> {
        for (depth, table) in self.tables.iter().enumerate().rev() {
            if depth == 0 {
                let id = crate::pipeline::coherence::resolve_id(names, module, name)?;
                return table.lookup(&Key::Id(id), kind);
            }
            if table.declared.contains(name) {
                return table.lookup(&Key::Local(name.to_string()), kind);
            }
        }
        None
    }

    /// The entry of the declaration being expanded, in the innermost scope that declares it.
    pub(super) fn own(
        &self,
        name: &str,
        module: &[String],
        names: &ResolvedNames,
        kind: Kind,
    ) -> Option<&'a Entry> {
        self.entry(name, module, names, kind)
    }
}

/// Whether a declaration derives `Copy`, and with which flow.
enum Copying {
    No,
    /// `derives Copy` without `via`: the flow is computed.
    Computed,
    /// `derives Copy via ...`: the set as written.
    Stated(Vec<String>),
}

/// What the computation reads of a declaration that derives `Copy` or `Clone`.
pub(super) struct FlowDecl {
    key: Key,
    module: Vec<String>,
    /// Every generic parameter in order, and the type-kinded ones among them (a row- or record-kinded parameter
    /// is rejected elsewhere).
    generics: Vec<String>,
    params: Vec<String>,
    fields: Vec<TypeExpr>,
    copy: Copying,
    /// Whether the declaration derives `Clone` itself.
    clone: bool,
}

/// How `collect` recognises the aspects of a declaration's clauses.
pub(super) struct Aspects {
    pub(super) implicit: Option<SymbolId>,
    pub(super) clone: Option<SymbolId>,
}

/// The flow declaration of a struct or enum, if it derives `Copy` or `Clone`.
pub(super) fn flow_decl(
    decl: &Decl,
    module: &[String],
    names: &ResolvedNames,
    aspects: &Aspects,
    key_of: impl Fn(&str) -> Option<Key>,
) -> Option<FlowDecl> {
    let (name, generics, clauses, fields): (&str, &[GenericParam], _, Vec<TypeExpr>) = match decl {
        Decl::Struct(sd) => (
            &sd.name,
            &sd.generics,
            &sd.clauses,
            sd.fields.iter().map(|f| f.type_ann.clone()).collect(),
        ),
        Decl::Enum(ed) => (
            &ed.name,
            &ed.generics,
            &ed.clauses,
            ed.variants
                .iter()
                .flat_map(|v| v.fields.iter().map(|f| f.type_ann.clone()))
                .collect(),
        ),
        _ => return None,
    };
    let derives = |id: Option<SymbolId>, e: &crate::data::ast::ClauseEntry| {
        id.is_some() && crate::pipeline::coherence::resolve_id(names, module, &e.name) == id
    };
    let copy_entry = clauses
        .derives
        .iter()
        .find(|e| e.from_class_keyword || derives(aspects.implicit, e));
    let clone = clauses.derives.iter().any(|e| derives(aspects.clone, e));
    if copy_entry.is_none() && !clone {
        return None;
    }
    let copy = match copy_entry {
        None => Copying::No,
        Some(e) => e.flow.as_ref().map_or(Copying::Computed, |flow| {
            Copying::Stated(flow.iter().map(|p| p.name.clone()).collect())
        }),
    };
    Some(FlowDecl {
        key: key_of(name)?,
        module: module.to_vec(),
        generics: generics.iter().map(|g| g.name.clone()).collect(),
        params: generics
            .iter()
            .filter(|g| !g.is_record && !g.is_row)
            .map(|g| g.name.clone())
            .collect(),
        fields,
        copy,
        clone,
    })
}

/// Solve a group of declarations that are in scope together: the module's, or one function body's. `outer`
/// holds the tables of the enclosing scopes, outermost first. For a module group `outer` is empty and the
/// table being built is the module table.
pub(super) fn solve(
    decls: &[FlowDecl],
    all_names: &HashSet<String>,
    outer: &[&Table],
    names: &ResolvedNames,
) -> Table {
    let mut table = Table {
        declared: all_names.clone(),
        ..Table::default()
    };
    for decl in decls {
        let entry = |set: BTreeSet<String>| Entry {
            generics: decl.generics.clone(),
            set,
        };
        match &decl.copy {
            Copying::Stated(stated) => {
                table
                    .copy
                    .insert(decl.key.clone(), entry(stated.iter().cloned().collect()));
            }
            Copying::Computed => {
                table.copy.insert(decl.key.clone(), entry(BTreeSet::new()));
            }
            Copying::No if decl.clone => {
                table.clone.insert(decl.key.clone(), entry(BTreeSet::new()));
            }
            Copying::No => {}
        }
    }
    loop {
        let mut updates: Vec<(Key, Kind, BTreeSet<String>)> = Vec::new();
        {
            let mut tables: Vec<&Table> = outer.to_vec();
            tables.push(&table);
            let scope = Scope::new(&tables);
            for decl in decls {
                // A stated flow is the interface as written; only the others are computed.
                let kind = match &decl.copy {
                    Copying::Computed => Kind::Copy,
                    Copying::No if decl.clone => Kind::Clone,
                    Copying::Stated(_) | Copying::No => continue,
                };
                let deps = dependence(
                    &decl.fields,
                    &decl.params,
                    &decl.module,
                    names,
                    &scope,
                    kind,
                );
                updates.push((decl.key.clone(), kind, deps));
            }
        }
        let mut changed = false;
        for (key, kind, deps) in updates {
            let map = if kind == Kind::Copy {
                &mut table.copy
            } else {
                &mut table.clone
            };
            if let Some(entry) = map.get_mut(&key) {
                for param in deps {
                    changed |= entry.set.insert(param);
                }
            }
        }
        if !changed {
            break;
        }
    }
    table
}

/// The module-level declarations of a program's modules, and the table of their flows.
pub(super) fn module_table(graph: &ModuleGraph, names: &ResolvedNames, aspects: &Aspects) -> Table {
    let mut decls = Vec::new();
    for module in &graph.modules {
        for decl in &module.program.decls {
            let key_of = |name: &str| {
                names
                    .symbols
                    .get(&(
                        module.module_path.clone(),
                        Namespace::Type,
                        name.to_string(),
                    ))
                    .map(|id| Key::Id(*id))
            };
            if let Some(flow) = flow_decl(decl, &module.module_path, names, aspects, key_of) {
                decls.push(flow);
            }
        }
    }
    // The module table resolves by `SymbolId`, not by name: `declared` is only for local scopes.
    solve(&decls, &HashSet::new(), &[], names)
}

/// The table of the type declarations in one function body, solved with the enclosing scopes in view.
pub(super) fn local_table(
    stmts: &[Decl],
    module: &[String],
    outer: &[&Table],
    names: &ResolvedNames,
    aspects: &Aspects,
) -> Table {
    let mut decls = Vec::new();
    let mut declared = HashSet::new();
    for decl in stmts {
        match decl {
            Decl::Struct(sd) => {
                declared.insert(sd.name.clone());
            }
            Decl::Enum(ed) => {
                declared.insert(ed.name.clone());
            }
            _ => {}
        }
        if let Some(flow) = flow_decl(decl, module, names, aspects, |name| {
            Some(Key::Local(name.to_string()))
        }) {
            decls.push(flow);
        }
    }
    solve(&decls, &declared, outer, names)
}

/// The type parameters (of `params`) a set of field types' derivation depends on, by the rule of each type
/// form. A nominal that has no stored flow (it derives neither `Copy` nor `Clone`) and any form this does not
/// look through depend on every argument that mentions a parameter, which is the conservative reading.
pub(super) fn dependence(
    fields: &[TypeExpr],
    params: &[String],
    module: &[String],
    names: &ResolvedNames,
    scope: &Scope<'_>,
    kind: Kind,
) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for ty in fields {
        collect(ty, params, module, names, scope, kind, &mut out);
    }
    out
}

fn collect(
    ty: &TypeExpr,
    params: &[String],
    module: &[String],
    names: &ResolvedNames,
    scope: &Scope<'_>,
    kind: Kind,
    out: &mut BTreeSet<String>,
) {
    let recurse = |t: &TypeExpr, out: &mut BTreeSet<String>| {
        collect(t, params, module, names, scope, kind, out);
    };
    match ty {
        TypeExpr::Named(name, args, _) => {
            if args.is_empty() && params.iter().any(|p| p == name) {
                out.insert(name.clone());
                return;
            }
            match scope.entry(name, module, names, kind) {
                Some(entry) => {
                    for (i, arg) in args.iter().enumerate() {
                        if entry.generics.get(i).is_some_and(|g| entry.set.contains(g)) {
                            recurse(arg, out);
                        }
                    }
                }
                None => args.iter().for_each(|arg| recurse(arg, out)),
            }
        }
        TypeExpr::Reference(_) | TypeExpr::Array(_) => {}
        TypeExpr::MutReference(inner) | TypeExpr::SizedArray(inner, _) => recurse(inner, out),
        TypeExpr::Tuple(items) => items.iter().for_each(|t| recurse(t, out)),
        TypeExpr::Record(fields) => fields.iter().for_each(|(_, t)| recurse(t, out)),
        _ => out.extend(params.iter().cloned()),
    }
}
