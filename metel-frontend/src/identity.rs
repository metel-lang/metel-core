//! The frontend-owned resolved-identity model (ADR-0054).
//!
//! After lexical resolution and inference, the frontend *freezes* every
//! successfully inferred body into an ID-complete representation. From that
//! point on, no compiler or evaluator phase is allowed to determine the
//! meaning of a program expression, type, member, field, method, or runtime
//! binding by looking a source spelling up in a textual environment
//! (metel-core#1047).
//!
//! This module defines the identity domains that carry that meaning and the
//! containers that hold them. It deliberately does *not* migrate the existing
//! passes onto them — that is #1049 (lexical resolution), #1050 (typed IR and
//! tooling), #1051 (type-directed selection), and #1052 (evaluator). What lands
//! here is the contract those issues consume, plus a structural allocator with
//! adversarial fixtures.
//!
//! # Allocation is structural, not positional
//!
//! Per the 2026-09-10 amendment to ADR-0054, an identity is a function of *what
//! an entity is*, never of where its text sits or the order a traversal reached
//! it:
//!
//! - [`SymbolId`] (defined in [`crate::symbols`]) keys on
//!   `(canonical module path, declared name, overload ordinal)`.
//! - [`LocalId`] and [`RefId`] key on `(owner, `[`LexicalPath`]`)` — the chain
//!   of structural positions from the owning body to the binding or use. They
//!   are the stable hash of that key, so inserting an unrelated binding earlier
//!   in the same body does not renumber a later one, and reformatting or adding
//!   blank lines changes nothing.
//! - [`ModuleId`] keys on the canonical (alias-dereferenced) module path.
//! - [`FieldId`] / [`VariantId`] key on `(owning SymbolId, declared member
//!   name)` — populated by #1051, declared here.
//!
//! None of this promises identity persistence across *structural* edits
//! (renaming a binding, moving a declaration between modules, reordering an
//! overload set), nor across processes. That is a later
//! incremental-compilation decision; structural allocation is the part that is
//! cheap now and expensive to retrofit, so it is settled here.

use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use crate::ast::Span;

pub use crate::symbols::SymbolId;

mod lexical_path;
pub use lexical_path::{LexicalPath, LexicalSeg};

mod allocate;
pub use allocate::{allocate_graph, allocate_module, Allocation, GraphModuleNav, ModuleNav};

mod position;
pub use position::{PositionHit, PositionIndex};

mod member;
pub use member::{collect_members, collect_members_for_graph, MemberInfo, MemberTable};

#[cfg(test)]
mod tests;

// ── Identity domains ─────────────────────────────────────────────────────────

/// Identity of a lexical binding: a parameter, a `let` / `mut` binding, a
/// nested function, a loop binding, a closure parameter, or a pattern binding.
///
/// The wrapped value is the stable hash of the binding's structural key
/// (`(owner, `[`LexicalPath`]`)`); it is opaque and never shown to a user.
/// Shadowed bindings have distinct lexical paths and therefore distinct
/// `LocalId`s.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub u64);

/// Identity of a *reference site* — one use of a name in expression position.
///
/// Keyed structurally the same way as [`LocalId`] (`(owner, `[`LexicalPath`]`)`
/// with a [`LexicalSeg::Use`] leaf) so that a resolved reference survives edits
/// elsewhere in the file. This is the durable key of
/// [`ResolutionMap::references`]; byte-offset lookups go through
/// [`PositionIndex`], never through a span map.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RefId(pub u64);

/// Identity of a module namespace, interned from its canonical
/// (alias-dereferenced) module path.
///
/// A module is not an ordinary runtime value binding: `ModuleId` is *not* a
/// [`BindingId`] variant and never enters an activation frame or value
/// registry. A navigation query that wants a module location asks for a
/// `ModuleId` explicitly (see [`ModuleTable`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModuleId(pub u32);

/// Identity of a nominal field declaration (`(owning SymbolId, field name)`).
///
/// Declared here; assigned by #1051 when type-directed selection is frozen.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FieldId(pub u32);

/// Identity of a nominal enum variant declaration (`(owning SymbolId, variant
/// name)`).
///
/// Declared here; assigned by #1051.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VariantId(pub u32);

/// Interned source spelling of an identifier. Survives resolution as diagnostic
/// and rendering metadata, or as the input to an ID-keyed constraint. It is
/// never a textual map key after parsing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NameId(pub u32);

/// Interned structural record / row field spelling. Separate from [`NameId`]
/// because a row label is not a declaration owned by one nominal type
/// (ADR-0054).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LabelId(pub u32);

/// Identity of a value definition or a value use: either a globally addressable
/// declaration ([`SymbolId`]) or a lexical binding ([`LocalId`]).
///
/// This is what a resolved value reference carries in the frozen IR. It is a
/// closed set — a use is global or local, never "absent, guess from the name".
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BindingId {
    /// A module-level declaration, method, constructor, or imported name
    /// resolved to its defining declaration.
    Global(SymbolId),
    /// A lexical binding in the enclosing body.
    Local(LocalId),
}

impl BindingId {
    /// The global identity, if this is a global binding.
    #[must_use]
    pub fn as_global(self) -> Option<SymbolId> {
        match self {
            BindingId::Global(id) => Some(id),
            BindingId::Local(_) => None,
        }
    }

    /// The local identity, if this is a lexical binding.
    #[must_use]
    pub fn as_local(self) -> Option<LocalId> {
        match self {
            BindingId::Local(id) => Some(id),
            BindingId::Global(_) => None,
        }
    }
}

// ── Reference resolution ─────────────────────────────────────────────────────

/// The resolution of one reference site. Total: every [`RefId`] in a
/// [`ResolutionMap`] has one of these, so a later phase never reads "no entry"
/// and guesses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resolution {
    /// The reference resolves to this binding.
    Resolved(BindingId),
    /// The reference does not resolve. This is explicit diagnostic state and
    /// only ever lives in the *pre-freeze* map: a body that still contains an
    /// unresolved reference fails typechecking and is never frozen, so no
    /// post-freeze phase sees one.
    Unresolved(UnresolvedRef),
}

impl Resolution {
    /// The resolved binding, if this reference resolved.
    #[must_use]
    pub fn binding(&self) -> Option<BindingId> {
        match self {
            Resolution::Resolved(b) => Some(*b),
            Resolution::Unresolved(_) => None,
        }
    }

    /// Whether this reference failed to resolve.
    #[must_use]
    pub fn is_unresolved(&self) -> bool {
        matches!(self, Resolution::Unresolved(_))
    }
}

/// An unresolved reference site: the spelling that was looked up and why it
/// failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnresolvedRef {
    /// The interned spelling as written at the use site.
    pub spelling: NameId,
    /// Why resolution failed — carries the T0003 / T0009 distinction forward.
    pub cause: UnresolvedCause,
}

/// Why a reference did not resolve.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnresolvedCause {
    /// No binding with this spelling is in scope (diagnostic T0003).
    NotInScope,
    /// More than one binding is equally visible and nothing disambiguates
    /// (e.g. two globs). The candidates are recorded for the diagnostic.
    Ambiguous(Vec<BindingId>),
    /// A binding with this spelling exists but is not visible here — e.g. a
    /// private declaration in another module (diagnostic T0009).
    VisibilityDenied(SymbolId),
}

// ── ResolutionMap ────────────────────────────────────────────────────────────

/// The durable resolved artifact for one analysis run.
///
/// Every key is an identity. No field is keyed by [`Span`] or by `String`; a
/// [`Span`] appears only as metadata *inside* [`DefinitionInfo`]. Byte-offset
/// queries go through the separate, rebuilt-per-snapshot [`PositionIndex`].
#[derive(Debug, Clone, Default)]
pub struct ResolutionMap {
    /// Every value definition reachable in this run, by identity.
    pub definitions: HashMap<BindingId, DefinitionInfo>,
    /// Every value reference site, by identity. Total (see [`Resolution`]).
    pub references: HashMap<RefId, Resolution>,
}

impl ResolutionMap {
    /// Merge another map into this one. Used to assemble a whole-graph map from
    /// per-module walks; the structural keys never collide across modules
    /// because the owner chain is rooted in a module-unique [`SymbolId`].
    pub fn extend_from(&mut self, other: ResolutionMap) {
        self.definitions.extend(other.definitions);
        self.references.extend(other.references);
    }

    /// Whether any reference site is still unresolved. A body whose references
    /// are all resolved is eligible for the freeze; one with an unresolved
    /// reference is not (ADR-0054).
    #[must_use]
    pub fn has_unresolved(&self) -> bool {
        self.references.values().any(Resolution::is_unresolved)
    }

    /// All reference sites that resolve to `binding` — the reverse lookup
    /// find-references is built on (#1050). Linear today; #1050 adds an index
    /// if the LSP needs it.
    pub fn references_to(&self, binding: BindingId) -> impl Iterator<Item = RefId> + '_ {
        self.references
            .iter()
            .filter_map(move |(rid, res)| (res.binding() == Some(binding)).then_some(*rid))
    }
}

/// Metadata about one value definition. The identity is the map key; this is
/// everything else a diagnostic or a tooling query needs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefinitionInfo {
    /// What kind of binding this is.
    pub kind: DefinitionKind,
    /// The interned declared spelling, for rendering.
    pub name: NameId,
    /// The declaration site, for go-to-definition and diagnostics.
    pub span: Span,
}

/// The syntactic category of a value definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefinitionKind {
    /// A function parameter.
    Param,
    /// A closure parameter.
    ClosureParam,
    /// A `let` binding.
    Let,
    /// A `mut` binding.
    Mut,
    /// A binding introduced by a pattern (destructuring, match arm).
    PatternBinding,
    /// A `for … in` / C-style loop binding.
    LoopBinding,
    /// A function declared inside a body.
    NestedFn,
    /// A module-level declaration. Detailed global kinds (type, aspect, method,
    /// constructor, overload) stay on [`SymbolId`]'s own tables; this is only
    /// what the value-binding view needs.
    Global,
}

// ── Name interning ──────────────────────────────────────────────────────────

/// Interns identifier spellings to [`NameId`] and row labels to [`LabelId`].
///
/// Owned by the resolver, handed to the frozen artifact by value, and treated
/// as immutable thereafter. Equal spellings intern equal, so this is
/// deterministic per resolved module graph and independent of traversal order.
#[derive(Debug, Clone, Default)]
pub struct NameInterner {
    names: Interner,
    labels: Interner,
}

impl NameInterner {
    /// A fresh, empty interner.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern an identifier spelling.
    pub fn name(&mut self, spelling: &str) -> NameId {
        NameId(self.names.intern(spelling))
    }

    /// Intern a row / record label spelling.
    pub fn label(&mut self, spelling: &str) -> LabelId {
        LabelId(self.labels.intern(spelling))
    }

    /// Resolve an interned identifier back to its spelling (rendering,
    /// diagnostics).
    #[must_use]
    pub fn name_str(&self, id: NameId) -> Option<&str> {
        self.names.lookup(id.0)
    }

    /// Resolve an interned label back to its spelling.
    #[must_use]
    pub fn label_str(&self, id: LabelId) -> Option<&str> {
        self.labels.lookup(id.0)
    }
}

/// A minimal string interner: spelling → dense `u32`, with a reverse table.
#[derive(Debug, Clone, Default)]
struct Interner {
    map: HashMap<String, u32>,
    rev: Vec<String>,
}

impl Interner {
    fn intern(&mut self, s: &str) -> u32 {
        if let Some(&id) = self.map.get(s) {
            return id;
        }
        let id = u32::try_from(self.rev.len()).expect("interner overflow");
        self.rev.push(s.to_string());
        self.map.insert(s.to_string(), id);
        id
    }

    fn lookup(&self, id: u32) -> Option<&str> {
        self.rev.get(id as usize).map(String::as_str)
    }
}

// ── Module identity ─────────────────────────────────────────────────────────

/// Interns canonical module paths to [`ModuleId`] and records where each module
/// is declared, for module-segment go-to-definition.
///
/// The path handed in must already be canonical — alias dereferencing
/// (`crate::name_resolver::canonical_path`) happens before interning, so
/// `["a", "b"]` and an alias `["x", "y"] -> ["a", "b"]` land on the same id.
#[derive(Debug, Clone, Default)]
pub struct ModuleTable {
    map: HashMap<Vec<String>, ModuleId>,
    info: Vec<ModuleInfo>,
}

impl ModuleTable {
    /// A fresh, empty table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern a canonical module path, recording its declaration span the first
    /// time it is seen. Passing `None` for `decl_span` (e.g. the crate root, or
    /// a module first seen only as a path prefix) leaves it unset; a later call
    /// with a real span fills it in.
    ///
    /// # Panics
    /// Panics if more than `u32::MAX` distinct module paths are interned.
    pub fn intern(&mut self, canonical_path: &[String], decl_span: Option<Span>) -> ModuleId {
        if let Some(&id) = self.map.get(canonical_path) {
            if let Some(span) = decl_span {
                let slot = &mut self.info[id.0 as usize];
                if slot.decl_span.is_none() {
                    slot.decl_span = Some(span);
                }
            }
            return id;
        }
        let id = ModuleId(u32::try_from(self.info.len()).expect("module table overflow"));
        self.info.push(ModuleInfo {
            canonical_path: canonical_path.to_vec(),
            decl_span,
        });
        self.map.insert(canonical_path.to_vec(), id);
        id
    }

    /// Look up a module's recorded metadata.
    #[must_use]
    pub fn get(&self, id: ModuleId) -> Option<&ModuleInfo> {
        self.info.get(id.0 as usize)
    }

    /// The id a canonical path was interned under, if any.
    #[must_use]
    pub fn lookup(&self, canonical_path: &[String]) -> Option<ModuleId> {
        self.map.get(canonical_path).copied()
    }
}

/// What is known about one module namespace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleInfo {
    /// The canonical (alias-dereferenced) path segments.
    pub canonical_path: Vec<String>,
    /// The `mod` site (or the module file), for go-to-definition on a module
    /// segment of a qualified path. `None` for the crate root and for modules
    /// only ever seen as a path prefix.
    pub decl_span: Option<Span>,
}

// ── Structural hashing ──────────────────────────────────────────────────────

/// Hash a structural key `(owner, path)` to the opaque `u64` an identity wraps.
///
/// Uses [`DefaultHasher`], whose seed is fixed, so the result is deterministic
/// for a given key on a given target. The [`allocate`] module keeps a reverse
/// table and asserts there is no genuine collision.
pub(crate) fn structural_hash(owner: BindingId, path: &LexicalPath) -> u64 {
    let mut h = DefaultHasher::new();
    // Domain-separate so a LocalId key and a RefId key over the same path (the
    // latter has a `Use` leaf, but be defensive) can never collide.
    "metel.identity.v1".hash(&mut h);
    owner.hash(&mut h);
    path.hash(&mut h);
    h.finish()
}
