use std::collections::HashMap;
use std::fmt;
use std::sync::atomic::{AtomicU32, Ordering};

/// A stable, opaque identity for a resolved symbol (a unique `(source_module, source_name)` pair).
///
/// Assigned during name resolution and threaded through the compilation pipeline so that later
/// stages can identify the same declaration regardless of local alias or path spelling.
/// Diagnostic output always uses the original path spelling; `SymbolId` is for structural identity
/// only and is never surfaced to the user.
///
/// The variants are the kinds of symbol, so two kinds cannot collide and no numeric range has to be
/// kept apart from another (ADR-0065, replacing the declared ranges of metel-core#1542). The payloads
/// are private index types: an id is compared, hashed, matched and passed, and is minted only by the
/// allocator that owns its kind.
///
/// | Variant | Minted by | Meaning |
/// |---|---|---|
/// | `Builtin` | nothing (a fixed set) | the primitives, core types and core aspects the language knows by id |
/// | `Declared` | [`SymbolTable`] | a named top-level declaration, or an impl/aspect method key |
/// | `BlockLocal` | [`BlockLocalAllocator`] | a struct or enum declared inside a block |
/// | `Overload` | `type_checking::overload` | a free-function overload definition (METEL-180) |
///
/// `Overload` is one temporary variant fed by a process-global counter; ADR-0065 step 2 splits it into
/// a structural per-module id and an id for the embedded `std::core` table.
///
/// There is deliberately no `Ord`: an order over kinds carries no meaning code should rely on.
///
/// Code outside this crate cannot build a payload, or call the allocator that would mint an
/// `Overload`, from a number (these are the regression guards for ADR-0065 Decision 2):
///
/// ```compile_fail,E0423
/// use metel_frontend::identity::symbols::{DeclaredIndex, SymbolId};
/// let _ = SymbolId::Declared(DeclaredIndex(1));
/// ```
///
/// ```compile_fail,E0603
/// use metel_frontend::identity::symbols::allocate_overload;
/// use std::sync::atomic::AtomicU32;
/// let _ = allocate_overload(&AtomicU32::new(12345));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolId {
    Builtin(Builtin),
    Declared(DeclaredIndex),
    BlockLocal(BlockLocalIndex),
    Overload(OverloadIndex),
}

/// Declares a private-payload index type. It prints as the bare number, so `SymbolId::Declared(42)`
/// debugs as `Declared(42)`.
macro_rules! symbol_index {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name(u32);

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Debug::fmt(&self.0, f)
            }
        }
    };
}

symbol_index!(
    /// The index of a [`SymbolId::Declared`]; built only by [`SymbolTable`].
    DeclaredIndex
);
symbol_index!(
    /// The index of a [`SymbolId::BlockLocal`]; built only by [`BlockLocalAllocator`].
    BlockLocalIndex
);
symbol_index!(
    /// The index of a [`SymbolId::Overload`]; built only by `allocate_overload`, which is crate-private.
    OverloadIndex
);

impl SymbolId {
    /// A `Declared` id for a test, so unit tests inside this crate can name an id without
    /// running the resolver. Tests in other crates intern through a [`SymbolTable`].
    #[cfg(test)]
    #[must_use]
    pub(crate) const fn declared_for_test(index: u32) -> SymbolId {
        SymbolId::Declared(DeclaredIndex(index))
    }
}

// ── The builtin symbols (metel-core#1542) ─────────────────────────────────────

/// Whether a builtin names a type or an aspect.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinKind {
    Type,
    Aspect,
}

/// Declares [`Builtin`] from one list: each entry gives the variant, its `std::core` name and its
/// kind. The variant, the name, the kind and [`Builtin::ALL`] come from that one line, so a builtin
/// cannot be added to one of them and missed in another, and `name` / `kind` are exhaustive matches.
macro_rules! builtins {
    ($($variant:ident, $name:literal, $kind:ident;)*) => {
        /// A symbol the language knows by identity: the primitives, the core types and the core
        /// aspects.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum Builtin {
            $($variant,)*
        }

        impl Builtin {
            /// Every builtin, in declaration order.
            pub const ALL: &'static [Builtin] = &[$(Builtin::$variant,)*];

            /// The builtin's name in `std::core`.
            #[must_use]
            pub const fn name(self) -> &'static str {
                match self {
                    $(Builtin::$variant => $name,)*
                }
            }

            /// Whether the builtin is a type or an aspect.
            #[must_use]
            pub const fn kind(self) -> BuiltinKind {
                match self {
                    $(Builtin::$variant => BuiltinKind::$kind,)*
                }
            }
        }
    };
}

builtins! {
    Boolean, "boolean", Type;
    String, "String", Type;
    Char, "Char", Type;
    I8, "i8", Type;
    I16, "i16", Type;
    I32, "i32", Type;
    I64, "i64", Type;
    U8, "u8", Type;
    U16, "u16", Type;
    U32, "u32", Type;
    U64, "u64", Type;
    F32, "f32", Type;
    F64, "f64", Type;
    List, "List", Type;
    Perhaps, "Perhaps", Type;
    Result, "Result", Type;
    Range, "Range", Type;
    RangeInclusive, "RangeInclusive", Type;
    Display, "Display", Aspect;
    Iterable, "Iterable", Aspect;
    From, "From", Aspect;
}

impl Builtin {
    /// The builtin's `SymbolId`.
    #[must_use]
    pub const fn id(self) -> SymbolId {
        SymbolId::Builtin(self)
    }

    /// The builtin named `name` of `kind`, if there is one.
    #[must_use]
    pub fn from_name(name: &str, kind: BuiltinKind) -> Option<Builtin> {
        Builtin::ALL
            .iter()
            .copied()
            .find(|b| b.kind() == kind && b.name() == name)
    }
}

// The named ids the rest of the code uses.
pub const SYM_TYPE_BOOLEAN: SymbolId = Builtin::Boolean.id();
pub const SYM_TYPE_STRING: SymbolId = Builtin::String.id();
pub const SYM_TYPE_CHAR: SymbolId = Builtin::Char.id();
pub const SYM_TYPE_I8: SymbolId = Builtin::I8.id();
pub const SYM_TYPE_I16: SymbolId = Builtin::I16.id();
pub const SYM_TYPE_I32: SymbolId = Builtin::I32.id();
pub const SYM_TYPE_I64: SymbolId = Builtin::I64.id();
pub const SYM_TYPE_U8: SymbolId = Builtin::U8.id();
pub const SYM_TYPE_U16: SymbolId = Builtin::U16.id();
pub const SYM_TYPE_U32: SymbolId = Builtin::U32.id();
pub const SYM_TYPE_U64: SymbolId = Builtin::U64.id();
pub const SYM_TYPE_F32: SymbolId = Builtin::F32.id();
pub const SYM_TYPE_F64: SymbolId = Builtin::F64.id();
pub const SYM_TYPE_LIST: SymbolId = Builtin::List.id();
pub const SYM_TYPE_PERHAPS: SymbolId = Builtin::Perhaps.id();
pub const SYM_TYPE_RESULT: SymbolId = Builtin::Result.id();
pub const SYM_TYPE_RANGE: SymbolId = Builtin::Range.id();
pub const SYM_TYPE_RANGE_INCLUSIVE: SymbolId = Builtin::RangeInclusive.id();
pub const SYM_ASPECT_DISPLAY: SymbolId = Builtin::Display.id();
pub const SYM_ASPECT_ITERABLE: SymbolId = Builtin::Iterable.id();
pub const SYM_ASPECT_FROM: SymbolId = Builtin::From.id();

/// The well-known id of the builtin named `name` of `kind`, if there is one.
#[must_use]
pub fn builtin_symbol(name: &str, kind: BuiltinKind) -> Option<SymbolId> {
    Builtin::from_name(name, kind).map(Builtin::id)
}

// ── Allocators ────────────────────────────────────────────────────────────────

/// Mints [`SymbolId::BlockLocal`] ids for struct and enum declarations inside blocks.
#[derive(Debug, Clone, Default)]
pub struct BlockLocalAllocator {
    next: u32,
}

impl BlockLocalAllocator {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The next unused block-local id.
    ///
    /// # Panics
    /// Panics when the index space is exhausted rather than wrapping to an id already handed out.
    pub fn fresh(&mut self) -> SymbolId {
        let index = self.next;
        self.next = index
            .checked_add(1)
            .expect("the block-local SymbolId space is exhausted");
        SymbolId::BlockLocal(BlockLocalIndex(index))
    }

    /// Move this allocator past every id `other` has handed out, so ids minted from here on cannot
    /// repeat one `other` minted. Never moves backwards: an allocator already ahead of `other`
    /// stays where it is.
    ///
    /// A block-local id is minted by the registry of the module being checked, and that registry
    /// absorbs its dependencies' definitions with `merge_from`. Without this, each module's fresh
    /// registry would start again at index 0 and its first local type would overwrite the
    /// dependency's entry for the same id.
    pub fn advance_past(&mut self, other: &BlockLocalAllocator) {
        self.next = self.next.max(other.next);
    }
}

/// Take the next [`SymbolId::Overload`] id from `counter`.
///
/// The counter is a process-global in `type_checking::overload` (`LIMIT-NAME-RESOLUTION-002`;
/// ADR-0065 step 2 removes it).
///
/// # Panics
/// Panics when the index space is exhausted rather than wrapping to an id already handed out.
pub(crate) fn allocate_overload(counter: &AtomicU32) -> SymbolId {
    // A compare-exchange loop, not `fetch_update`/`try_update`: the former is deprecated on current
    // stable and the latter is not on every toolchain this crate builds with.
    let mut index = counter.load(Ordering::Relaxed);
    loop {
        let next = index
            .checked_add(1)
            .expect("the overload SymbolId space is exhausted");
        match counter.compare_exchange_weak(index, next, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(_) => return SymbolId::Overload(OverloadIndex(index)),
            Err(current) => index = current,
        }
    }
}

// ── SymbolTable ───────────────────────────────────────────────────────────────

/// Intern table: maps `(source_module, source_name)` → stable `SymbolId`.
/// Pre-populated with builtin entries so that imports of stdlib names get the
/// same well-known IDs as the `SYM_*` constants above.
pub struct SymbolTable {
    map: HashMap<(Vec<String>, String), SymbolId>,
    next_id: u32,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolTable {
    #[must_use]
    // arch-implements: ["arch.name-resolution.requirement-1"]
    // limit: ["LIMIT-NAME-RESOLUTION-004"]
    pub fn new() -> Self {
        let std_core = || vec!["std".to_string(), "core".to_string()];
        let map = Builtin::ALL
            .iter()
            .map(|b| ((std_core(), b.name().to_string()), b.id()))
            .collect();
        Self { map, next_id: 0 }
    }

    /// Return the existing `SymbolId` for `(source_module, source_name)`, or assign
    /// a fresh one. Two calls with identical arguments always return the same id.
    ///
    /// # Panics
    /// Panics when the declared index space is exhausted rather than wrapping.
    // arch-implements: ["arch.name-resolution.requirement-1"]
    pub fn intern(&mut self, source_module: &[String], source_name: &str) -> SymbolId {
        let key = (source_module.to_vec(), source_name.to_string());
        *self.map.entry(key).or_insert_with(|| {
            let index = self.next_id;
            self.next_id = index
                .checked_add(1)
                .expect("the declared SymbolId space is exhausted");
            SymbolId::Declared(DeclaredIndex(index))
        })
    }

    /// The interned symbols.
    #[must_use]
    pub fn map(&self) -> &HashMap<(Vec<String>, String), SymbolId> {
        &self.map
    }

    /// The interned symbols, consuming the table.
    #[must_use]
    pub fn into_map(self) -> HashMap<(Vec<String>, String), SymbolId> {
        self.map
    }

    /// A table whose next declared index is `next_id`, for tests that exercise the end of the space.
    #[cfg(test)]
    fn with_next_id(next_id: u32) -> Self {
        Self {
            next_id,
            ..Self::new()
        }
    }
}

#[cfg(test)]
mod architecture_evidence_tests {
    use super::*;

    fn std_core() -> Vec<String> {
        vec!["std".to_string(), "core".to_string()]
    }

    // arch-verifies: ["arch.name-resolution.requirement-1"]
    #[test]
    fn builtin_std_core_declarations_are_pre_seeded_at_their_fixed_ids() {
        let mut table = SymbolTable::new();
        assert_eq!(table.intern(&std_core(), "Perhaps"), SYM_TYPE_PERHAPS);
        assert_eq!(table.intern(&std_core(), "String"), SYM_TYPE_STRING);
        assert_eq!(table.intern(&std_core(), "Display"), SYM_ASPECT_DISPLAY);
    }

    // arch-verifies: ["arch.name-resolution.requirement-1"]
    #[test]
    fn declared_symbols_are_distinct_from_every_builtin_and_allocated_in_order() {
        let mut table = SymbolTable::new();
        let first = table.intern(&["app".to_string()], "Widget");
        let second = table.intern(&["app".to_string()], "Gadget");
        assert_eq!(first, SymbolId::Declared(DeclaredIndex(0)));
        assert_eq!(second, SymbolId::Declared(DeclaredIndex(1)));
        assert_eq!(
            table.intern(&["app".to_string()], "Widget"),
            first,
            "interning the same key again returns the same id"
        );
        for builtin in Builtin::ALL {
            assert_ne!(first, builtin.id());
            assert_ne!(second, builtin.id());
        }
    }

    #[test]
    fn the_same_index_in_two_kinds_is_two_different_symbols() {
        let declared = SymbolId::Declared(DeclaredIndex(5));
        let block_local = SymbolId::BlockLocal(BlockLocalIndex(5));
        let overload = SymbolId::Overload(OverloadIndex(5));
        assert_ne!(declared, block_local);
        assert_ne!(declared, overload);
        assert_ne!(block_local, overload);
        let all: std::collections::HashSet<_> = [declared, block_local, overload].into();
        assert_eq!(all.len(), 3, "and they hash apart as well");
    }

    #[test]
    fn debug_output_names_the_kind() {
        assert_eq!(
            format!("{:?}", SymbolId::Declared(DeclaredIndex(42))),
            "Declared(42)"
        );
        assert_eq!(
            format!("{:?}", SymbolId::BlockLocal(BlockLocalIndex(7))),
            "BlockLocal(7)"
        );
        assert_eq!(
            format!("{:?}", SymbolId::Overload(OverloadIndex(3))),
            "Overload(3)"
        );
        assert_eq!(format!("{SYM_TYPE_RESULT:?}"), "Builtin(Result)");
    }

    #[test]
    fn builtin_ids_and_names_are_unique() {
        let mut ids = std::collections::HashSet::new();
        let mut names = std::collections::HashSet::new();
        for builtin in Builtin::ALL {
            let name = builtin.name();
            assert!(ids.insert(builtin.id()), "duplicate builtin id ({name})");
            assert!(
                names.insert((name, builtin.kind() as u8)),
                "duplicate builtin name {name}"
            );
        }
        assert_eq!(Builtin::ALL.len(), 21);
        let kinds = |k| Builtin::ALL.iter().filter(|b| b.kind() == k).count();
        assert_eq!(kinds(BuiltinKind::Type), 18);
        assert_eq!(kinds(BuiltinKind::Aspect), 3);
    }

    #[test]
    fn the_named_ids_are_the_builtins() {
        assert_eq!(SYM_TYPE_BOOLEAN, Builtin::Boolean.id());
        assert_eq!(SYM_TYPE_RANGE_INCLUSIVE, Builtin::RangeInclusive.id());
        assert_eq!(SYM_ASPECT_DISPLAY, Builtin::Display.id());
        assert_eq!(SYM_ASPECT_FROM, Builtin::From.id());
    }

    /// Builtin types the language provides itself; they are not declared in `std::core`.
    const INTRINSIC_BUILTINS: [&str; 15] = [
        "boolean",
        "String",
        "Char",
        "i8",
        "i16",
        "i32",
        "i64",
        "u8",
        "u16",
        "u32",
        "u64",
        "f32",
        "f64",
        "Range",
        "RangeInclusive",
    ];

    #[test]
    fn every_builtin_is_declared_in_std_core_or_is_an_intrinsic_type() {
        use crate::data::ast::Decl;
        let declared: std::collections::HashSet<&str> = crate::stdlib::core_program()
            .decls
            .iter()
            .filter_map(|d| match d {
                Decl::Struct(s) => Some(s.name.as_str()),
                Decl::Enum(e) => Some(e.name.as_str()),
                Decl::Aspect(a) => Some(a.name.as_str()),
                _ => None,
            })
            .collect();
        for builtin in Builtin::ALL {
            let name = builtin.name();
            let intrinsic = INTRINSIC_BUILTINS.contains(&name);
            assert!(
                declared.contains(name) != intrinsic,
                "builtin `{name}` must be either declared in std::core or an intrinsic type, not both and not neither"
            );
        }
    }

    #[test]
    fn the_table_is_seeded_with_exactly_the_builtins() {
        let table = SymbolTable::new();
        assert_eq!(table.map().len(), Builtin::ALL.len());
        for builtin in Builtin::ALL {
            assert_eq!(
                table.map().get(&(std_core(), builtin.name().to_string())),
                Some(&builtin.id()),
                "{}",
                builtin.name()
            );
        }
    }

    #[test]
    fn builtin_symbol_looks_up_by_name_and_kind() {
        assert_eq!(
            builtin_symbol("Display", BuiltinKind::Aspect),
            Some(SYM_ASPECT_DISPLAY)
        );
        assert_eq!(builtin_symbol("Display", BuiltinKind::Type), None);
        assert_eq!(
            builtin_symbol("Perhaps", BuiltinKind::Type),
            Some(SYM_TYPE_PERHAPS)
        );
        assert_eq!(builtin_symbol("NotABuiltin", BuiltinKind::Type), None);
    }

    #[test]
    #[should_panic(expected = "the declared SymbolId space is exhausted")]
    fn interning_past_the_end_of_the_declared_space_panics_instead_of_wrapping() {
        let mut table = SymbolTable::with_next_id(u32::MAX - 1);
        let last = table.intern(&["app".to_string()], "Last");
        assert_eq!(last, SymbolId::Declared(DeclaredIndex(u32::MAX - 1)));
        let _ = table.intern(&["app".to_string()], "OneTooMany");
    }

    #[test]
    fn the_block_local_allocator_hands_out_distinct_consecutive_ids() {
        let mut alloc = BlockLocalAllocator::new();
        let first = alloc.fresh();
        let second = alloc.fresh();
        assert_eq!(first, SymbolId::BlockLocal(BlockLocalIndex(0)));
        assert_eq!(second, SymbolId::BlockLocal(BlockLocalIndex(1)));
        assert_ne!(first, second);
    }

    #[test]
    fn advancing_past_another_allocator_skips_the_ids_it_handed_out() {
        let mut dependency = BlockLocalAllocator::new();
        let first = dependency.fresh();
        let second = dependency.fresh();

        let mut module = BlockLocalAllocator::new();
        module.advance_past(&dependency);
        let own = module.fresh();
        assert_ne!(own, first);
        assert_ne!(own, second);
        assert_eq!(own, SymbolId::BlockLocal(BlockLocalIndex(2)));
    }

    #[test]
    fn advancing_past_never_moves_an_allocator_backwards() {
        let behind = BlockLocalAllocator::new();
        let mut ahead = BlockLocalAllocator::new();
        let _ = ahead.fresh();
        let _ = ahead.fresh();
        let _ = ahead.fresh();

        ahead.advance_past(&behind);
        assert_eq!(ahead.fresh(), SymbolId::BlockLocal(BlockLocalIndex(3)));

        let mut same = ahead.clone();
        same.advance_past(&ahead);
        assert_eq!(
            same.fresh(),
            ahead.fresh(),
            "advancing past an equal allocator is a no-op"
        );
    }

    #[test]
    #[should_panic(expected = "the block-local SymbolId space is exhausted")]
    fn the_block_local_allocator_panics_at_the_end_instead_of_reusing_ids() {
        let mut alloc = BlockLocalAllocator { next: u32::MAX - 1 };
        let last = alloc.fresh();
        assert_eq!(last, SymbolId::BlockLocal(BlockLocalIndex(u32::MAX - 1)));
        let _ = alloc.fresh();
    }

    #[test]
    fn the_overload_allocator_hands_out_consecutive_ids_from_the_counter() {
        let counter = AtomicU32::new(10);
        assert_eq!(
            allocate_overload(&counter),
            SymbolId::Overload(OverloadIndex(10))
        );
        assert_eq!(
            allocate_overload(&counter),
            SymbolId::Overload(OverloadIndex(11))
        );
    }

    #[test]
    #[should_panic(expected = "the overload SymbolId space is exhausted")]
    fn the_overload_allocator_panics_at_the_end_instead_of_wrapping() {
        let counter = AtomicU32::new(u32::MAX - 1);
        assert_eq!(
            allocate_overload(&counter),
            SymbolId::Overload(OverloadIndex(u32::MAX - 1))
        );
        let _ = allocate_overload(&counter);
    }
}
