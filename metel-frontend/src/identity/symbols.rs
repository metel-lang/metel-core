/// A stable, opaque identity for a resolved symbol (a unique `(source_module, source_name)` pair).
///
/// Assigned during name resolution and threaded through the compilation pipeline so that later
/// stages can identify the same declaration regardless of local alias or path spelling.
/// Diagnostic output always uses the original path spelling; `SymbolId` is for structural identity
/// only and is never surfaced to the user.
///
/// # ID ranges
///
/// | Range         | Purpose                                        |
/// |---------------|------------------------------------------------|
/// | 1 – 49        | Builtin types (primitives + core stdlib)       |
/// | 50 – 99       | Builtin aspects                                |
/// | 100 – 999     | Reserved for stdlib expansion                  |
/// | 1000 +        | User-defined declarations (name-resolver IDs)  |
/// | 0x4000_0000 + | Free-function overload definitions (METEL-180) |
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymbolId(pub u32);

// ── Builtin types (1–49) ──────────────────────────────────────────────────────

pub const SYM_TYPE_BOOLEAN: SymbolId = SymbolId(1);
pub const SYM_TYPE_STRING: SymbolId = SymbolId(2);
pub const SYM_TYPE_CHAR: SymbolId = SymbolId(3);
pub const SYM_TYPE_I8: SymbolId = SymbolId(4);
pub const SYM_TYPE_I16: SymbolId = SymbolId(5);
pub const SYM_TYPE_I32: SymbolId = SymbolId(6);
pub const SYM_TYPE_I64: SymbolId = SymbolId(7);
pub const SYM_TYPE_U8: SymbolId = SymbolId(8);
pub const SYM_TYPE_U16: SymbolId = SymbolId(9);
pub const SYM_TYPE_U32: SymbolId = SymbolId(10);
pub const SYM_TYPE_U64: SymbolId = SymbolId(11);
pub const SYM_TYPE_F32: SymbolId = SymbolId(12);
pub const SYM_TYPE_F64: SymbolId = SymbolId(13);
pub const SYM_TYPE_LIST: SymbolId = SymbolId(14);
pub const SYM_TYPE_PERHAPS: SymbolId = SymbolId(15);
pub const SYM_TYPE_RESULT: SymbolId = SymbolId(16);
pub const SYM_TYPE_RANGE: SymbolId = SymbolId(17);
pub const SYM_TYPE_RANGE_INCLUSIVE: SymbolId = SymbolId(18);
// 19–49 reserved for future stdlib types.

// ── Builtin aspects (50–99) ───────────────────────────────────────────────────

pub const SYM_ASPECT_DISPLAY: SymbolId = SymbolId(50);
pub const SYM_ASPECT_ITERABLE: SymbolId = SymbolId(51);
pub const SYM_ASPECT_FROM: SymbolId = SymbolId(52);
// 53–99 reserved for future aspects.

// 100–999 reserved for stdlib expansion.

// ── The ranges of the SymbolId space (metel-core#1542, Engineering Standard §11) ───────────────

/// A named, half-open slice of the `SymbolId` space owned by one allocator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolRange {
    pub name: &'static str,
    pub start: u32,
    pub end: u32,
}

impl SymbolRange {
    #[must_use]
    pub const fn contains(&self, id: u32) -> bool {
        self.start <= id && id < self.end
    }
}

/// Builtin types: the primitives and the core types the language knows by id.
pub const BUILTIN_TYPES: SymbolRange = SymbolRange {
    name: "builtin types",
    start: 1,
    end: 50,
};
/// Builtin aspects.
pub const BUILTIN_ASPECTS: SymbolRange = SymbolRange {
    name: "builtin aspects",
    start: 50,
    end: 100,
};
/// Reserved for stdlib expansion; nothing allocates here yet.
pub const STDLIB_RESERVED: SymbolRange = SymbolRange {
    name: "stdlib reserved",
    start: 100,
    end: 1000,
};
/// User-defined declarations, allocated by the name resolver's [`SymbolTable`].
pub const USER: SymbolRange = SymbolRange {
    name: "user declarations",
    start: 1000,
    end: 0x4000_0000,
};
/// Free-function overload definitions (METEL-180), allocated upward from a process-global counter (see
/// `type_checking::overload`; the counter itself is `LIMIT-NAME-RESOLUTION-002`).
pub const OVERLOAD: SymbolRange = SymbolRange {
    name: "overload definitions",
    start: 0x4000_0000,
    end: 0x8000_0000,
};
/// Block-local struct and enum declarations, minted by the type engine and allocated **downward** from
/// the top of the range, so they stay clear of the two ascending allocators.
pub const BLOCK_LOCAL: SymbolRange = SymbolRange {
    name: "block-local types",
    start: 0x8000_0000,
    end: u32::MAX,
};

/// Every range, in order of start.
pub const ALL_RANGES: [SymbolRange; 6] = [
    BUILTIN_TYPES,
    BUILTIN_ASPECTS,
    STDLIB_RESERVED,
    USER,
    OVERLOAD,
    BLOCK_LOCAL,
];

/// First `SymbolId` assigned to user-defined declarations by the name resolver.
pub const USER_SYM_START: u32 = USER.start;

/// Start of the range allocated to free-function overload definitions.
pub const OVERLOAD_SYM_START: u32 = OVERLOAD.start;

const fn ranges_are_ordered_and_disjoint(ranges: &[SymbolRange]) -> bool {
    let mut i = 0;
    while i < ranges.len() {
        if ranges[i].start >= ranges[i].end {
            return false;
        }
        if i > 0 && ranges[i - 1].end > ranges[i].start {
            return false;
        }
        i += 1;
    }
    true
}

// A range edited into its neighbour is a compile error, not a collision found later as a wrong id.
const _: () = assert!(ranges_are_ordered_and_disjoint(&ALL_RANGES));

/// Take the next id from `counter`, which hands out ids of `range`.
///
/// # Panics
/// Panics when `range` is exhausted: stepping past its end would reuse an id of the next range, or
/// wrap, either of which is a silent collision.
pub fn allocate_from(counter: &AtomicU32, range: SymbolRange) -> SymbolId {
    let id = counter
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
            (next < range.end).then(|| next + 1)
        })
        .unwrap_or_else(|_| {
            panic!(
                "SymbolId range `{}` ({}..{}) is exhausted",
                range.name, range.start, range.end
            )
        });
    SymbolId(id)
}

/// Take the next id from `next`, which hands out ids of `range` counting **down**, and step it.
///
/// # Panics
/// Panics when `range` is exhausted: stepping below its start would reuse an id of the previous range.
pub fn allocate_down(next: &mut u32, range: SymbolRange) -> SymbolId {
    assert!(
        range.contains(*next),
        "SymbolId range `{}` ({}..{}) is exhausted",
        range.name,
        range.start,
        range.end
    );
    let id = *next;
    // Wraps to a value outside every range when the bottom is reached, so the next call panics.
    *next = id.wrapping_sub(1);
    SymbolId(id)
}

// ── The builtin symbols, in one place ─────────────────────────────────────────

/// Whether a builtin names a type or an aspect.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinKind {
    Type,
    Aspect,
}

/// Every builtin symbol: its `std::core` name, its kind and its fixed id. The name resolver seeds its
/// table from this, and the evaluator looks builtins up here, so the three hand-kept mirrors of this
/// list (the table seeding and two `match`es in the evaluator) are one. Ids are unique and lie in the
/// range of their kind (checked below); the names are checked against the embedded `std::core` in the
/// tests.
pub const BUILTIN_SYMBOLS: [(&str, BuiltinKind, SymbolId); 21] = [
    ("boolean", BuiltinKind::Type, SYM_TYPE_BOOLEAN),
    ("String", BuiltinKind::Type, SYM_TYPE_STRING),
    ("Char", BuiltinKind::Type, SYM_TYPE_CHAR),
    ("i8", BuiltinKind::Type, SYM_TYPE_I8),
    ("i16", BuiltinKind::Type, SYM_TYPE_I16),
    ("i32", BuiltinKind::Type, SYM_TYPE_I32),
    ("i64", BuiltinKind::Type, SYM_TYPE_I64),
    ("u8", BuiltinKind::Type, SYM_TYPE_U8),
    ("u16", BuiltinKind::Type, SYM_TYPE_U16),
    ("u32", BuiltinKind::Type, SYM_TYPE_U32),
    ("u64", BuiltinKind::Type, SYM_TYPE_U64),
    ("f32", BuiltinKind::Type, SYM_TYPE_F32),
    ("f64", BuiltinKind::Type, SYM_TYPE_F64),
    ("List", BuiltinKind::Type, SYM_TYPE_LIST),
    ("Perhaps", BuiltinKind::Type, SYM_TYPE_PERHAPS),
    ("Result", BuiltinKind::Type, SYM_TYPE_RESULT),
    ("Range", BuiltinKind::Type, SYM_TYPE_RANGE),
    (
        "RangeInclusive",
        BuiltinKind::Type,
        SYM_TYPE_RANGE_INCLUSIVE,
    ),
    ("Display", BuiltinKind::Aspect, SYM_ASPECT_DISPLAY),
    ("Iterable", BuiltinKind::Aspect, SYM_ASPECT_ITERABLE),
    ("From", BuiltinKind::Aspect, SYM_ASPECT_FROM),
];

/// Builtin ids are pairwise distinct and each lies in the range of its kind.
const fn builtins_are_distinct_and_in_range() -> bool {
    let mut i = 0;
    while i < BUILTIN_SYMBOLS.len() {
        let (_, kind, id) = BUILTIN_SYMBOLS[i];
        let range = match kind {
            BuiltinKind::Type => BUILTIN_TYPES,
            BuiltinKind::Aspect => BUILTIN_ASPECTS,
        };
        if !range.contains(id.0) {
            return false;
        }
        let mut j = i + 1;
        while j < BUILTIN_SYMBOLS.len() {
            if BUILTIN_SYMBOLS[j].2.0 == id.0 {
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
}

const _: () = assert!(builtins_are_distinct_and_in_range());

/// The well-known id of the builtin named `name` of `kind`, if there is one.
#[must_use]
pub fn builtin_symbol(name: &str, kind: BuiltinKind) -> Option<SymbolId> {
    BUILTIN_SYMBOLS
        .iter()
        .find(|(n, k, _)| *n == name && *k == kind)
        .map(|(_, _, id)| *id)
}

// ── SymbolTable ───────────────────────────────────────────────────────────────

use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering};

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
        let map = BUILTIN_SYMBOLS
            .iter()
            .map(|(name, _, id)| ((std_core(), (*name).to_string()), *id))
            .collect();
        Self {
            map,
            next_id: USER.start,
        }
    }

    /// Return the existing `SymbolId` for `(source_module, source_name)`, or assign
    /// a fresh one. Two calls with identical arguments always return the same id.
    ///
    /// # Panics
    /// Panics when the user range is exhausted: the next id would belong to the overload range.
    // arch-implements: ["arch.name-resolution.requirement-1"]
    pub fn intern(&mut self, source_module: &[String], source_name: &str) -> SymbolId {
        let key = (source_module.to_vec(), source_name.to_string());
        *self.map.entry(key).or_insert_with(|| {
            assert!(
                self.next_id < USER.end,
                "SymbolId range `{}` ({}..{}) is exhausted",
                USER.name,
                USER.start,
                USER.end
            );
            let id = SymbolId(self.next_id);
            self.next_id += 1;
            id
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

    /// A table whose next user id is `next_id`, for tests that exercise the end of the range.
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
    fn user_declarations_are_allocated_from_the_user_range_below_the_overload_range() {
        let mut table = SymbolTable::new();
        let first = table.intern(&["app".to_string()], "Widget");
        let second = table.intern(&["app".to_string()], "Gadget");
        assert_eq!(first, SymbolId(USER_SYM_START));
        assert_eq!(second, SymbolId(USER_SYM_START + 1));
        assert!(
            second.0 < OVERLOAD_SYM_START,
            "overload-synthesized symbols have their own reserved range"
        );
    }

    // metel-core#1542: the ranges, the builtin table and the allocators are checked.

    #[test]
    fn the_declared_ranges_are_ordered_and_disjoint() {
        assert!(ranges_are_ordered_and_disjoint(&ALL_RANGES));
        assert_eq!(USER_SYM_START, USER.start);
        assert_eq!(OVERLOAD_SYM_START, OVERLOAD.start);
        for pair in ALL_RANGES.windows(2) {
            assert!(
                pair[0].end <= pair[1].start,
                "{} overlaps {}",
                pair[0].name,
                pair[1].name
            );
        }
    }

    #[test]
    fn an_overlap_an_empty_range_and_a_wrong_order_are_rejected() {
        let a = SymbolRange {
            name: "a",
            start: 0,
            end: 10,
        };
        let overlapping = SymbolRange {
            name: "b",
            start: 5,
            end: 20,
        };
        let empty = SymbolRange {
            name: "c",
            start: 30,
            end: 30,
        };
        assert!(ranges_are_ordered_and_disjoint(&[a]));
        assert!(!ranges_are_ordered_and_disjoint(&[a, overlapping]));
        assert!(!ranges_are_ordered_and_disjoint(&[empty]));
        assert!(!ranges_are_ordered_and_disjoint(&[overlapping, a]));
    }

    #[test]
    fn builtin_ids_and_names_are_unique_and_in_the_range_of_their_kind() {
        let mut ids = std::collections::HashSet::new();
        let mut names = std::collections::HashSet::new();
        for (name, kind, id) in BUILTIN_SYMBOLS {
            assert!(ids.insert(id.0), "duplicate builtin id {} ({name})", id.0);
            assert!(
                names.insert((name, kind as u8)),
                "duplicate builtin name {name}"
            );
            let range = match kind {
                BuiltinKind::Type => BUILTIN_TYPES,
                BuiltinKind::Aspect => BUILTIN_ASPECTS,
            };
            assert!(
                range.contains(id.0),
                "{name} ({}) is outside {}",
                id.0,
                range.name
            );
        }
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
        for (name, _, _) in BUILTIN_SYMBOLS {
            let intrinsic = INTRINSIC_BUILTINS.contains(&name);
            assert!(
                declared.contains(name) != intrinsic,
                "builtin `{name}` must be either declared in std::core or an intrinsic type, not both and not neither"
            );
        }
    }

    #[test]
    fn the_table_is_seeded_with_exactly_the_builtins_at_their_ids() {
        let table = SymbolTable::new();
        assert_eq!(table.map().len(), BUILTIN_SYMBOLS.len());
        for (name, _, id) in BUILTIN_SYMBOLS {
            assert_eq!(
                table.map().get(&(std_core(), name.to_string())),
                Some(&id),
                "{name}"
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
    #[should_panic(expected = "SymbolId range `user declarations`")]
    fn interning_past_the_end_of_the_user_range_panics_instead_of_entering_the_overload_range() {
        let mut table = SymbolTable::with_next_id(USER.end - 1);
        let last = table.intern(&["app".to_string()], "Last");
        assert!(USER.contains(last.0));
        let _ = table.intern(&["app".to_string()], "OneTooMany");
    }

    #[test]
    #[should_panic(expected = "SymbolId range `overload definitions`")]
    fn the_overload_allocator_panics_instead_of_wrapping() {
        let counter = AtomicU32::new(OVERLOAD.end - 1);
        assert_eq!(
            allocate_from(&counter, OVERLOAD),
            SymbolId(OVERLOAD.end - 1)
        );
        let _ = allocate_from(&counter, OVERLOAD);
    }

    #[test]
    fn the_block_local_allocator_counts_down_and_stays_in_its_range() {
        let mut next = BLOCK_LOCAL.end - 1;
        let first = allocate_down(&mut next, BLOCK_LOCAL);
        let second = allocate_down(&mut next, BLOCK_LOCAL);
        assert_eq!(first, SymbolId(BLOCK_LOCAL.end - 1));
        assert_eq!(second, SymbolId(BLOCK_LOCAL.end - 2));
        assert!(BLOCK_LOCAL.contains(first.0) && BLOCK_LOCAL.contains(second.0));
    }

    #[test]
    #[should_panic(expected = "SymbolId range `block-local types`")]
    fn the_block_local_allocator_panics_at_the_bottom_instead_of_reusing_ids() {
        let mut next = BLOCK_LOCAL.start;
        let last = allocate_down(&mut next, BLOCK_LOCAL);
        assert_eq!(last, SymbolId(BLOCK_LOCAL.start));
        let _ = allocate_down(&mut next, BLOCK_LOCAL);
    }

    #[test]
    fn the_overload_allocator_hands_out_consecutive_ids_from_its_start() {
        let counter = AtomicU32::new(OVERLOAD.start);
        assert_eq!(allocate_from(&counter, OVERLOAD), SymbolId(OVERLOAD.start));
        assert_eq!(
            allocate_from(&counter, OVERLOAD),
            SymbolId(OVERLOAD.start + 1)
        );
    }
}
