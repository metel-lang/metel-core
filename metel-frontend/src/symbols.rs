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

/// First `SymbolId` assigned to user-defined declarations by the name resolver.
pub const USER_SYM_START: u32 = 1000;

/// Start of the range allocated to free-function overload definitions
/// (METEL-180). Each overloaded definition gets a process-unique id from a
/// global counter (see `typechecker::overload`), disjoint from the
/// name-resolver range so the two allocators never collide.
pub const OVERLOAD_SYM_START: u32 = 0x4000_0000;

// ── SymbolTable ───────────────────────────────────────────────────────────────

use std::collections::HashMap;

/// Intern table: maps `(source_module, source_name)` → stable `SymbolId`.
/// Pre-populated with builtin entries so that imports of stdlib names get the
/// same well-known IDs as the `SYM_*` constants above.
pub struct SymbolTable {
    pub map: HashMap<(Vec<String>, String), SymbolId>,
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
    pub fn new() -> Self {
        let mut map = HashMap::new();
        let sc = || vec!["std".to_string(), "core".to_string()];

        // Builtin types
        map.insert((sc(), "boolean".into()), SYM_TYPE_BOOLEAN);
        map.insert((sc(), "String".into()), SYM_TYPE_STRING);
        map.insert((sc(), "Char".into()), SYM_TYPE_CHAR);
        map.insert((sc(), "i8".into()), SYM_TYPE_I8);
        map.insert((sc(), "i16".into()), SYM_TYPE_I16);
        map.insert((sc(), "i32".into()), SYM_TYPE_I32);
        map.insert((sc(), "i64".into()), SYM_TYPE_I64);
        map.insert((sc(), "u8".into()), SYM_TYPE_U8);
        map.insert((sc(), "u16".into()), SYM_TYPE_U16);
        map.insert((sc(), "u32".into()), SYM_TYPE_U32);
        map.insert((sc(), "u64".into()), SYM_TYPE_U64);
        map.insert((sc(), "f32".into()), SYM_TYPE_F32);
        map.insert((sc(), "f64".into()), SYM_TYPE_F64);
        map.insert((sc(), "List".into()), SYM_TYPE_LIST);
        map.insert((sc(), "Perhaps".into()), SYM_TYPE_PERHAPS);
        map.insert((sc(), "Result".into()), SYM_TYPE_RESULT);
        map.insert((sc(), "Range".into()), SYM_TYPE_RANGE);
        map.insert((sc(), "RangeInclusive".into()), SYM_TYPE_RANGE_INCLUSIVE);

        // Builtin aspects
        map.insert((sc(), "Display".into()), SYM_ASPECT_DISPLAY);
        map.insert((sc(), "Iterable".into()), SYM_ASPECT_ITERABLE);
        map.insert((sc(), "From".into()), SYM_ASPECT_FROM);

        Self {
            map,
            next_id: USER_SYM_START,
        }
    }

    /// Return the existing `SymbolId` for `(source_module, source_name)`, or assign
    /// a fresh one. Two calls with identical arguments always return the same id.
    // arch-implements: ["arch.name-resolution.requirement-1"]
    pub fn intern(&mut self, source_module: &[String], source_name: &str) -> SymbolId {
        let key = (source_module.to_vec(), source_name.to_string());
        *self.map.entry(key).or_insert_with(|| {
            let id = SymbolId(self.next_id);
            self.next_id += 1;
            id
        })
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
}
