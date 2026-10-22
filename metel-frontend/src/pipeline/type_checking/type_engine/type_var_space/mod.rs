//! The `TypeVar` space and the generator that hands it out (metel-core#1541, Engineering Standard §11).
//!
//! `TypeVar` equality is identity: two variables with the same `u32` are the same variable, across
//! every generator of a type-check run. Phases that must not see each other's variables therefore
//! allocate from disjoint ranges of the one `u32` space. Those ranges used to be hand-picked literals
//! scattered over four files (10,000; 1,000,000; 2,000,000 twice) that nothing checked; they are
//! declared here, in one place, and checked twice: the compiler rejects ranges that overlap or are out
//! of order, and a generator panics rather than step into its neighbour's range.
use super::TypeVar;
use std::ops::Range;

/// A named, half-open slice of the `TypeVar` space owned by one phase.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeVarRange {
    pub name: &'static str,
    pub start: u32,
    pub end: u32,
}

impl TypeVarRange {
    #[must_use]
    pub const fn contains(&self, var: u32) -> bool {
        self.start <= var && var < self.end
    }

    #[must_use]
    pub const fn as_range(&self) -> Range<u32> {
        self.start..self.end
    }
}

/// Each range is 16,777,216 variables, far past anything a module produces; the next starts where it ends.
const SPAN: u32 = 1 << 24;

/// A module's own variables: its registry (`build_registry`) and its inference passes. Restarts at the
/// bottom for every module.
pub const LOCAL: TypeVarRange = TypeVarRange {
    name: "local",
    start: 0,
    end: SPAN,
};
/// The quantified variables of the built-in schemes derived from the embedded `std::core` (ADR-0027).
pub const PRELUDE: TypeVarRange = TypeVarRange {
    name: "prelude",
    start: SPAN,
    end: 2 * SPAN,
};
/// The fresh variables of one generic-body reconstruction (`construct_generic_body`); every
/// reconstruction starts again at the bottom of this range.
pub const CONSTRUCTION: TypeVarRange = TypeVarRange {
    name: "construction",
    start: 2 * SPAN,
    end: 3 * SPAN,
};
/// The quantified variables of schemes alpha-renamed for export, so that an imported scheme can never
/// share an id with a live variable of the importing module (METEL-181).
pub const EXPORT: TypeVarRange = TypeVarRange {
    name: "export",
    start: 3 * SPAN,
    end: 4 * SPAN,
};

/// Every range, in order of start.
pub const ALL: [TypeVarRange; 4] = [LOCAL, PRELUDE, CONSTRUCTION, EXPORT];

/// Whether `ranges` are non-empty, in order, and pairwise disjoint.
const fn ranges_are_ordered_and_disjoint(ranges: &[TypeVarRange]) -> bool {
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

// A range edited into its neighbour is a compile error, not a collision found later as a type error.
const _: () = assert!(ranges_are_ordered_and_disjoint(&ALL));

/// Counter for generating fresh type variables inside one [`TypeVarRange`].
///
/// # Invariant: `TypeVar` identity is global
///
/// All generators within a single type-check run produce variables from the one `u32` space, so two
/// generators that can meet in one substitution must draw from different ranges, or the second must
/// start past the first. Within the same range the second must start past the first: the `InferContext`
/// owns the generator for Pass 1, and `ctx.split_gen()` hands Pass 2 a generator that continues it
/// (same range, starting where Pass 1 stopped). A collision otherwise produces self-referential
/// substitutions and infinite recursion in `Substitution::apply`.
// limit: ["LIMIT-TYPE-INFERENCE-006"]
pub struct TypeVarGenerator {
    counter: u32,
    range: TypeVarRange,
}

impl TypeVarGenerator {
    /// A generator over the module-local range, starting at its bottom.
    #[must_use]
    pub fn new() -> Self {
        Self::in_range(LOCAL)
    }

    /// A generator over `range`, starting at its bottom.
    #[must_use]
    pub fn in_range(range: TypeVarRange) -> Self {
        TypeVarGenerator {
            counter: range.start,
            range,
        }
    }

    /// A generator over the same range, continuing from this one's counter.
    #[must_use]
    pub fn continuing(&self) -> Self {
        TypeVarGenerator {
            counter: self.counter,
            range: self.range,
        }
    }

    /// Generate a fresh type variable.
    ///
    /// # Panics
    /// Panics when the range is exhausted: stepping past its end would reuse an id of the next range,
    /// which is a silent collision (Standard §11).
    pub fn fresh(&mut self) -> TypeVar {
        assert!(
            self.counter < self.range.end,
            "TypeVar range `{}` ({}..{}) is exhausted",
            self.range.name,
            self.range.start,
            self.range.end
        );
        let var = TypeVar(self.counter);
        self.counter += 1;
        var
    }

    /// Move the counter past `var` if `var` lies in this generator's own range, so a fresh variable
    /// cannot equal it. A variable from another range is disjoint by construction and needs nothing.
    pub fn reserve_past(&mut self, var: TypeVar) {
        if self.range.contains(var.0) {
            self.counter = self.counter.max(var.0 + 1);
        }
    }

    /// The range this generator draws from.
    #[must_use]
    pub fn range(&self) -> TypeVarRange {
        self.range
    }

    /// Get the current counter state (for testing and for continuing a pass).
    #[must_use]
    pub fn counter(&self) -> u32 {
        self.counter
    }

    /// A generator over the local range starting at `start`, for tests that need a known position.
    #[cfg(test)]
    #[must_use]
    pub fn starting_at(start: u32) -> Self {
        TypeVarGenerator {
            counter: start,
            range: LOCAL,
        }
    }
}

impl Default for TypeVarGenerator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests;
