//! [`LexicalPath`] — the structural key that [`LocalId`] and [`RefId`] hash.
//!
//! A path is the chain of structural positions from an owning body to a binding
//! or a use inside it. It contains no byte offsets and no traversal counters
//! that depend on unrelated siblings: a `let` step carries the interned
//! *spelling*, a block step carries its ordinal *among blocks* (stable unless
//! blocks are added/removed), a parameter step carries its ordinal in the
//! parameter list (part of the signature). Inserting a blank line, reformatting,
//! or adding an unrelated `let` earlier in the same block does not change any
//! existing path.
//!
//! [`LocalId`]: super::LocalId
//! [`RefId`]: super::RefId

use std::hash::Hash;

/// One step in a [`LexicalPath`].
///
/// Name-bearing steps carry the raw spelling, not an interned [`NameId`]: an
/// interned id is a per-run dense integer whose value depends on allocation
/// order, which is exactly the positional dependence structural allocation
/// exists to avoid. The spelling *is* the stable structural identity of "the
/// `let` binding called `target`".
///
/// [`NameId`]: super::NameId
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LexicalSeg {
    /// The n-th parameter of the owning function (ordinal is part of the
    /// signature, not a traversal artifact).
    Param(u32),
    /// The n-th parameter of a closure.
    ClosureParam(u32),
    /// Into the n-th nested block of the current body. Counted among blocks
    /// only, so sibling non-block statements do not perturb it.
    Block(u32),
    /// Into the n-th closure expression of the current scope.
    Closure(u32),
    /// A `let` binding with this spelling.
    Let(String),
    /// A `mut` binding with this spelling.
    Mut(String),
    /// A function declared inside the body, by spelling.
    NestedFn(String),
    /// A `for … in` or C-style loop binding, by spelling.
    LoopBinding(String),
    /// A binding introduced by a pattern field (`Point { x, y }` → `x`, `y`).
    PatternField(String),
    /// A binding introduced by a positional pattern element (`(a, b)` → 0, 1;
    /// array rest → its own step).
    PatternElem(u32),
    /// The leaf of a *reference* path: one use of this spelling in expression
    /// position, disambiguated by its ordinal among like-spelled uses in the
    /// same immediate scope.
    Use { name: String, occurrence: u32 },
}

/// The structural location of a binding or use within its owner.
///
/// Ordering of the `Vec` is outermost-first. Two distinct bindings always have
/// distinct paths — shadowing included, because the inner binding sits under an
/// extra [`LexicalSeg::Block`] (or a later `Let`/`Mut` step) that the outer one
/// does not.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct LexicalPath(pub Vec<LexicalSeg>);

impl LexicalPath {
    /// The empty path (the owning body itself).
    #[must_use]
    pub fn root() -> Self {
        Self(Vec::new())
    }

    /// A new path with `seg` appended.
    #[must_use]
    pub fn child(&self, seg: LexicalSeg) -> Self {
        let mut segs = self.0.clone();
        segs.push(seg);
        Self(segs)
    }

    /// Append `seg` in place.
    pub fn push(&mut self, seg: LexicalSeg) {
        self.0.push(seg);
    }

    /// Drop the last step in place.
    pub fn pop(&mut self) {
        self.0.pop();
    }

    /// The steps, outermost first.
    #[must_use]
    pub fn segments(&self) -> &[LexicalSeg] {
        &self.0
    }
}
