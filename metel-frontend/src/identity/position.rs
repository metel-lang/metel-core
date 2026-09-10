//! [`PositionIndex`] — the one structure allowed to be keyed by source
//! position.
//!
//! It is rebuilt from a parsed snapshot, never persisted, and never a semantic
//! input: it exists only to answer an editor's "what identity is at byte N"
//! question. Everything durable ([`ResolutionMap`], the frozen IR) is keyed by
//! identity. Keeping the two apart is what lets a later incremental layer
//! rebuild position lookup on every keystroke while the resolved facts survive
//! untouched (ADR-0054, 2026-09-10 amendment).
//!
//! [`ResolutionMap`]: super::ResolutionMap

use crate::ast::Span;

use super::{BindingId, RefId};

/// What sits at a source position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PositionHit {
    /// A definition site (the declared name of a binding).
    Definition(BindingId),
    /// A reference site (one use of a name).
    Reference(RefId),
}

/// A span-sorted spine over a snapshot's definition and reference sites.
///
/// Lookup returns the *innermost* (smallest) span that contains the offset,
/// matching the tie-break the existing tooling queries use.
#[derive(Debug, Clone, Default)]
pub struct PositionIndex {
    entries: Vec<(Span, PositionHit)>,
}

impl PositionIndex {
    /// Build from `(span, hit)` pairs collected during the identity walk.
    #[must_use]
    pub fn from_entries(mut entries: Vec<(Span, PositionHit)>) -> Self {
        // Sort by start, then by widest-first, so a linear scan can stop early
        // and the innermost match is deterministic.
        entries.sort_by(|(a, _), (b, _)| a.start.cmp(&b.start).then(b.end.cmp(&a.end)));
        Self { entries }
    }

    /// Combine position indices produced for individual modules.
    ///
    /// The entries remain snapshot-local metadata, so merging them only
    /// concatenates and re-sorts their already-derived position entries.
    #[must_use]
    pub fn from_indices(indices: impl IntoIterator<Item = Self>) -> Self {
        Self::from_entries(
            indices
                .into_iter()
                .flat_map(|index| index.entries)
                .collect(),
        )
    }

    /// The identity at `byte_offset` in `filename`, or `None` for whitespace,
    /// comments, and any position not covered by a definition or reference
    /// span.
    #[must_use]
    pub fn resolve(&self, filename: &str, byte_offset: usize) -> Option<PositionHit> {
        self.entries
            .iter()
            .filter(|(span, _)| {
                span.filename == filename && span.start <= byte_offset && byte_offset < span.end
            })
            .min_by_key(|(span, _)| span.end - span.start)
            .map(|(_, hit)| *hit)
    }

    /// Number of indexed sites (definitions + references).
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the index is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}
