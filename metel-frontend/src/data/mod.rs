//! Pure data definitions shared across the pipeline: no stage owns any of these.
//! The ast -> typed_ast progression, `types`' vocabulary, and `error`'s diagnostics.

pub mod ast;
pub mod error;
pub mod typed_ast;
pub mod types;
