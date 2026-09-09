//! Metel language interpreter library.
//! Exposes modules for use in tests and external code.

// clippy::pedantic's numeric-cast lints (cast_possible_truncation,
// cast_sign_loss, cast_precision_loss, cast_possible_wrap, cast_lossless)
// fire on essentially every numeric conversion in this crate, because
// converting between Metel's own sized numeric `Value` variants (and to/from
// Rust's `usize` for array indexing) is core, pervasive domain logic here,
// not an incidental detail — see e.g. `evaluator::builtins`'s
// `native_int_from`/`native_float_from` macros, which implement Metel's own
// `as`-cast/`From` conversion semantics and truncate/wrap/lose precision by
// *design*, matching Rust's own `as` operator. Blanket-allowed at the crate
// level rather than per call site (of which there are ~90) for exactly this
// reason: each site was reviewed and is either (a) implementing intentional
// numeric-conversion semantics or (b) an index/length conversion already
// bounds-checked by the surrounding code. A cast found to be a genuine latent
// truncation bug should still be fixed directly, not "hidden" by this.
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss,
    clippy::cast_possible_wrap,
    clippy::cast_lossless
)]

pub use metel_frontend::{
    analysis, ast, coherence, elaborator, error, module_loader, module_paths, move_check,
    name_resolver, native_keys, parser, path_normalizer, place, query, reference_resolver, stdlib,
    symbols, typechecker, typed_ast, typeinference, types,
};
pub mod evaluator;
pub mod pipeline;
