// Metel's deliberate numeric conversion semantics require these casts throughout the
// frontend; see the equivalent rationale in the interpreter crate.
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss,
    clippy::cast_possible_wrap,
    clippy::cast_lossless
)]

pub mod analysis;
pub mod ast;
pub mod coherence;
pub mod elaborator;
pub mod error;
pub(crate) mod flow_state;
pub mod identity;
pub mod module_loader;
pub mod module_paths;
pub mod move_check;
pub mod name_resolver;
pub mod native_keys;
pub mod parser;
pub mod path_normalizer;
pub mod place;
pub mod reference_resolver;
pub mod stdlib;
pub mod symbols;
pub mod type_alias;
pub mod typechecker;
pub mod typed_ast;
pub mod typeinference;
pub mod types;
