//! The frontend pipeline, organized by stage. Each stage's public API takes
//! only its immediate predecessor's typed output -- no stage reaches past that
//! boundary into an earlier stage's internals (`architecture/engineering-standards.md`
//! Standard 4).

pub mod coherence;
pub mod elaboration;
pub mod move_check;
pub mod name_resolution;
pub mod parsing;
pub mod path_normalization;
pub mod type_checking;
