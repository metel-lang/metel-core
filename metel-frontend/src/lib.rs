// Metel's deliberate numeric conversion semantics require these casts throughout the
// frontend; see the equivalent rationale in the interpreter crate.
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss,
    clippy::cast_possible_wrap,
    clippy::cast_lossless
)]

pub mod data;
pub mod identity;
pub mod ownership;
pub mod pipeline;
pub mod stdlib;
pub mod tooling;
