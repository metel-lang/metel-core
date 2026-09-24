//! `flow_state` layered directly on `place` (RFC-0071 §9b, ADR-0045): shared
//! vocabulary for move checking and, eventually, borrow checking, not owned by
//! either as a pipeline stage.

pub mod place;

pub(crate) mod flow_state;
