//! The functions declared inside a definition's body (ADR-0068).
//!
//! A nested function sees none of the enclosing function's locals or type parameters (RFC-0195), so
//! it is analysed as a definition of its own, ahead of any instantiation of the enclosing generic.

use crate::data::ast::{Block, Decl, FunDecl};

/// Every function declared in `block`, outermost first, with the functions declared inside those
/// following them.
pub(in crate::pipeline::type_checking) fn nested_functions(block: &Block) -> Vec<&FunDecl> {
    let mut found = Vec::new();
    crate::data::decl_walk::for_each_declaration(block, &mut |declaration| {
        if let Decl::Fun(function) = declaration {
            found.push(function);
        }
    });
    found
}
