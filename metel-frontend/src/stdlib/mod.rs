//! Standard-library sources embedded into the binary at build time (METEL-181).
//!
//! `build.rs` scans `stdlib/**/*.mtl` and generates `EMBEDDED_STDLIB`, a table of
//! `(module_path_segments, source)` pairs. The module loader serves these
//! through `EmbeddedStdlibProvider` so `std::…` modules need no on-disk files.

pub mod native_keys;

include!(concat!(env!("OUT_DIR"), "/stdlib_embedded.rs"));

/// Embedded source for a logical stdlib module path (e.g. `["std", "core"]`),
/// or `None` if no embedded module matches.
#[must_use]
pub fn lookup(module_path: &[String]) -> Option<&'static str> {
    EMBEDDED_STDLIB
        .iter()
        .find(|(segs, _)| {
            segs.len() == module_path.len()
                && segs.iter().zip(module_path).all(|(a, b)| *a == b.as_str())
        })
        .map(|(_, src)| *src)
}

/// Every embedded stdlib module path. Used by the loader to synthesize the
/// stdlib modules into the module graph ahead of user code.
#[must_use]
pub fn module_paths() -> Vec<Vec<String>> {
    EMBEDDED_STDLIB
        .iter()
        .map(|(segs, _)| segs.iter().map(std::string::ToString::to_string).collect())
        .collect()
}

/// The parsed `std::core` program, cached for the lifetime of the process.
/// Consumed by the typechecker registry (builtin type/aspect registration),
/// the prelude (free-function schemes), and the runtime (host bindings) —
/// `stdlib/core.mtl` is the single source of truth for the core surface.
///
/// # Panics
/// Panics if `std::core` is missing from the embedded stdlib table or fails to
/// parse — both indicate a broken build, not a user-reachable condition.
pub fn core_program() -> &'static crate::data::ast::Program {
    use std::sync::OnceLock;
    static CORE: OnceLock<crate::data::ast::Program> = OnceLock::new();
    CORE.get_or_init(|| {
        let core_path = ["std".to_string(), "core".to_string()];
        let source = lookup(&core_path).expect("std::core is embedded in the binary");
        crate::pipeline::parsing::parser::parse(source, "<embedded std::core>")
            .expect("embedded std::core must parse; it is compiled into the binary")
    })
}

#[cfg(test)]
mod tests;
