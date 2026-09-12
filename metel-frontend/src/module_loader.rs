use std::collections::{HashMap, HashSet};
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use crate::ast::{ImportTree, PathRoot, Program};
use crate::error::{MetelError, ParseErrorCode};
use crate::module_paths::resolve_path_root;
use crate::parser;

/// Process-global memo of `parser::parse` for the embedded standard-library
/// modules. Their source is fixed for the life of the process, so parsing it
/// once per test run instead of once per fixture removes the dominant repeated
/// cost of the integration suite (metel-core#873). Keyed by
/// `(module path, source hash)` so an LSP overlay that shadows a stdlib module
/// with different text is a clean miss. A `Program` AST is pure owned data
/// (spans are byte offsets, no `SymbolId`/`TypeVar`/diagnostic state), so a
/// clone per load is equivalent to a fresh parse and cannot leak between runs.
type StdlibParseCache = Mutex<HashMap<(Vec<String>, u64), Program>>;
static STDLIB_PARSE_CACHE: OnceLock<StdlibParseCache> = OnceLock::new();

fn hash_source(source: &str) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    source.hash(&mut h);
    h.finish()
}

/// Parse an embedded stdlib module, serving a clone from the process cache on a
/// repeat of the same `(module_path, source)`.
fn parse_stdlib_cached(
    module_path: &[String],
    source: &str,
    filename: &str,
) -> Result<Program, MetelError> {
    let key = (module_path.to_vec(), hash_source(source));
    let cache = STDLIB_PARSE_CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    // `unwrap_or_else(PoisonError::into_inner)`: a poisoned lock only means some
    // other parse panicked; the memo map itself is still a consistent
    // `HashMap<_, Program>` and safe to keep using.
    if let Some(program) = cache
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .get(&key)
    {
        return Ok(program.clone());
    }
    let program = parser::parse(source, filename)?;
    cache
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .insert(key, program.clone());
    Ok(program)
}

/// Supplies module source text to the loader (RFC-0058).
///
/// Abstracts the read step so the loader can serve source from the filesystem
/// (default), from compiled-in stdlib data, or from an in-memory overlay (LSP
/// unsaved buffers). Implementations receive both the logical module path (for
/// keyed lookups, e.g. embedded stdlib) and the resolved filesystem path (for
/// disk reads); a given implementation uses whichever it needs.
pub trait SourceProvider {
    /// # Errors
    /// Returns an error if the module's source cannot be located or read
    /// (implementation-defined: e.g. a missing file or a missing embedded entry).
    fn read(&self, module_path: &[String], file_path: &Path) -> Result<String, MetelError>;

    /// Resolve a candidate module file path to its canonical, existence-confirmed
    /// form, or `None` if this provider has no source for it (metel-core#1147).
    ///
    /// Import discovery tries several candidate paths per import (an item name
    /// vs. a nested module directory, `import parser::ast::Ast` trying
    /// `parser/ast.mtl` before `parser.mtl`) and needs to know which one is
    /// real *before* calling [`read`](Self::read) on it -- and the winning
    /// path's canonical form is also the stable key module-visited /
    /// diamond-dependency tracking relies on, so this does both jobs at once
    /// rather than needing a separate canonicalization step afterward.
    ///
    /// Defaults to a real filesystem canonicalization, matching every
    /// filesystem-backed provider's actual files. A provider whose files
    /// aren't on disk (an in-memory editor overlay) overrides this to consult
    /// its own map instead of the filesystem, since `Path::canonicalize`
    /// cannot see a virtual document at all -- the previous absence of this
    /// override was exactly why `InMemorySourceProvider`/virtual-root analysis
    /// could resolve only its own root file and no import at all.
    fn canonicalize(&self, candidate: &Path) -> Option<PathBuf> {
        candidate.canonicalize().ok()
    }
}

/// The default provider: reads module source from the filesystem. Behaviour is
/// identical to the loader's previous direct `fs::read_to_string` calls.
#[derive(Debug, Default, Clone, Copy)]
pub struct FsSourceProvider;

impl SourceProvider for FsSourceProvider {
    fn read(&self, _module_path: &[String], file_path: &Path) -> Result<String, MetelError> {
        fs::read_to_string(file_path).map_err(|e| {
            module_error(
                format!("failed to read module '{}': {e}", file_path.display()),
                file_path,
            )
        })
    }
}

/// Serves `std::…` modules from the binary-embedded stdlib sources, falling
/// through to the filesystem for everything else (RFC-0058 / METEL-181).
/// This is the default provider used by [`load_root`].
#[derive(Debug, Default, Clone, Copy)]
pub struct EmbeddedStdlibProvider {
    inner: FsSourceProvider,
}

impl SourceProvider for EmbeddedStdlibProvider {
    fn read(&self, module_path: &[String], file_path: &Path) -> Result<String, MetelError> {
        if let Some(src) = crate::stdlib::lookup(module_path) {
            return Ok(src.to_string());
        }
        self.inner.read(module_path, file_path)
    }
}

/// Supplies one virtual root module and the binary-embedded standard library.
///
/// This is the single-file, no-filesystem source provider used by callers such
/// as the browser playground. Multi-file editor overlays belong to their own
/// provider: this type deliberately has no fallback to the filesystem.
#[derive(Debug, Clone)]
pub struct InMemorySourceProvider {
    root: PathBuf,
    source: String,
}

impl InMemorySourceProvider {
    #[must_use]
    pub fn new(root: impl Into<PathBuf>, source: impl Into<String>) -> Self {
        Self {
            root: root.into(),
            source: source.into(),
        }
    }
}

impl SourceProvider for InMemorySourceProvider {
    fn read(&self, module_path: &[String], file_path: &Path) -> Result<String, MetelError> {
        if file_path == self.root {
            return Ok(self.source.clone());
        }
        if let Some(source) = crate::stdlib::lookup(module_path) {
            return Ok(source.to_string());
        }
        Err(module_error(
            format!(
                "in-memory source provider has no source for module '{}'",
                file_path.display()
            ),
            file_path,
        ))
    }

    // Only the root itself "exists" -- matches this provider's own single-file
    // design (metel-core#1147); an import still correctly fails to resolve,
    // rather than silently reaching the real filesystem via the default impl.
    fn canonicalize(&self, candidate: &Path) -> Option<PathBuf> {
        (candidate == self.root).then(|| self.root.clone())
    }
}

/// A multi-file editor overlay, the provider [`InMemorySourceProvider`]'s own
/// doc comment anticipates: a virtual root plus zero or more sibling in-memory
/// files, for an editor session with more than one open/virtual document
/// (metel-core#1046/#1147) -- an import or a module-path query needs the
/// imported module's own source, not just the root's.
///
/// Sibling files are keyed exactly as the loader resolves an import's file
/// path: the root's directory joined with the module path's own file name
/// (e.g. `import alpha;` next to root `"editor.mtl"` looks for `"alpha.mtl"`
/// beside it) -- the same convention [`FsSourceProvider`] uses on disk, just
/// against this map instead of the filesystem.
#[derive(Debug, Clone)]
pub struct MultiFileSourceProvider {
    root: PathBuf,
    root_source: String,
    files: HashMap<PathBuf, String>,
}

impl MultiFileSourceProvider {
    #[must_use]
    pub fn new(root: impl Into<PathBuf>, root_source: impl Into<String>) -> Self {
        Self {
            root: root.into(),
            root_source: root_source.into(),
            files: HashMap::new(),
        }
    }

    /// Register a sibling file's source, keyed by its path relative to the
    /// root's own directory (e.g. `"alpha.mtl"`).
    #[must_use]
    pub fn with_file(
        mut self,
        relative_path: impl Into<PathBuf>,
        source: impl Into<String>,
    ) -> Self {
        let dir = self.root.parent().unwrap_or_else(|| Path::new("."));
        self.files
            .insert(dir.join(relative_path.into()), source.into());
        self
    }
}

impl SourceProvider for MultiFileSourceProvider {
    fn read(&self, module_path: &[String], file_path: &Path) -> Result<String, MetelError> {
        if file_path == self.root {
            return Ok(self.root_source.clone());
        }
        if let Some(source) = self.files.get(file_path) {
            return Ok(source.clone());
        }
        if let Some(source) = crate::stdlib::lookup(module_path) {
            return Ok(source.to_string());
        }
        Err(module_error(
            format!(
                "in-memory source provider has no source for module '{}'",
                file_path.display()
            ),
            file_path,
        ))
    }

    fn canonicalize(&self, candidate: &Path) -> Option<PathBuf> {
        if candidate == self.root {
            return Some(self.root.clone());
        }
        self.files
            .contains_key(candidate)
            .then(|| candidate.to_path_buf())
    }
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct LoadedModule {
    pub module_path: Vec<String>,
    pub file_path: PathBuf,
    pub program: Program,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct ModuleGraph {
    pub root: PathBuf,
    pub modules: Vec<LoadedModule>,
    /// Maps alias module paths to their canonical module path.
    /// Populated when the same physical file is reachable via multiple logical paths
    /// (diamond dependency). e.g. `["right", "base"] -> ["left", "base"]`.
    pub path_aliases: HashMap<Vec<String>, Vec<String>>,
}

/// Load a module graph from `path` using the default provider: embedded stdlib
/// for `std::…` modules, filesystem for everything else (RFC-0058 / METEL-181).
///
/// # Errors
/// Returns an error if `path` does not exist, if any reachable module fails to
/// read or parse, or if the import graph contains a circular dependency.
pub fn load_root(path: impl AsRef<Path>) -> Result<ModuleGraph, MetelError> {
    load_root_with(path, &EmbeddedStdlibProvider::default())
}

/// Load a module graph from `path`, reading source through `provider` (RFC-0058).
///
/// # Errors
/// Returns an error if `path` does not exist, if any reachable module fails to
/// read (via `provider`) or parse, or if the import graph contains a circular
/// dependency.
pub fn load_root_with<P: SourceProvider>(
    path: impl AsRef<Path>,
    provider: &P,
) -> Result<ModuleGraph, MetelError> {
    let root = canonicalize_existing(path.as_ref())?;
    load_root_at(root, provider)
}

/// Load a graph rooted at a virtual source file through `provider`.
///
/// Unlike [`load_root_with`], `path` is not canonicalized and need not exist on
/// disk. This lets a single in-memory root enter the normal module pipeline
/// without turning an overlay into an accidental filesystem read. Providers
/// which need multi-file overlays can use the same entry point.
///
/// # Errors
/// Returns an error if the provider cannot supply the root or an imported
/// module, or if parsing or module-graph validation fails.
pub fn load_virtual_root_with<P: SourceProvider>(
    path: impl AsRef<Path>,
    provider: &P,
) -> Result<ModuleGraph, MetelError> {
    load_root_at(path.as_ref().to_path_buf(), provider)
}

fn load_root_at<P: SourceProvider>(root: PathBuf, provider: &P) -> Result<ModuleGraph, MetelError> {
    let root_dir = root
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf();
    let mut loader = Loader::new(root_dir, provider);
    // Synthesize the binary-embedded std:: modules into the graph ahead of user
    // code, so std::core is a real module flowing through the normal pipeline
    // (METEL-181) rather than a virtual injection.
    loader.load_embedded_stdlib()?;
    loader.load_module(root.clone(), Vec::new())?;
    let mut graph = ModuleGraph {
        root,
        modules: loader.modules,
        path_aliases: loader.path_aliases,
    };
    // RFC-0160: erase transparent type aliases before anything downstream runs.
    crate::type_alias::expand(&mut graph)?;
    Ok(graph)
}

/// Parse a single `.mtl` file and return its `Program`.
/// Single-file shim for tests that only need one-module typechecking.
///
/// # Errors
/// Returns an error if `path` does not exist, cannot be read, or fails to parse.
#[allow(dead_code)] // public API used by module-loading test harness
pub fn load_program(path: impl AsRef<Path>) -> Result<Program, MetelError> {
    let path = canonicalize_existing(path.as_ref())?;
    let source = fs::read_to_string(&path)
        .map_err(|e| MetelError::internal(format!("could not read {}: {e}", path.display())))?;
    let filename = path.file_name().unwrap_or_default().to_string_lossy();
    crate::parser::parse(&source, &filename)
}

struct Loader<'a> {
    modules: Vec<LoadedModule>,
    visited: HashSet<PathBuf>,
    /// Maps each file's canonical path to the module path assigned on first visit.
    file_to_path: HashMap<PathBuf, Vec<String>>,
    /// Alias map: alternative module path → canonical module path.
    path_aliases: HashMap<Vec<String>, Vec<String>>,
    stack: Vec<PathBuf>,
    root_dir: PathBuf,
    provider: &'a dyn SourceProvider,
}

impl<'a> Loader<'a> {
    fn new(root_dir: PathBuf, provider: &'a dyn SourceProvider) -> Self {
        Self {
            modules: Vec::new(),
            visited: HashSet::new(),
            file_to_path: HashMap::new(),
            path_aliases: HashMap::new(),
            stack: Vec::new(),
            root_dir,
            provider,
        }
    }
}

impl Loader<'_> {
    /// Parse the binary-embedded `std::` sources and add them to the graph as real
    /// modules (METEL-181). Their `module_path` is the logical path (e.g.
    /// `["std","core"]`); the synthetic `file_path` is for diagnostics only.
    /// Source is read through the provider so overlays (e.g. an LSP buffer
    /// shadowing a stdlib module in tests) keep working per RFC-0058.
    fn load_embedded_stdlib(&mut self) -> Result<(), MetelError> {
        for module_path in crate::stdlib::module_paths() {
            let filename = format!("<embedded {}>", module_path.join("::"));
            let source = self
                .provider
                .read(&module_path, Path::new(&filename))
                .or_else(|_| {
                    // A pure-filesystem provider cannot serve embedded paths;
                    // fall back to the compiled-in source.
                    crate::stdlib::lookup(&module_path)
                        .map(str::to_string)
                        .ok_or_else(|| {
                            MetelError::internal(format!(
                                "embedded stdlib module {} missing",
                                module_path.join("::")
                            ))
                        })
                })?;
            let program = parse_stdlib_cached(&module_path, &source, &filename)?;
            let file_path = PathBuf::from(&filename);
            self.visited.insert(file_path.clone());
            self.file_to_path
                .insert(file_path.clone(), module_path.clone());
            self.modules.push(LoadedModule {
                module_path,
                file_path,
                program,
            });
        }
        Ok(())
    }

    fn load_module(
        &mut self,
        file_path: PathBuf,
        module_path: Vec<String>,
    ) -> Result<(), MetelError> {
        let root_dir = self.root_dir.clone();
        if let Some(cycle_start) = self.stack.iter().position(|p| p == &file_path) {
            let mut chain: Vec<String> = self.stack[cycle_start..]
                .iter()
                .map(|p| p.display().to_string())
                .collect();
            chain.push(file_path.display().to_string());
            return Err(module_error(
                format!("circular module dependency: {}", chain.join(" -> ")),
                &file_path,
            ));
        }

        if self.visited.contains(&file_path) {
            // Same physical file reachable via a different logical path (diamond dependency).
            // Record the alias so the name resolver can dereference it. See ADR-0031.
            if let Some(canonical) = self.file_to_path.get(&file_path) {
                if *canonical != module_path {
                    self.path_aliases.insert(module_path, canonical.clone());
                }
            }
            return Ok(());
        }

        // `std` is reserved for the standard library; a user module may not occupy
        // that namespace. See RFC-0058 and the spec's "Reserved namespaces".
        validate_std_namespace(&module_path, &file_path)?;

        let source = self.provider.read(&module_path, &file_path)?;
        let filename = file_path.display().to_string();
        let program = parser::parse(&source, &filename)?;

        validate_super_root(&program, &module_path, &file_path)?;

        self.stack.push(file_path.clone());
        for import in &program.imports {
            if let Some((mod_segs, child)) = resolve_import_module(
                self.provider,
                &file_path,
                &root_dir,
                &module_path,
                &import.path.root,
                &import.path.tree,
            )? {
                // Already canonical -- `resolve_import_module` only returns a
                // path the provider itself confirmed and canonicalized
                // (metel-core#1147); a second, always-real-filesystem
                // canonicalization here would defeat that for an in-memory
                // overlay's imports.
                let child_path = child_module_path(&module_path, &import.path.root, &mod_segs);
                self.load_module(child, child_path)?;
            }
        }
        // An `export path::Name;` re-export (#660) names a module the same way an
        // `import` does -- `ExportDecl` and `ImportDecl` share the identical
        // `ImportPath` shape -- but nothing previously followed it to actually load
        // the target file. A module reachable *only* through another module's
        // `export`, with no `import` anywhere pulling it in directly, was simply
        // never parsed: its declarations existed nowhere in the compiled program, so
        // even a direct `import a::b::Name;` bypassing the re-export failed with
        // "unknown struct/enum/name", not just the re-export path itself.
        for export in &program.exports {
            if let Some((mod_segs, child)) = resolve_import_module(
                self.provider,
                &file_path,
                &root_dir,
                &module_path,
                &export.path.root,
                &export.path.tree,
            )? {
                let child_path = child_module_path(&module_path, &export.path.root, &mod_segs);
                self.load_module(child, child_path)?;
            }
        }
        self.stack.pop();

        self.visited.insert(file_path.clone());
        self.file_to_path
            .insert(file_path.clone(), module_path.clone());
        self.modules.push(LoadedModule {
            module_path,
            file_path,
            program,
        });
        Ok(())
    }
}

/// Compute the canonical module path for a child module.
///
/// For most root variants, delegates to `resolve_path_root` then appends `mod_segs`.
/// For `Name(n)`, however, `resolve_import_module` already puts `n` as `mod_segs[0]`,
/// so the base is just `parent` — using `resolve_path_root` here would double-include `n`.
/// See ADR-0023.
fn child_module_path(parent: &[String], root: &PathRoot, mod_segs: &[String]) -> Vec<String> {
    let base = match root {
        PathRoot::Name(_) => parent.to_vec(),
        _ => resolve_path_root(root, parent),
    };
    let mut path = base;
    path.extend_from_slice(mod_segs);
    path
}

fn canonicalize_existing(path: &Path) -> Result<PathBuf, MetelError> {
    path.canonicalize().map_err(|e| {
        module_error(
            format!("failed to resolve module '{}': {e}", path.display()),
            path,
        )
    })
}

/// The directory a module's own submodules live in.
///
/// A non-root module `parser.mtl` (module path `["parser"]`) owns a directory named
/// after itself, `parser/`, sitting *beside* the file rather than being its own
/// containing directory -- "a directory module with a public facade is expressed by
/// placing `name.mtl` alongside the `name/` directory" (`modules.md`, File-to-Module
/// Mapping). The root module (empty module path) has no such nesting: its "own"
/// directory for this purpose is simply wherever it already lives, `parent_dir`
/// itself -- the special case that made this indistinguishable from an ordinary
/// sibling lookup for as long as every test happened to write `self::`/a bare path
/// only from the root file (#663).
fn own_submodule_dir(parent_dir: &Path, current_module_path: &[String]) -> PathBuf {
    match current_module_path.last() {
        Some(name) => parent_dir.join(name),
        None => parent_dir.to_path_buf(),
    }
}

/// Resolve an import declaration to a module file.
///
/// Returns `Ok(Some((segments, path)))` when a `.mtl` file is found.
/// Returns `Ok(None)` for `std::` imports (handled by `CorePrelude` in the typechecker)
/// and for glob/group imports that carry no resolvable file segment.
/// Returns `Err` if the import names a concrete module that cannot be found.
///
/// Path mapping: `::` separators map to `/` directory separators.
/// `import parser::ast::Ast` tries `parser/ast.mtl` first, then `parser.mtl` —
/// the longest matching prefix wins.
fn resolve_import_module(
    provider: &dyn SourceProvider,
    parent_file: &Path,
    root_dir: &Path,
    current_module_path: &[String],
    root: &PathRoot,
    tree: &ImportTree,
) -> Result<Option<(Vec<String>, PathBuf)>, MetelError> {
    let parent_dir = parent_file.parent().unwrap_or_else(|| Path::new("."));

    match root {
        // `std::` modules are never filesystem files: every embedded stdlib
        // module is synthesized into the graph up front (load_embedded_stdlib),
        // so a std:: import never resolves to a file. An import of a
        // non-existent std module is reported by name resolution against the
        // (real) std module surfaces, not by file lookup.
        PathRoot::Std => Ok(None),

        PathRoot::Root => {
            let segs = import_tree_segments(tree);
            resolve_in_dir(provider, root_dir, &segs, parent_file)
        }

        PathRoot::Super => {
            let super_dir = if parent_dir == root_dir {
                root_dir.to_path_buf()
            } else {
                parent_dir.parent().unwrap_or(parent_dir).to_path_buf()
            };
            let segs = import_tree_segments(tree);
            resolve_in_dir(provider, &super_dir, &segs, parent_file)
        }

        // An existing, passing test
        // (accepts_root_self_super_std_and_child_roots_in_non_root_modules) asserts
        // that `self::` from a non-root module can reach a true top-level sibling,
        // the same file `root::`/a bare path from that position reaches -- its
        // fixture has no directory named after the current module at all, so it
        // never exercises the case `own_submodule_dir` is for. Applying the same
        // try-then-fall-back-to-sibling order as the bare-path case below satisfies
        // both: a sibling with no own-submodule alternative still resolves exactly
        // as that test expects, while `self::ast::Ast` written inside `parser.mtl`
        // now also reaches `parser/ast.mtl` when it exists (#663).
        PathRoot::Self_ => {
            let segs = import_tree_segments(tree);
            if !current_module_path.is_empty() {
                let self_dir = own_submodule_dir(parent_dir, current_module_path);
                if let Some(result) = find_module_file(provider, &self_dir, &segs) {
                    return Ok(Some(result));
                }
            }
            resolve_in_dir(provider, parent_dir, &segs, parent_file)
        }

        PathRoot::Name(name) => {
            let mut segs = vec![name.clone()];
            segs.extend(import_tree_segments(tree));
            if segs.is_empty() {
                return Ok(None);
            }
            // A bare (unprefixed) path is ambiguous between "one of my own
            // submodules" and "a sibling of me" (#663) -- `parser.mtl` re-exporting
            // `ast::Ast` means its own `parser/ast.mtl`, but re-exporting
            // `lexer::Token` (also written bare, in the very same file) means the
            // true top-level sibling `lexer.mtl`, not `parser/lexer.mtl`. Try the
            // module's own submodule directory first (the more specific match), and
            // only fall back to sibling resolution -- the pre-#663 behavior, and
            // still correct for the root module, which has no submodule directory
            // of its own to prefer -- if nothing is found there.
            if !current_module_path.is_empty() {
                let self_dir = own_submodule_dir(parent_dir, current_module_path);
                if let Some(result) = find_module_file(provider, &self_dir, &segs) {
                    return Ok(Some(result));
                }
            }
            resolve_in_dir(provider, parent_dir, &segs, parent_file)
        }
    }
}

fn resolve_in_dir(
    provider: &dyn SourceProvider,
    dir: &Path,
    segs: &[String],
    source_file: &Path,
) -> Result<Option<(Vec<String>, PathBuf)>, MetelError> {
    if segs.is_empty() {
        return Ok(None);
    }
    match find_module_file(provider, dir, segs) {
        Some(result) => Ok(Some(result)),
        None => Err(module_error(
            format!("cannot find module file for `{}`", segs.join("::")),
            source_file,
        )),
    }
}

/// Collect all identifier segments from an import tree in path order.
/// Stops at the terminal item(s) — returns their names as the last segment(s).
/// For `ast::Ast` → `["ast", "Ast"]`; for `ast::{A, B}` → `["ast"]`; for `*` → `[]`.
fn import_tree_segments(tree: &ImportTree) -> Vec<String> {
    match tree {
        ImportTree::Name { name, .. } => vec![name.clone()],
        ImportTree::Path { name, tree } => {
            let mut segs = vec![name.clone()];
            segs.extend(import_tree_segments(tree));
            segs
        }
        ImportTree::Group(_) | ImportTree::Glob => vec![],
    }
}

/// Try path prefixes from longest to shortest, returning the first `.mtl`
/// `provider` confirms exists, already in its canonical form
/// (metel-core#1147 -- delegates to the provider rather than a hardcoded
/// `Path::exists`/`canonicalize`, so an in-memory overlay's imports resolve
/// too, not just the real filesystem's).
fn find_module_file(
    provider: &dyn SourceProvider,
    base_dir: &Path,
    segs: &[String],
) -> Option<(Vec<String>, PathBuf)> {
    for len in (1..=segs.len()).rev() {
        let prefix = &segs[..len];
        let mut candidate = base_dir.to_path_buf();
        for seg in prefix {
            candidate = candidate.join(seg);
        }
        let file = candidate.with_extension("mtl");
        if let Some(canonical) = provider.canonicalize(&file) {
            return Some((prefix.to_vec(), canonical));
        }
    }
    None
}

/// Reject any user module whose path begins with `std`. The `std` namespace is
/// reserved for the standard library; enforcing it here (the file-discovery
/// layer) matches the `std` keyword reservation in the grammar. See RFC-0058.
fn validate_std_namespace(module_path: &[String], file_path: &Path) -> Result<(), MetelError> {
    if module_path.first().map(String::as_str) == Some("std") {
        return Err(module_error(
            "module path `std::…` is reserved for the standard library",
            file_path,
        ));
    }
    Ok(())
}

fn validate_super_root(
    program: &Program,
    module_path: &[String],
    file_path: &Path,
) -> Result<(), MetelError> {
    if !module_path.is_empty() {
        return Ok(());
    }

    for import in &program.imports {
        if import.path.root == PathRoot::Super || import_tree_contains_super(&import.path.tree) {
            return Err(module_error(
                "`super::` is invalid from the root module",
                file_path,
            ));
        }
    }

    Ok(())
}

fn import_tree_contains_super(tree: &ImportTree) -> bool {
    match tree {
        ImportTree::Name { .. } | ImportTree::Glob => false,
        ImportTree::Group(trees) => trees.iter().any(import_tree_contains_super),
        ImportTree::Path { tree, .. } => import_tree_contains_super(tree),
    }
}

fn module_error(message: impl Into<String>, path: &Path) -> MetelError {
    MetelError::ParseError {
        code: ParseErrorCode::P0001,
        message: message.into(),
        start: 0,
        end: 0,
        filename: path.display().to_string(),
        line: 1,
        col: 1,
        source_line: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn std_namespace_is_reserved_for_user_modules() {
        let path = Path::new("std.mtl");
        let err = validate_std_namespace(&["std".to_string()], path)
            .expect_err("a user module named `std` must be rejected");
        assert!(
            err.to_string()
                .contains("reserved for the standard library"),
            "got: {err}"
        );
        // Nested under std is also rejected.
        assert!(validate_std_namespace(&["std".to_string(), "io".to_string()], path).is_err());
    }

    #[test]
    fn non_std_module_paths_are_allowed() {
        let path = Path::new("foo.mtl");
        assert!(validate_std_namespace(&[], path).is_ok());
        assert!(validate_std_namespace(&["foo".to_string()], path).is_ok());
        // `standard` is a different name, not the reserved `std` segment.
        assert!(validate_std_namespace(&["standard".to_string()], path).is_ok());
    }

    #[test]
    fn source_provider_overlay_supplies_in_memory_source() {
        // Proves the SourceProvider abstraction supports an in-memory overlay
        // (the LSP unsaved-buffer use case) without touching disk.
        struct Overlay;
        impl SourceProvider for Overlay {
            fn read(&self, module_path: &[String], _file: &Path) -> Result<String, MetelError> {
                assert_eq!(module_path, &["greeter".to_string()]);
                Ok("pub fun hi() {}".to_string())
            }
        }
        let provider = Overlay;
        let src = provider
            .read(&["greeter".to_string()], Path::new("ignored.mtl"))
            .unwrap();
        assert!(src.contains("fun hi"));
    }

    #[test]
    fn multi_file_source_provider_resolves_an_import() {
        // metel-core#1147: the virtual-root path could previously only ever
        // load its single root file -- any import failed, since
        // find_module_file's Path::exists check has no way to see an
        // in-memory sibling. Proves the fix: MultiFileSourceProvider's own
        // canonicalize override is now actually consulted during import
        // discovery, not bypassed by a hardcoded filesystem check.
        let provider = MultiFileSourceProvider::new(
            "editor.mtl",
            "import alpha::helper;\nfun main() -> i64 { helper() }\n",
        )
        .with_file("alpha.mtl", "public fun helper() -> i64 { 42 }\n");

        let graph = load_virtual_root_with("editor.mtl", &provider)
            .expect("the import should resolve through the provider, not the filesystem");
        let module_paths: Vec<&[String]> = graph
            .modules
            .iter()
            .map(|m| m.module_path.as_slice())
            .collect();
        assert!(
            module_paths.contains(&["alpha".to_string()].as_slice()),
            "alpha's module should have loaded: {module_paths:?}"
        );
    }

    #[test]
    fn multi_file_source_provider_reports_a_missing_sibling() {
        // The other half of the same fix: a genuinely absent sibling must
        // still fail (not silently succeed by falling through to some
        // stale filesystem state), with the same diagnostic shape a real
        // missing file gets.
        let provider = MultiFileSourceProvider::new("editor.mtl", "import alpha::helper;\n");
        let err = load_virtual_root_with("editor.mtl", &provider)
            .expect_err("alpha.mtl was never registered with the provider");
        assert!(
            err.to_string().contains("cannot find module file"),
            "got: {err}"
        );
    }

    #[test]
    fn virtual_root_loads_without_an_on_disk_root() {
        let provider = InMemorySourceProvider::new("playground.mtl", "fun main() {}");
        let graph = load_virtual_root_with("playground.mtl", &provider)
            .expect("an in-memory root should load without filesystem access");

        assert!(graph.root.ends_with("playground.mtl"));
        assert!(graph
            .modules
            .iter()
            .any(|module| module.module_path.is_empty()));
    }
}
