//! Stdlib-only native host bindings (METEL-182).
//!
//! A `native(@std.core.print) fun print(x: String);` declaration binds a stdlib
//! function to a host (Rust) implementation. The surface id (`@std.core.print`)
//! is lowered to a closed [`NativeKey`] so dispatch never depends on the surface
//! spelling, and coverage between declared native functions and registered host
//! implementations can be checked exhaustively.
//!
//! The enum is intentionally closed: every variant must have exactly one stdlib
//! declaration and exactly one host implementation. Third-party native providers
//! are an FFI-era concern, out of scope here.

/// A host-backed standard-library function, identified independently of its
/// surface name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NativeKey {
    /// `std::core::print` — write a value's Display form to stdout, no newline.
    StdCorePrint,
    /// `std::core::println` — write a value's Display form to stdout with newline.
    StdCorePrintln,
    /// `std::core::dbg` — debug-print a value to stderr and return it unchanged.
    StdCoreDbg,
    /// `std::core::assert` — panic if the condition is false.
    StdCoreAssert,
    /// `std::core::assert(boolean, String)` — the message-carrying assert
    /// overload; panics with the message if the condition is false.
    StdCoreAssertMsg,
    /// `std::core::clock` — milliseconds since the Unix epoch.
    StdCoreClock,
    /// `std::core::yolo_none` — panics unconditionally; `Perhaps::yolo()`'s `None` arm.
    StdCoreYoloNone,
    /// `std::core::yolo_err` — panics unconditionally, including the `Err` value's
    /// debug representation; `Result::yolo()`'s `Err` arm.
    StdCoreYoloErr,
    /// `std::core::panic(msg: String) -> !` — panics unconditionally with `msg`.
    StdCorePanic,
    /// `String::len` — number of characters in a string.
    StdCoreStringLen,
    /// `String::is_empty(self) -> boolean`.
    StdCoreStringIsEmpty,
    /// `String::to_upper(self) -> String`.
    StdCoreStringToUpper,
    /// `String::to_lower(self) -> String`.
    StdCoreStringToLower,
    /// `String::trim(self) -> String`.
    StdCoreStringTrim,
    /// `String::trim_start(self) -> String`.
    StdCoreStringTrimStart,
    /// `String::trim_end(self) -> String`.
    StdCoreStringTrimEnd,
    /// `String::contains(self, String) -> boolean`.
    StdCoreStringContains,
    /// `String::starts_with(self, String) -> boolean`.
    StdCoreStringStartsWith,
    /// `String::ends_with(self, String) -> boolean`.
    StdCoreStringEndsWith,
    /// `String::index_of(self, String) -> Perhaps<i64>` — scalar index.
    StdCoreStringIndexOf,
    /// `String::split(self, String) -> String[]`.
    StdCoreStringSplit,
    /// `String::replace(self, String, String) -> String`.
    StdCoreStringReplace,
    /// `String::repeat(self, i64) -> String`.
    StdCoreStringRepeat,
    /// `String::join(String[], String) -> String` — associated (no receiver).
    StdCoreStringJoin,
    /// `String::chars(self) -> Char[]`.
    StdCoreStringChars,
    /// `String::char_at(self, i64) -> Perhaps<Char>` — scalar index.
    StdCoreStringCharAt,
    /// `String::substring(self, i64, i64) -> String` — clamped scalar range.
    StdCoreStringSubstring,
    /// `Display::to_string` for every displayable primitive — the host formats
    /// the receiver by its runtime value, so one key serves all 13 impls.
    StdCoreToString,
    /// `i8::from(numeric)` — convert any numeric value to i8.
    StdCoreI8From,
    /// `i16::from(numeric)` — convert any numeric value to i16.
    StdCoreI16From,
    /// `i32::from(numeric)` — convert any numeric value to i32.
    StdCoreI32From,
    /// `i64::from(numeric)` — convert any numeric value to i64.
    StdCoreI64From,
    /// `u8::from(numeric)` — convert any numeric value to u8.
    StdCoreU8From,
    /// `u16::from(numeric)` — convert any numeric value to u16.
    StdCoreU16From,
    /// `u32::from(numeric | Char)` — convert a numeric value or a Char code
    /// point to u32.
    StdCoreU32From,
    /// `u64::from(numeric)` — convert any numeric value to u64.
    StdCoreU64From,
    /// `f32::from(numeric)` — convert any numeric value to f32.
    StdCoreF32From,
    /// `f64::from(numeric)` — convert any numeric value to f64.
    StdCoreF64From,
    /// `Char::from(u32)` — code point to Char; panics on invalid scalars.
    StdCoreCharFrom,
    /// `List::new()` — empty list.
    StdCoreListNew,
    /// `List::from(T[])` — list with a copy of the array's elements.
    StdCoreListFrom,
    /// `List::push(&mut self, T)` — append an element.
    StdCoreListPush,
    /// `List::pop(&mut self) -> Perhaps<T>` — remove and return the last element.
    StdCoreListPop,
    /// `List::len(self) -> i64` — number of elements.
    StdCoreListLen,
    /// `List::get(self, i64) -> Perhaps<T>` — element at an index.
    StdCoreListGet,
    /// `List::set(&mut self, i64, T) -> Perhaps<T>` — overwrite an element in place,
    /// returning the value it replaced, or `None` if the index was out of bounds.
    StdCoreListSet,
    /// `List::as_slice(self) -> T[]` — the backing array.
    StdCoreListAsSlice,

    // ── std::env ────────────────────────────────────────────────────────────
    /// `env::get(String) -> Perhaps<String>` — value of an environment variable.
    StdEnvVar,
    /// `env::vars() -> EnvVar[]` — all environment variables.
    StdEnvVars,

    // ── std::fs ─────────────────────────────────────────────────────────────
    /// `fs::read_to_string(String) -> Result<String, OsError>`.
    StdFsReadToString,
    /// `fs::write_string(String, String) -> Result<(), OsError>`.
    StdFsWriteString,
    /// `fs::append_string(String, String) -> Result<(), OsError>`.
    StdFsAppendString,
    /// `fs::exists(String) -> boolean`.
    StdFsExists,
    /// `fs::read_dir(String) -> Result<String[], OsError>` — entry names.
    StdFsReadDir,
    /// `fs::create_dir(String) -> Result<(), OsError>`.
    StdFsCreateDir,
    /// `fs::create_dir_all(String) -> Result<(), OsError>`.
    StdFsCreateDirAll,
    /// `fs::remove_file(String) -> Result<(), OsError>`.
    StdFsRemoveFile,
    /// `fs::remove_dir(String) -> Result<(), OsError>`.
    StdFsRemoveDir,
    /// `fs::remove_dir_all(String) -> Result<(), OsError>`.
    StdFsRemoveDirAll,

    // ── std::process ────────────────────────────────────────────────────────
    /// `process::args() -> String[]` — the process command-line arguments.
    StdProcessArgs,
    /// `process::run(String, String[]) -> Result<ProcessOutput, OsError>`.
    StdProcessRun,
}

impl NativeKey {
    /// Lower a dotted surface id (`["std","core","print"]`) to a [`NativeKey`].
    /// Returns `None` for an unknown id — the caller reports it as an error so
    /// the closed enum stays the single source of truth for host bindings.
    pub fn from_path(path: &[String]) -> Option<NativeKey> {
        let segments: Vec<&str> = path.iter().map(String::as_str).collect();
        let key = match segments.as_slice() {
            ["std", "core", "print"] => NativeKey::StdCorePrint,
            ["std", "core", "println"] => NativeKey::StdCorePrintln,
            ["std", "core", "dbg"] => NativeKey::StdCoreDbg,
            ["std", "core", "assert"] => NativeKey::StdCoreAssert,
            ["std", "core", "assert_msg"] => NativeKey::StdCoreAssertMsg,
            ["std", "core", "clock"] => NativeKey::StdCoreClock,
            ["std", "core", "yolo_none"] => NativeKey::StdCoreYoloNone,
            ["std", "core", "yolo_err"] => NativeKey::StdCoreYoloErr,
            ["std", "core", "panic"] => NativeKey::StdCorePanic,
            ["std", "core", "string_len"] => NativeKey::StdCoreStringLen,
            ["std", "core", "string_is_empty"] => NativeKey::StdCoreStringIsEmpty,
            ["std", "core", "string_to_upper"] => NativeKey::StdCoreStringToUpper,
            ["std", "core", "string_to_lower"] => NativeKey::StdCoreStringToLower,
            ["std", "core", "string_trim"] => NativeKey::StdCoreStringTrim,
            ["std", "core", "string_trim_start"] => NativeKey::StdCoreStringTrimStart,
            ["std", "core", "string_trim_end"] => NativeKey::StdCoreStringTrimEnd,
            ["std", "core", "string_contains"] => NativeKey::StdCoreStringContains,
            ["std", "core", "string_starts_with"] => NativeKey::StdCoreStringStartsWith,
            ["std", "core", "string_ends_with"] => NativeKey::StdCoreStringEndsWith,
            ["std", "core", "string_index_of"] => NativeKey::StdCoreStringIndexOf,
            ["std", "core", "string_split"] => NativeKey::StdCoreStringSplit,
            ["std", "core", "string_replace"] => NativeKey::StdCoreStringReplace,
            ["std", "core", "string_repeat"] => NativeKey::StdCoreStringRepeat,
            ["std", "core", "string_join"] => NativeKey::StdCoreStringJoin,
            ["std", "core", "string_chars"] => NativeKey::StdCoreStringChars,
            ["std", "core", "string_char_at"] => NativeKey::StdCoreStringCharAt,
            ["std", "core", "string_substring"] => NativeKey::StdCoreStringSubstring,
            ["std", "core", "to_string"] => NativeKey::StdCoreToString,
            ["std", "core", "i8_from"] => NativeKey::StdCoreI8From,
            ["std", "core", "i16_from"] => NativeKey::StdCoreI16From,
            ["std", "core", "i32_from"] => NativeKey::StdCoreI32From,
            ["std", "core", "i64_from"] => NativeKey::StdCoreI64From,
            ["std", "core", "u8_from"] => NativeKey::StdCoreU8From,
            ["std", "core", "u16_from"] => NativeKey::StdCoreU16From,
            ["std", "core", "u32_from"] => NativeKey::StdCoreU32From,
            ["std", "core", "u64_from"] => NativeKey::StdCoreU64From,
            ["std", "core", "f32_from"] => NativeKey::StdCoreF32From,
            ["std", "core", "f64_from"] => NativeKey::StdCoreF64From,
            ["std", "core", "char_from"] => NativeKey::StdCoreCharFrom,
            ["std", "core", "list_new"] => NativeKey::StdCoreListNew,
            ["std", "core", "list_from"] => NativeKey::StdCoreListFrom,
            ["std", "core", "list_push"] => NativeKey::StdCoreListPush,
            ["std", "core", "list_pop"] => NativeKey::StdCoreListPop,
            ["std", "core", "list_len"] => NativeKey::StdCoreListLen,
            ["std", "core", "list_get"] => NativeKey::StdCoreListGet,
            ["std", "core", "list_set"] => NativeKey::StdCoreListSet,
            ["std", "core", "list_as_slice"] => NativeKey::StdCoreListAsSlice,
            ["std", "env", "get"] => NativeKey::StdEnvVar,
            ["std", "env", "vars"] => NativeKey::StdEnvVars,
            ["std", "fs", "read_to_string"] => NativeKey::StdFsReadToString,
            ["std", "fs", "write_string"] => NativeKey::StdFsWriteString,
            ["std", "fs", "append_string"] => NativeKey::StdFsAppendString,
            ["std", "fs", "exists"] => NativeKey::StdFsExists,
            ["std", "fs", "read_dir"] => NativeKey::StdFsReadDir,
            ["std", "fs", "create_dir"] => NativeKey::StdFsCreateDir,
            ["std", "fs", "create_dir_all"] => NativeKey::StdFsCreateDirAll,
            ["std", "fs", "remove_file"] => NativeKey::StdFsRemoveFile,
            ["std", "fs", "remove_dir"] => NativeKey::StdFsRemoveDir,
            ["std", "fs", "remove_dir_all"] => NativeKey::StdFsRemoveDirAll,
            ["std", "process", "args"] => NativeKey::StdProcessArgs,
            ["std", "process", "run"] => NativeKey::StdProcessRun,
            _ => return None,
        };
        Some(key)
    }

    /// The surface id this key lowers from, for diagnostics.
    #[must_use]
    pub fn surface_id(&self) -> &'static str {
        match self {
            NativeKey::StdCorePrint => "@std.core.print",
            NativeKey::StdCorePrintln => "@std.core.println",
            NativeKey::StdCoreDbg => "@std.core.dbg",
            NativeKey::StdCoreAssert => "@std.core.assert",
            NativeKey::StdCoreAssertMsg => "@std.core.assert_msg",
            NativeKey::StdCoreClock => "@std.core.clock",
            NativeKey::StdCoreYoloNone => "@std.core.yolo_none",
            NativeKey::StdCoreYoloErr => "@std.core.yolo_err",
            NativeKey::StdCorePanic => "@std.core.panic",
            NativeKey::StdCoreStringLen => "@std.core.string_len",
            NativeKey::StdCoreStringIsEmpty => "@std.core.string_is_empty",
            NativeKey::StdCoreStringToUpper => "@std.core.string_to_upper",
            NativeKey::StdCoreStringToLower => "@std.core.string_to_lower",
            NativeKey::StdCoreStringTrim => "@std.core.string_trim",
            NativeKey::StdCoreStringTrimStart => "@std.core.string_trim_start",
            NativeKey::StdCoreStringTrimEnd => "@std.core.string_trim_end",
            NativeKey::StdCoreStringContains => "@std.core.string_contains",
            NativeKey::StdCoreStringStartsWith => "@std.core.string_starts_with",
            NativeKey::StdCoreStringEndsWith => "@std.core.string_ends_with",
            NativeKey::StdCoreStringIndexOf => "@std.core.string_index_of",
            NativeKey::StdCoreStringSplit => "@std.core.string_split",
            NativeKey::StdCoreStringReplace => "@std.core.string_replace",
            NativeKey::StdCoreStringRepeat => "@std.core.string_repeat",
            NativeKey::StdCoreStringJoin => "@std.core.string_join",
            NativeKey::StdCoreStringChars => "@std.core.string_chars",
            NativeKey::StdCoreStringCharAt => "@std.core.string_char_at",
            NativeKey::StdCoreStringSubstring => "@std.core.string_substring",
            NativeKey::StdCoreToString => "@std.core.to_string",
            NativeKey::StdCoreI8From => "@std.core.i8_from",
            NativeKey::StdCoreI16From => "@std.core.i16_from",
            NativeKey::StdCoreI32From => "@std.core.i32_from",
            NativeKey::StdCoreI64From => "@std.core.i64_from",
            NativeKey::StdCoreU8From => "@std.core.u8_from",
            NativeKey::StdCoreU16From => "@std.core.u16_from",
            NativeKey::StdCoreU32From => "@std.core.u32_from",
            NativeKey::StdCoreU64From => "@std.core.u64_from",
            NativeKey::StdCoreF32From => "@std.core.f32_from",
            NativeKey::StdCoreF64From => "@std.core.f64_from",
            NativeKey::StdCoreCharFrom => "@std.core.char_from",
            NativeKey::StdCoreListNew => "@std.core.list_new",
            NativeKey::StdCoreListFrom => "@std.core.list_from",
            NativeKey::StdCoreListPush => "@std.core.list_push",
            NativeKey::StdCoreListPop => "@std.core.list_pop",
            NativeKey::StdCoreListLen => "@std.core.list_len",
            NativeKey::StdCoreListGet => "@std.core.list_get",
            NativeKey::StdCoreListSet => "@std.core.list_set",
            NativeKey::StdCoreListAsSlice => "@std.core.list_as_slice",
            NativeKey::StdEnvVar => "@std.env.get",
            NativeKey::StdEnvVars => "@std.env.vars",
            NativeKey::StdFsReadToString => "@std.fs.read_to_string",
            NativeKey::StdFsWriteString => "@std.fs.write_string",
            NativeKey::StdFsAppendString => "@std.fs.append_string",
            NativeKey::StdFsExists => "@std.fs.exists",
            NativeKey::StdFsReadDir => "@std.fs.read_dir",
            NativeKey::StdFsCreateDir => "@std.fs.create_dir",
            NativeKey::StdFsCreateDirAll => "@std.fs.create_dir_all",
            NativeKey::StdFsRemoveFile => "@std.fs.remove_file",
            NativeKey::StdFsRemoveDir => "@std.fs.remove_dir",
            NativeKey::StdFsRemoveDirAll => "@std.fs.remove_dir_all",
            NativeKey::StdProcessArgs => "@std.process.args",
            NativeKey::StdProcessRun => "@std.process.run",
        }
    }

    /// Every variant — used by the coverage check that asserts each has a host
    /// implementation registered.
    pub const ALL: &'static [NativeKey] = &[
        NativeKey::StdCorePrint,
        NativeKey::StdCorePrintln,
        NativeKey::StdCoreDbg,
        NativeKey::StdCoreAssert,
        NativeKey::StdCoreAssertMsg,
        NativeKey::StdCoreClock,
        NativeKey::StdCoreYoloNone,
        NativeKey::StdCoreYoloErr,
        NativeKey::StdCorePanic,
        NativeKey::StdCoreStringLen,
        NativeKey::StdCoreStringIsEmpty,
        NativeKey::StdCoreStringToUpper,
        NativeKey::StdCoreStringToLower,
        NativeKey::StdCoreStringTrim,
        NativeKey::StdCoreStringTrimStart,
        NativeKey::StdCoreStringTrimEnd,
        NativeKey::StdCoreStringContains,
        NativeKey::StdCoreStringStartsWith,
        NativeKey::StdCoreStringEndsWith,
        NativeKey::StdCoreStringIndexOf,
        NativeKey::StdCoreStringSplit,
        NativeKey::StdCoreStringReplace,
        NativeKey::StdCoreStringRepeat,
        NativeKey::StdCoreStringJoin,
        NativeKey::StdCoreStringChars,
        NativeKey::StdCoreStringCharAt,
        NativeKey::StdCoreStringSubstring,
        NativeKey::StdCoreToString,
        NativeKey::StdCoreI8From,
        NativeKey::StdCoreI16From,
        NativeKey::StdCoreI32From,
        NativeKey::StdCoreI64From,
        NativeKey::StdCoreU8From,
        NativeKey::StdCoreU16From,
        NativeKey::StdCoreU32From,
        NativeKey::StdCoreU64From,
        NativeKey::StdCoreF32From,
        NativeKey::StdCoreF64From,
        NativeKey::StdCoreCharFrom,
        NativeKey::StdCoreListNew,
        NativeKey::StdCoreListFrom,
        NativeKey::StdCoreListPush,
        NativeKey::StdCoreListPop,
        NativeKey::StdCoreListLen,
        NativeKey::StdCoreListGet,
        NativeKey::StdCoreListSet,
        NativeKey::StdCoreListAsSlice,
        NativeKey::StdEnvVar,
        NativeKey::StdEnvVars,
        NativeKey::StdFsReadToString,
        NativeKey::StdFsWriteString,
        NativeKey::StdFsAppendString,
        NativeKey::StdFsExists,
        NativeKey::StdFsReadDir,
        NativeKey::StdFsCreateDir,
        NativeKey::StdFsCreateDirAll,
        NativeKey::StdFsRemoveFile,
        NativeKey::StdFsRemoveDir,
        NativeKey::StdFsRemoveDirAll,
        NativeKey::StdProcessArgs,
        NativeKey::StdProcessRun,
    ];
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_known_paths() {
        for key in NativeKey::ALL {
            let id = key.surface_id().trim_start_matches('@');
            let path: Vec<String> = id.split('.').map(str::to_string).collect();
            assert_eq!(NativeKey::from_path(&path), Some(*key), "for {id}");
        }
    }

    #[test]
    fn unknown_path_is_none() {
        assert_eq!(
            NativeKey::from_path(&["std".into(), "core".into(), "nope".into()]),
            None
        );
        assert_eq!(NativeKey::from_path(&["foo".into()]), None);
    }
}
