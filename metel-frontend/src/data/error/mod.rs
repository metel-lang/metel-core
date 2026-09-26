use crate::data::ast::Span;

/// One frame in a runtime call stack.
#[derive(Debug, Clone)]
pub struct FrameInfo {
    /// Name of the function that was entered.
    pub fn_name: String,
    /// Span of the call expression that invoked this frame.
    pub call_site: Span,
}

// ── Error code enums, one per pipeline phase ──────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseErrorCode {
    P0001, // Syntax error
    P0002, // Invalid integer literal
    P0003, // Invalid float literal
    P0004, // Invalid character literal
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeErrorCode {
    T0001, // Type mismatch
    T0002, // Annotation required
    T0003, // Undefined name
    T0004, // Arity mismatch
    T0005, // Invalid operand types
    T0006, // Assignment to immutable binding
    T0007, // Invalid cast
    T0008, // Non-exhaustive match
    T0009, // Private item access
    T0010, // Unannotated pub declaration
    T0011, // Import name conflict
    T0012, // Aspect bound not satisfied
    T0013, // Ambiguous aspect method resolution
    T0014, // Orphan implementation
    T0015, // Conflicting implementation
    T0016, // Function declared `-> !` does not diverge on all paths
    T0017, // Impl missing a required associated type definition (RFC-0082 §2)
    T0018, // Naming the concrete type of an opaque `extends Aspect` return value (RFC-0037)
    T0019, // Use of moved value
    T0021, // `break` or `continue` outside an enclosing loop
    T0022, // `extends Aspect` used outside parameter or return position
    T0023, // Assignment through a non-owning view (`T[]`)
    T0024, // Read-copy of a non-`Copy` value out of a reference (RFC-0067a §3a)
    T0025, // Aspect is not object-safe, used in `dyn` position (RFC-0008 §3)
    T0026, // Closure capture-list error (RFC-0050)
    T0027, // Closure requires `once` (RFC-0134)
    T0028, // Closure requires `var` (RFC-0153)
    T0029, // Mutating closure called through shared reference (RFC-0153)
    T0030, // Borrow into enclosing closure environment (RFC-0050)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeErrorCode {
    R0001, // No `main` function defined
    R0002, // `main` is not a valid entry point
    R0003, // Undefined variable at runtime
    R0004, // Index out of bounds
    R0005, // Tuple index out of bounds
    R0006, // Non-exhaustive match at runtime
    R0007, // Arithmetic error (division or remainder by zero)
    R0008, // Field not found
    R0009, // Method not found
    R0010, // Call on non-callable value
    R0011, // Invalid for-in iterator
    R0012, // Assertion failed
    R0013, // Unwrap on `None`/`Err` (`.yolo()`)
    R0014, // Explicit panic (`panic()`)
    R0015, // Re-entrant call to a mutating closure (RFC-0153)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InternalErrorCode {
    I0001, // Internal interpreter error (interpreter bug — should never happen)
    I0002, // Not implemented (feature not yet supported in this version)
}

macro_rules! impl_display_via_debug {
    ($t:ty) => {
        impl std::fmt::Display for $t {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{self:?}")
            }
        }
    };
}

impl_display_via_debug!(ParseErrorCode);
impl_display_via_debug!(TypeErrorCode);
impl_display_via_debug!(RuntimeErrorCode);
impl_display_via_debug!(InternalErrorCode);

// ── Error variants ────────────────────────────────────────────────────────────

/// All errors that can be produced at any stage of the pipeline.
#[derive(Debug)]
pub enum MetelError {
    ParseError {
        code: ParseErrorCode,
        message: String,
        /// Raw byte offsets from the pest span. Exposed via [`MetelError::primary_span`]
        /// for IDE/LSP span mapping (see RFC-0059).
        start: usize,
        end: usize,
        filename: String,
        line: u32,
        col: u32,
        /// Source line text, if available (from the pest grammar failure).
        source_line: Option<String>,
    },
    TypeError {
        code: TypeErrorCode,
        message: String,
        /// Raw byte offsets from the pest span. Exposed via [`MetelError::primary_span`]
        /// for IDE/LSP span mapping (see RFC-0059).
        start: usize,
        end: usize,
        filename: String,
        line: u32,
        col: u32,
    },
    RuntimePanic {
        code: RuntimeErrorCode,
        message: String,
        start: usize,
        end: usize,
        filename: String,
        line: u32,
        col: u32,
        /// Call stack at the point of the panic, innermost frame first.
        stack: Vec<FrameInfo>,
    },
    /// A bug in the interpreter or an unimplemented feature — never caused by user input.
    Internal {
        code: InternalErrorCode,
        message: String,
    },
}

impl std::fmt::Display for MetelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MetelError::ParseError {
                code,
                message,
                filename,
                line,
                col,
                source_line: None,
                ..
            } => write!(
                f,
                "[{code}] parse error in {filename}:{line}:{col}: {message}"
            ),
            MetelError::ParseError {
                code,
                message,
                filename,
                line,
                col,
                source_line: Some(src),
                ..
            } => write!(
                f,
                "[{code}] parse error in {filename}:{line}:{col} (`{src}`): {message}"
            ),
            MetelError::TypeError {
                code,
                message,
                filename,
                line,
                col,
                ..
            } => write!(
                f,
                "[{code}] type error in {filename}:{line}:{col}: {message}"
            ),
            MetelError::RuntimePanic {
                code,
                message,
                filename,
                line,
                col,
                stack,
                ..
            } => {
                write!(
                    f,
                    "[{code}] runtime error: {message}\n  at {filename}:{line}:{col}"
                )?;
                for frame in stack.iter().rev() {
                    write!(
                        f,
                        "\n  in {} at {}:{}:{}",
                        frame.fn_name,
                        frame.call_site.filename,
                        frame.call_site.line,
                        frame.call_site.col,
                    )?;
                }
                Ok(())
            }
            MetelError::Internal { code, message } => {
                write!(f, "[{code}] internal error: {message}")
            }
        }
    }
}

impl std::error::Error for MetelError {}

#[cfg(test)]
mod tests;

// ── Constructor helpers ───────────────────────────────────────────────────────

impl MetelError {
    pub fn parse(code: ParseErrorCode, msg: impl Into<String>, span: &Span) -> Self {
        Self::ParseError {
            code,
            message: msg.into(),
            start: span.start,
            end: span.end,
            filename: span.filename.clone(),
            line: span.line,
            col: span.col,
            source_line: None,
        }
    }

    pub fn type_error(code: TypeErrorCode, msg: impl Into<String>, span: &Span) -> Self {
        Self::TypeError {
            code,
            message: msg.into(),
            start: span.start,
            end: span.end,
            filename: span.filename.clone(),
            line: span.line,
            col: span.col,
        }
    }

    pub fn panic(code: RuntimeErrorCode, msg: impl Into<String>, span: &Span) -> Self {
        Self::RuntimePanic {
            code,
            message: msg.into(),
            start: span.start,
            end: span.end,
            filename: span.filename.clone(),
            line: span.line,
            col: span.col,
            stack: vec![],
        }
    }

    /// Attach a call stack to a `RuntimePanic`; no-op if already set or not a panic.
    #[must_use]
    pub fn with_stack(self, frames: Vec<FrameInfo>) -> Self {
        match self {
            Self::RuntimePanic {
                code,
                message,
                start,
                end,
                filename,
                line,
                col,
                stack,
            } if stack.is_empty() => Self::RuntimePanic {
                code,
                message,
                start,
                end,
                filename,
                line,
                col,
                stack: frames,
            },
            other => other,
        }
    }

    /// Interpreter bug — the typechecker should have prevented this state.
    pub fn internal(msg: impl Into<String>) -> Self {
        Self::Internal {
            code: InternalErrorCode::I0001,
            message: msg.into(),
        }
    }

    /// Feature not yet implemented in this version of the interpreter.
    pub fn not_implemented(msg: impl Into<String>) -> Self {
        Self::Internal {
            code: InternalErrorCode::I0002,
            message: msg.into(),
        }
    }

    /// The primary source span this error refers to, if it carries location data.
    ///
    /// Returns `None` for `Internal` errors, which are interpreter bugs not tied
    /// to a source location. Provides a uniform accessor over the per-variant
    /// `start`/`end`/`filename`/`line`/`col` fields so consumers (diagnostics,
    /// tooling) do not need to match every variant. See RFC-0059.
    #[must_use]
    pub fn primary_span(&self) -> Option<Span> {
        match self {
            Self::ParseError {
                start,
                end,
                filename,
                line,
                col,
                ..
            }
            | Self::TypeError {
                start,
                end,
                filename,
                line,
                col,
                ..
            }
            | Self::RuntimePanic {
                start,
                end,
                filename,
                line,
                col,
                ..
            } => Some(Span {
                start: *start,
                end: *end,
                filename: filename.clone(),
                line: *line,
                col: *col,
            }),
            Self::Internal { .. } => None,
        }
    }
}
