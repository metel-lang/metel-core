<p align="center">
  <img src="media/metel-logo-dark.svg" alt="Metel" width="600"/>
</p>

A statically-typed language exploring what happens when ownership, structural typing,
and a real aspect system are designed in together instead of bolted on.

## Why

You surely know as well as I do that the world does not need another amateur language,
so the honest reason is: I wanted to build one. It started as a small, Rust-influenced
tree-walk interpreter and grew into something with a two-pass Hindley-Milner type
checker, affine-by-default ownership with a real move checker, an aspect system
standing in for traits, and structural records living alongside nominal structs.

It's a personal project — there is no team, no company, and no roadmap beyond my own
curiosity about whether these ideas hold together once they collide with generics,
closures, and real programs. It's heavily AI-assisted: most of the implementation was
built with a lot of help from AI tools, with the design work reviewed and curated in
detail rather than accepted wholesale. Read more about how it started, and where it's
headed, in [Introducing Metel](https://metel-lang.org/blog/introducing-metel).

## What it can do today

**Ownership is affine by default.** A non-`Copy` value has exactly one owner; moving it
invalidates the source, checked statically with `--move-check`. `Copy` and `Drop` are
opt-in aspects, mutually exclusive by construction. References (`&T`, `&var T`) are
explicit aliases with auto-deref through field access and method calls, and reading a
`Copy` value back out of a reference ("read-copy") is the only implicit duplication
allowed.

**Aspects stand in for interfaces.** `aspect Name { fun method(&self) -> T; }` declares
a capability; `extend Type: Aspect { ... }` implements it, with default methods,
negative bounds (`T: !Aspect`), associated types, and coherence checking to keep two
conflicting implementations of the same aspect for the same type from compiling.

```metel
aspect Greet {
    fun greet(&self) -> String;
}

struct Person { name: String }

extend Person: Greet {
    fun greet(&self) -> String { "Hello, ${self.name}!" }
}

extend Person {
    fun rename(&var self, new_name: String) { self.name := new_name; }
}

fun greet_all<T: Greet>(people: [T]) {
    for (p in people) { println(p.greet()); }
}

fun main() -> i64 {
    var ada := Person { name = "Ada" };
    let ada_ref: &var Person := &var ada;
    ada_ref.rename("Ada Lovelace");   // auto-deref through &var — writes back to ada

    greet_all([ada, Person { name = "Grace" }]);
    return 0;
}
```

**Records are the structural counterpart to structs.** `{ x: f64, y: f64 }` is a type
with no declaration site — two unrelated pieces of code that write the same shape are
talking about the same type. A row bound constrains a generic parameter by the fields
it carries rather than by an aspect it implements:

```metel
fun magnitude<record T: { x: f64, y: f64, .. }>(p: T) -> f64 {
    return p.x * p.x + p.y * p.y;
}

fun main() {
    println(magnitude({ x = 3.0, y = 4.0 }));   // 25
}
```

**Algebraic data types and exhaustive pattern matching:**

```metel
enum Shape {
    Circle { radius: f64 },
    Rectangle { width: f64, height: f64 },
}

fun area(s: Shape) -> f64 {
    match s {
        Shape::Circle { radius }           => 3.14159 * radius * radius,
        Shape::Rectangle { width, height } => width * height,
    }
}
```

**Explicit error handling**, with `?`-propagation and automatic coercion between error
types via `From`:

```metel
struct IoError { msg: String }
struct AppError { msg: String }

extend AppError: From<IoError> {
    fun from(value: IoError) -> AppError {
        return AppError { msg = "io: ${value.msg}" };
    }
}

fun load() -> Result<String, IoError> {
    return Result::Err { error = IoError { msg = "disk full" } };
}

fun load_config() -> Result<String, AppError> {
    let data := load()?;   // IoError coerced to AppError via From
    return Result::Ok { value = data };
}
```

Also: generics with full monomorphization, a module system (`import`/`export`, `pub`
visibility), `Perhaps<T>` instead of null, string interpolation, and a growing standard
library (`List<T>`, `String`, host-backed `fs`/`env`/`process` modules).

## What's next

**Short term:** field-sensitive access into records (reading an unnamed field of an
open row bound), and closing the remaining gaps `--move-check` doesn't cover by
default yet.

**Medium term:** a borrow checker (tracking what's currently borrowed, not just what's
been moved), allocators and lifetime anchors as an explicit, program-visible storage
model, and linear types as a stricter opt-in layer above the affine default
(use-*exactly*-once, not just at-most-once).

**Further out:** compile-time execution (`comptime`) staged by the same evaluator
rather than a separate macro language, and fiber-based concurrency with typed channels
— no `async`/`await`, no function coloring.

All of this is designed in the open — see the [RFC process](docs/rfcs/) for the
proposals, the arguments for and against, and the decisions as they're made.

## Quick Start

### Prerequisites

- Rust 1.70+
- Cargo

### Build

```bash
cargo build --release --workspace
```

### Run a Program

```bash
cargo run --release -- path/to/program.mtl
```

Pass `--move-check` to additionally reject use-after-move and moving a value out of a
reference — off by default while the existing corpus finishes migrating to the style
affine ownership expects.

### Run Tests

```bash
cargo test --release --workspace
```

## Project Structure

```
metel-core/
├── metel-frontend/        # Parsing through typechecking; produces a typed AST
│   └── src/
│       ├── parser/        # PEG grammar (pest) → untyped AST
│       ├── ast/           # Untyped AST node definitions
│       ├── typeinference/ # Hindley-Milner constraint solver
│       ├── typechecker/   # Two-pass type checker (inference, then construction)
│       ├── typed_ast/     # Typed AST node definitions
│       ├── move_check/    # Opt-in affine-ownership checker
│       ├── coherence.rs   # Aspect-impl overlap/orphan checking
│       └── elaborator/    # Resolves method dispatch ahead of evaluation
│
├── metel-interpreter/     # Runtime
│   └── src/
│       ├── evaluator/     # Tree-walking evaluator
│       ├── pipeline.rs    # Wires parsing → typechecking → elaboration → evaluation
│       └── main.rs        # CLI entry point
│
└── docs/                  # Submodule: spec, RFCs, changelog, decision records
```

## Resources

- **Website:** [metel-lang.org](https://metel-lang.org)
- **Language Specification:** [`docs/reference/spec/`](docs/reference/spec/)
- **RFCs:** [`docs/rfcs/`](docs/rfcs/) — every language design decision,
  public at every stage
- **Changelog:** [`docs/release-notes/changelog.md`](docs/release-notes/changelog.md)
- **Introducing Metel:** [the blog post](https://metel-lang.org/blog/introducing-metel)
  on why this exists and where it's headed
- **Architecture:** [`docs/architecture/architecture.md`](docs/architecture/architecture.md)
  — moved here from `metel-docs-internal` (ADR-0051, amended 2026-08-23), plus
  `typechecker.md`/`evaluator.md` in each crate's own `docs/`
- **Decision Records:** [`docs/architecture/decisions/`](docs/architecture/decisions/)
  — why past decisions were made, and why some were reversed
- **Scripts and CI:** [`PROCESSES.md`](PROCESSES.md) — every script and CI workflow
  across this repo, `metel-docs`, `metel-docs-internal`, and `metel-website`: what
  runs, what triggers it, and which repo owns which secret

## License

Metel is licensed under the Apache License 2.0. See [LICENSE](LICENSE) for details.
