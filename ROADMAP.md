# Roadmap

Planned work is organised by **theme**, not by version number. A version number is a
statement about what shipped, so it is chosen when a release is cut (`/cut-release`), by
the rule in `metel-docs-internal/internal/versioning.md`: a spec change needs at least a minor bump, a patch never
changes the language. Until then nothing refers to a future number.

## How milestones work

- **One numbered milestone is the release in progress** (`vX.Y.Z`, horizon **now**). Its
  issues are what the next tag will contain; `/gap-analysis`, the integration session and
  `/cut-release` run on it.
- **Every other milestone is a theme**, named for the capability it delivers and carrying no
  version number. The first line of its description is `Horizon: next`, `later` or
  `parallel`, then the outcome, the exit test (`Exit:`), what it must come `After:`, and
  what it was `Formerly:`. `parallel` is work off the critical path (website, documentation,
  project, and language additions with no ordering constraint): it can be taken whenever its
  listed prerequisites are met.
- **A theme is coherent.** It has one outcome in a sentence, an exit test, and every issue in
  it is a necessary step to that outcome. An issue that is not goes to its nearest theme, to
  Backlog if it is a bug, or stays without a milestone (with `needs-design` or
  `rfc-tracking`) until it has a home.
- **Promotion.** When a release is cut, pick the theme(s) that follow, choose the version
  by the versioning rule, and **rename the theme milestone to that version** (renaming keeps
  its issues and links). A theme can also be split: move its issues into the numbered
  milestone and keep the rest as a theme.
- **Re-planning is free.** Moving an issue between themes, merging or reordering themes does
  not rename anything that was ever published. Order lives in this file; the horizon in each
  description says how near it is.
- **Referring to the future.** Issues, RFC `target` fields, spec availability notes, the
  blog and release notes say *planned*, or name the theme. They never name a version that
  has not been cut. A shipped feature gets its real version (`Since v0.14.0`).

## Bugs

Bugs are not planned work, so they are not scheduled into themes.

- **What counts.** A bug is observable behaviour that contradicts the spec or a documented
  guarantee: a wrong result, a program accepted that should be rejected (or the reverse), an
  internal error (`I00xx`), a crash, or a wrong diagnostic. A known, intentional limitation
  or a not-yet-built feature is a feature, not a bug; limitations ship as limitation
  records with the issue linked. Defects in tooling (CI, doc checkers, release scripts) are
  bugs too and also carry `tooling`.
- **Where they live.** Every bug carries the `bug` label and one severity label, and sits in
  the **Backlog** milestone. Backlog is never promoted or renamed. A bug is not placed in a
  theme.
- **Severity.**
  - `severity:soundness`: accepts a program that breaks a language guarantee (type,
    ownership, memory safety). Blocks the next release wherever it is found.
  - `severity:incorrect`: wrong result, crash, internal error, or a spurious rejection.
  - `severity:diagnostic`: wrong or misleading message only; the behaviour is right.
- **Regressions.** A bug that worked in an earlier tag also carries `regression`, and is
  fixed ahead of other bugs of the same severity.
- **Entering a release.** A bug moves from Backlog into the numbered milestone only when we
  commit to fixing it in that release. A soundness bug or a regression introduced since the
  last tag is committed by default. Deferring one moves it back to Backlog, never to a theme.
- **Release type.** A fix that changes only diagnostics or internals can ship in a patch. A
  fix that changes which programs are accepted is language-visible and follows the versioning
  rule above.
- **Findings from `/milestone-integration-test`** are filed as bugs with a severity and go to
  Backlog, except soundness bugs and regressions, which go to the numbered milestone.

## Order

The numbered list is the priority order: each theme comes after the ones it lists in its
milestone description (`After:`). The tag is its horizon, how near it is.

1. **v0.14.1** [now]: CI and documentation tooling stop failing for unrelated reasons; the pending-marker process exists.
2. **Copy/Clone settlement** [next]: The Copy/Clone model is decided, so ownership work has a stable target.
3. **Drop and partial moves** [next]: Types with Drop run it in the right order and can be partially moved.
4. **Move check default-on** [next]: The move check runs by default on every program.
5. **Copy migration** [next]: Hardcoded Copy/Clone rules leave the typechecker and live in std.
6. **Reference rules (B0)** [next]: References are second-class under a minimal safe rule set.
7. **Borrow checking** [next]: Shared and exclusive borrowing, on by default from the first release, before the core surface freezes.
8. **Native contract** [next]: User libraries declare native functions through a backend-neutral contract.
9. **Narrowed drop receivers** [next]: A `Drop` impl can take only the fields it needs (`&var self: Self.{ fd }`).
10. **Spec and audit hygiene** [next]: The spec claims only what the implementation does, before it freezes.
11. **Compiler-ready pipeline** [later]: Frozen, monomorphized instances, a frozen core surface and package design.
12. **Lifetimes and regions** [later]: Lifetime anchors / abstract regions allow stored references.
13. **Storage identity** [later]: Storage identity and brand types are settled.
14. **Storage contract** [later]: Arrays, slices and List have one documented storage contract.
15. **Compiled profile v0** [later]: A first program compiles end to end, including the compiled Godot bridge.
16. **Godot integration** [later]: Godot embeds Metel through the native contract.
17. **Allocator foundation** [later]: Allocator-selected handles and placement.
18. **Runtime value semantics** [later]: The evaluator stops deep-cloning and follows ownership.
19. **Views and projections** [later]: Views and open projections work in every type position.
20. **Metel-backed List** [later]: A runtime-sized buffer.
21. **Tracing GC (experimental)** [later]: Local tracing GC.
22. **Compiler expansion** [later]: Broad end-to-end code generation.
23. **Compiler MVP** [later]: Standalone multi-module compilation.
24. **Standard library redesign** [later]: A usable, separately versioned std API.
25. **Standard library additions** [parallel]: Small std additions that do not wait on the redesign.
26. **Aspects and generics** [parallel]: Aspect system gaps: alias syntax, method constraints, where clauses, overlap, dyn Callable.
27. **Metaprogramming and derive** [parallel]: Derive, comptime and attributes designed and built.
28. **Records and surface syntax** [parallel]: Surface-syntax additions: conversions, unions, closure ergonomics, hoisting.
29. **Patterns and receivers** [parallel]: Destructuring assignment, field renaming, mutable-by-value receivers.
30. **Concurrency, effects and linear types** [later]: Long-range design settlements.
31. **Playground and interactive docs** [parallel]: Run Metel in the browser.
32. **Website content and experience** [parallel]: The website and tutorials are current.
33. **Docs and RFC tooling** [parallel]: The RFC and docs tooling is reliable.
34. **Engineering hygiene** [parallel]: Small repo-hygiene and lint debt.

Dependencies behind this order:

- Move check default-on and Copy migration wait on Copy/Clone settlement (#741).
- Borrow checking (RFC-0122) is before the core-surface freeze, and Lifetimes and regions follow it.
- Allocator foundation needs Borrow checking, Lifetimes and regions, and Storage identity.
- Native declarations are part of the frozen core surface (#1358), so Native contract and Narrowed drop receivers precede the freeze; the Godot prototype follows it.
- Parallel themes are off the critical path and can be taken whenever their prerequisites are met.

## Retired numbering

The numbers below were used before 2026-10-19. They appear in older issues, RFCs and
release notes; read them through this table. On 2026-10-20 the mixed theme milestones were
regrouped (below); a number in an issue body names the old grouping, so the issue's current
milestone is authoritative.

| Old | Theme |
|---|---|
| v0.14.2 | Website, docs and project |
| v0.14.3 | Copy/Clone settlement |
| v0.15.0 | Ownership core |
| v0.16.0 | Ownership on by default |
| v0.17.0 | Compiler-ready pipeline |
| v0.18.0 | Compiled profile v0 |
| v0.18.1 | Ownership extensions and views |
| v0.19.0 | Borrow checking |
| v0.19.1 | Lifetimes and abstract regions |
| v0.20.0 | Storage identity |
| v0.21.0 | Allocator foundation |
| v0.21.1 | Language expansion |
| v0.22.0 | Metel-backed List |
| v0.23.0 | Tracing GC (experimental) |
| v0.24.0 | Compiler expansion |
| v0.25.0 | Compiler MVP |

### Old themes after the regrouping

| Old theme | Now |
|---|---|
| Ownership core | Drop and partial moves, Copy migration, Storage contract, Runtime value semantics, Aspects and generics, Standard library additions |
| Ownership on by default | Move check default-on, Reference rules (B0), Borrow checking, Native contract, Narrowed drop receivers, Spec and audit hygiene, Patterns and receivers |
| Ownership extensions and views | Views and projections, Narrowed drop receivers |
| Borrow checking, Lifetimes and abstract regions | Borrow checking, Lifetimes and regions |
| Compiler-ready pipeline | Compiler-ready pipeline, Godot integration |
| Language expansion | Aspects and generics, Metaprogramming and derive, Records and surface syntax, Concurrency effects and linear types |
| Website, docs and project | Playground and interactive docs, Website content and experience, Docs and RFC tooling, Engineering hygiene, Standard library additions |
