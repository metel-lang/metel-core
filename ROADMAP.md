# Roadmap

Planned work is organised by **theme**, not by version number. A version number is a
statement about what shipped, so it is chosen when a release is cut (`/cut-release`), by
the rule in `metel-docs-internal/internal/versioning.md`: a spec change needs at least a minor bump, a patch never
changes the language. Until then nothing refers to a future number.

## How milestones work

- **The lowest numbered milestone is the release in progress** (`vX.Y.Z`, horizon **now**). Its
  issues are what the next tag will contain; `/gap-analysis`, the integration session and
  `/cut-release` run on it.
- **While that is a patch, the next minor may also be numbered** (`vX.(Y+1).0`, horizon
  **next**), so it can be planned and analysed before the patch ships. Never two patches, two
  minors, or a numbered milestone beyond the next minor. The minor does not merge ahead of
  the patch: a patch never changes the language and is tagged from `develop`, so nothing
  language-visible from the minor merges to `develop`, and no docs change only the minor needs
  reaches the pinned docs commit, until the patch tag is pushed. Meanwhile: gap analysis,
  issue rewriting, RFC lifecycle changes, and branches and draft pull requests. When the patch
  is tagged the minor becomes the release in progress and its held pull requests merge.
- **A release may be staged.** A large release can be built from several stage milestones and still
  be one release. A stage is a theme (no version number) whose description has the line
  `Part of: vX.Y.Z` after its `Horizon:` line, then its outcome and exit test. The numbered milestone
  holds the release-level issues (decisions, reconciliation, tracking); the stages hold the
  implementation. The release in progress is the numbered milestone together with its stages:
  `/gap-analysis`, the integration session and `/cut-release` read the whole set, and the tag waits
  for all of it. A stage's title carries its release as a bracket tag, `[vX.Y.Z] Theme name`, so the
  milestone list shows which stage belongs to which release; the `Part of:` line stays the source of
  truth, and a stage that slips leaves the release when its `Part of:` line is deleted and the tag
  dropped from the title; it stays
  a theme. At the cut the stages are closed. Stages do not count toward the limit on numbered
  milestones. To list a release's open issues:

```bash
# the release milestone, then every stage that declares `Part of: vX.Y.Z` (ROADMAP.md)
gh issue list --milestone "vX.Y.Z" --state open
gh api repos/metel-lang/metel-core/milestones --paginate \
  | jq -r --arg v "vX.Y.Z" '.[] | select((.description // "") | split("\n") | map(rtrimstr("\r")) | any(. == "Part of: " + $v)) | .title' \
  | while IFS= read -r stage; do echo "== $stage"; gh issue list --milestone "$stage" --state open; done
```

- **Milestone order.** GitHub lists milestones by due date, so every milestone carries a placeholder
  due date that encodes only the order of this file: a release, then its stages, then the next
  release, the `next` themes, the `later` themes and the `parallel` themes. The dates are not
  deadlines; when the order changes, re-date the affected milestones to match.

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
- **Entering a release.** A bug moves from Backlog into a numbered milestone only when we
  commit to fixing it in that release. With a patch and a minor both numbered, it goes to the
  patch when the fix makes the implementation follow the unchanged spec (Release type, below);
  otherwise to the minor. A soundness bug or a regression introduced since the
  last tag is committed by default. Deferring one moves it back to Backlog, never to a theme.
- **Release type.** A fix can ship in a patch when it makes the implementation follow the
  unchanged spec, including when it changes which programs are accepted (a spurious rejection
  removed, or a program the spec forbids now rejected). A fix that needs a spec change, or where
  the spec is silent or contradicts itself, is not a bug fix: the spec question is decided first
  (an RFC where one is required) and the change ships in a minor.
- **Findings from `/milestone-integration-test`** are filed as bugs with a severity and go to
  Backlog, except soundness bugs and regressions, which go to the release in progress.

## Order

The numbered list is the priority order: each theme comes after the ones it lists in its
milestone description (`After:`). The tag is its horizon, how near it is.

1. **v0.16.0** [now]: One release, staged. The shape of the Copy/Clone model is decided (RFC-0162: an explicit `Clone` and a sealed `Copy` that brings a provided `Clone`, specified in RFC-0206 and settled against RFC-0089's multiplicity lattice (the class keywords `copy`, `affine`, `linear`; `linear` reserved), with RFC-0207's `derives` clause, RFC-0212's aspect properties, RFC-0213's super-aspects and RFC-0158 `Share` settled alongside it; RFC-0135 is refused) and its follow-ups are built. The numbered milestone holds the decisions and reconciliation; the stages (milestones that say `Part of: v0.16.0`) are, in order: Call and record syntax (first, added 2026-11-07: the `pub` spelling, RFC-0218; keyword arguments at every call, RFC-0223, and the constructor-syntax review (RFC-0100 reopened and its call implementation rolled back under #1945; replacement RFC-0226, #1944); dotted row labels, RFC-0221; initialization-only `:=`, RFC-0183; one-field record update, RFC-0191; per-label negative row bounds, RFC-0189), then Declarations and derivation (#1799 aspect identity, a behaviour-preserving refactor with no dependency, may start at once), Copy migration (structural kinds as std impls), and Copy and Clone in std. The surface stage goes first because it does not depend on the Copy/Clone model, so the model-defining stages that follow keep their review time (decided 2026-11-07). The Row machinery stage was emptied on 2026-11-06: RFC-0211 was split, its v0.16.0 rule is implemented in Declarations and derivation, and the row-template half (RFC-0217, with RFC-0209 and RFC-0210) moved to "Structural kinds after comptime".
2. **v0.16.1** [next]: Defect fixes that make the implementation follow the unchanged spec: generic bodies are checked and run on the facts of their definition (#1704, #1751, #1752, #1770), module-qualified paths are order-independent (#1769), literals in generic bodies are typed and range-checked (#1774), and the website flow diagrams are fixed (#1760). A patch: the spec does not change. It is a patch that ships after v0.16.0 (decided 2026-11-06).
3. **Linear types** [next]: The linear-type design (multiplicity, `Linear`, partial consumption) and its closure rules (RFC-0194: a closure that captures a linear value is linear) are settled, so exactly-once consumption is available to effects and capabilities.
4. **Drop and partial moves** [next]: Types with Drop run it in the right order and can be partially moved.
5. **Move check default-on** [next]: The move check runs by default on every program.
6. **Comptime** [next]: Comptime execution, comptime-known generic parameters and `comptime for` over a record's fields are settled and built, so fixed-size arrays and record `Clone` no longer need typechecker or native special cases.
7. **Structural kinds after comptime** [later]: Arrays, the native record `Clone` hook and the remaining structural kinds become std impls, so the compiler rules that v0.16.0 keeps for them are deleted.
8. **Abstract ownership solver** [later]: The hybrid end state of the Copy and Clone design: nominal types get stored ownership interfaces (explicit conditions first, then computed once per declaration by the obligation solver), generic bodies consult only stored interfaces, witnesses are carried to elaboration, and the v0.16.0 limitation (an undecided abstract ownership is a diagnostic in generic bodies) is lifted for what is proven. Epic #1821.
9. **Runtime value semantics** [next]: The evaluator stops deep-cloning and follows ownership.
10. **Reference rules (B0)** [next]: References are second-class under a minimal safe rule set.
11. **Borrow checking** [next]: Shared and exclusive borrowing, on by default from the first release, before the core surface freezes.
12. **Effects design settlement** [next]: Effect rows, markers, capability objects and handler control behaviour are settled as RFCs that share one calculus.
13. **Narrowed drop receivers** [next]: A `Drop` impl can take only the fields it needs (`&var self: Self.{ fd }`).
14. **Spec and audit hygiene** [next]: The spec claims only what the implementation does, before it freezes.
15. **Storage contract** [next]: The roles of `T[N]`, `T[]` and `List<T>` (inline fixed storage, borrowed contiguous view, owning runtime-sized buffer) are settled before the core surface freezes.
16. **Effect markers and capabilities** [later]: Effect rows are checked through functions, closures, generics and dispatch, native declarations in std carry checked effect metadata, and capability APIs pass authority explicitly.
17. **Algebraic effects** [later]: Handlers run with specified resumption, abandonment, borrowing and cleanup.
18. **Instance preparation** [later]: Frozen, monomorphized instances and an InstanceKey cache, with no run-time generic reconstruction.
19. **Core surface freeze** [later]: The core surface is frozen after effects validation and the storage contract, with user-declared `native`, the std API and slice validity rules not frozen; package design and a conformance corpus exist.
20. **Interop** [later]: User libraries declare native functions through a backend-neutral contract (which types cross, ownership at the call, errors, opaque handles, key checking), extending the effect metadata std natives already carry.
21. **Linear records** [later]: Per-field multiplicity and automatic downgrade are settled against the borrow and drop rules.
22. **Lifetimes and regions** [later]: Lifetime anchors / abstract regions allow stored references, including `T[]` slices (RFC-0124 slice half).
23. **Storage identity** [later]: Storage identity and brand types are settled.
24. **Compiled profile v0** [later]: A first program compiles end to end, including the compiled Godot bridge.
25. **Godot integration** [later]: Godot embeds Metel through the Interop contract, after the freeze.
26. **Allocator foundation** [later]: Allocator-selected handles and placement.
27. **Views and projections** [later]: Views and open projections work in every type position.
28. **Metel-backed List** [later]: A runtime-sized buffer.
29. **Tracing GC (experimental)** [later]: Local tracing GC.
30. **Compiler expansion** [later]: Broad end-to-end code generation.
31. **Compiler MVP** [later]: Standalone multi-module compilation.
32. **Standard library redesign** [later]: A usable, separately versioned std API.
33. **Concurrency** [later]: The concurrency model (RFC-0003) is settled.
34. **Copy migration** [stage of v0.16.0]: Hardcoded Copy/Clone rules for tuples and function types leave the typechecker and live in std.
35. **Standard library additions** [parallel]: Small std additions that do not wait on the redesign.
36. **Aspects and generics** [parallel]: Aspect system gaps: alias syntax, method constraints, where clauses, overlap, dyn Callable.
37. **Metaprogramming and derive** [parallel]: Type-as-value reflection, derive, attributes and auto-impl aspects designed and built on the comptime core.
38. **Records and surface syntax** [parallel]: Surface-syntax additions: conversions, unions, closure ergonomics, hoisting.
39. **Patterns and receivers** [parallel]: Destructuring assignment, field renaming, mutable-by-value receivers.
40. **Playground and interactive docs** [parallel]: Run Metel in the browser.
41. **Website content and experience** [parallel]: The website and tutorials are current.
42. **Docs and RFC tooling** [parallel]: The RFC and docs tooling is reliable.
43. **Engineering hygiene** [parallel]: Small repo-hygiene and lint debt.

Dependencies behind this order:

- Move check default-on waits on the Copy decisions of #741, settled in v0.16.0, which stay on the critical path. Copy migration also waits on them and is a stage of v0.16.0, so it ships in the same release.
- Comptime design settlement runs alongside the Copy decisions, Drop and Move check, and its implementation follows Move check default-on: RFC-0132 (execution model and comptime-known generic parameters) first, then RFC-0174 (`comptime for`). Structural kinds after comptime consumes it: `[T; N]: Copy` cannot leave the typechecker without RFC-0132 §3 (the array half of #263, now #1811), and the native record `Clone` hook (#1390) waits on RFC-0174. v0.16.0 keeps arrays and that hook as named compiler rules, which that theme deletes. The rest of metaprogramming (type-as-value, `typeinfo` and `emit`, derive, attributes, auto-impl) stays parallel.
- Linear types follows the Copy decisions of v0.16.0. It is design settlement only (RFC-0089, then RFC-0194 on linear closures and captures, which needs RFC-0089 and function types satisfying `Linear` via the auto-impl mechanism, #739); implementation follows Drop and partial moves. Linear records (RFC-0091) also waits on Borrow checking (its open question is the type of a borrow taken before a downgrade) and on Narrowed drop receivers.
- Runtime value semantics (#277) starts once move checking is default-on and coordinates with Drop; it does not wait behind Allocator foundation.
- Borrow checking (RFC-0122) is before the core-surface freeze, and Lifetimes and regions follow it.
- Effects design settlement draws on Linear types (exactly-once consumption, one-shot resumption) and the Copy decisions (callable multiplicity). It overlaps the ownership implementation themes; its exit is a set of accepted RFCs, and no effects implementation starts before them.
- Effect markers and capabilities covers the `native` declarations std already has: each carries checked effect metadata, so a native cannot silently erase an effect. Interop extends that to user-declared natives after the freeze.
- The core-surface freeze (#1358) waits for Algebraic effects, so the model is validated by a working implementation before it freezes. The freeze covers std's own `native` bindings; user-declared `native` and the std API are not frozen. Interop (#1344, #1355) follows the freeze as an additive surface, and the Godot prototype follows Interop.
- Storage contract (#1292, with the `T[]` nominal question #1123) is settled before the freeze: it fixes the roles of `T[N]`, `T[]` and `List<T>` and promises no allocation or interpreter fallback in compiled programs. It coordinates RFC-0053, RFC-0124, RFC-0126 and RFC-0133, and its sized-array half uses Comptime (RFC-0132 §3). The slice half of RFC-0124 (#932) waits on the lifetime-anchor design and moves to Lifetimes and regions, so slice validity rules are not frozen; `List<T>` itself (#276) stays behind Allocator foundation.
- Allocator foundation needs Borrow checking, Lifetimes and regions, and Storage identity.
- Parallel themes are off the critical path and can be taken whenever their prerequisites are met.

## Unscheduled design work

Draft RFCs with no tracking issue. They are listed here so they are not lost; each gets a tracker in its theme when the RFC is committed to a release (RFC process). The home is a proposal, not a commitment, and a draft that is stale is refused in the draft-RFC cleanup (#1671).

- **Aspects and generics**
  - RFC-0011: Operator Overloading Aspects
  - RFC-0062: Ord / Eq Comparison Aspects
  - RFC-0168: Equality Model and Super-Aspects
  - RFC-0176: Hash Aspect and Structural Hashing
  - RFC-0038: impl Aspect in Struct Fields and Existential Types
  - RFC-0104: Multi-Aspect Extend Blocks with Shared Bodies
  - RFC-0105: Struct-Embedded Aspect Lists
  - RFC-0114: Constructor Aspect and Canonical Construction
  - RFC-0128: Exportable overload sets and shadow-versus-extend semantics
- **Records and surface syntax** (RFC-0100, RFC-0183, RFC-0189, RFC-0191, RFC-0221 and RFC-0223 moved to the v0.16.0 stage "Call and record syntax" on 2026-11-07; the rest stay in this theme)
  - RFC-0151: Tuples as Numeric-Label Rows
  - RFC-0170: Literal Types and Discriminated Structural Unions
  - RFC-0175: Label Polymorphism
  - RFC-0188: Label syntax
  - RFC-0033: Field-Level Mutability
  - RFC-0015: Unwrap Syntax
  - RFC-0004: main() return type — should main return Result instead of ()?
  - RFC-0005: Warn on unreachable match arms
  - RFC-0101: Grammar-Enforced Naming Case Conventions
- **Interop**
  - RFC-0027: C FFI
  - RFC-0026: Unsafe Blocks
- **Allocator foundation, Lifetimes and regions**
  - RFC-0074: Shared Pointers — Rc and Arc
  - RFC-0075: Region Inference — Local AutoRegion
  - RFC-0145: Static Storage Duration
- **Storage contract**
  - RFC-0172: Sized and Unsized Kinds, and a Generalized Unsizing Coercion
- **Effects design settlement and Linear types (closures)**
  - RFC-0014: Panic Recovery
  - RFC-0164: Mutating Closures with a Propagating ? Are Call-Once
- **No theme yet**
  - RFC-0017: Language Edition System

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
| Language expansion | Aspects and generics, Comptime, Metaprogramming and derive, Records and surface syntax, Concurrency, Linear types, Linear records, Effects design settlement |
| Website, docs and project | Playground and interactive docs, Website content and experience, Docs and RFC tooling, Engineering hygiene, Standard library additions |

### Regrouping of 2026-10-29

Effects became a main track before the core-surface freeze; linear types moved up behind Copy/Clone settlement. Three themes were split.

| Before | Now |
|---|---|
| Concurrency, effects and linear types | Concurrency, Linear types, Linear records, Effects design settlement |
| Native contract | Interop |
| Compiler-ready pipeline | Instance preparation, Core surface freeze |
| Metaprogramming and derive | Comptime, Metaprogramming and derive |

Storage contract moved before the core-surface freeze; its slice half (#932) moves to Lifetimes and regions. New: Effect markers and capabilities, Algebraic effects. Comptime is a main track (RFC-0132 and RFC-0174 first; #1390 is its first consumer). Runtime value semantics moved up to follow Linear types. Copy/Clone settlement stays on the critical path; Copy migration became a parallel theme.
