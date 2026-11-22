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
  be one release. A stage is a theme (no version number) with a `[vX.Y.Z] Theme name` title. The
  numbered milestone holds the release-level issues (decisions, reconciliation, tracking); the stages
  hold the work. The release in progress is the numbered milestone together with its stages, and the
  tag waits for all of them. Stages do not count toward the limit on numbered milestones.
- **A stage is linked to its release in both directions.** The stage's description has the line
  `Part of: vX.Y.Z` after its `Horizon:` line, then its outcome and exit test. The release's
  description has a `Stages:` block after its outcome, one `- [vX.Y.Z] Theme name` per line, in the order
  the stages are meant to finish. A stage that cannot finish before another has a `Needs: <name>; <name>`
  line after `Part of:` (stage names without the tag), and the `Stages:` order must put it after the
  stages it needs; the milestone due dates follow the same order. A need is a hard dependency or a
  sequencing constraint, not a coordination (two stages that must agree on a design but can run in
  parallel do not need each other). A registry feature a stage delivers carries that stage's name in its
  `stage` field (`tools/feature-matrix/registry.toml`). `tools/release_stages.py` is the one reader of
  all this, and `/gap-analysis`, `/stage-gate`, the integration session and `/cut-release` call it:

  ```bash
  tools/release_stages.py list  vX.Y.Z           # the stages in order: state, open issues, gate report
  tools/release_stages.py open  vX.Y.Z           # the open issues of the release and of every stage
  tools/release_stages.py check vX.Y.Z           # the two links agree, titles are tagged, due dates and Needs: are in order
  ```

- **A stage is gated when it completes.** The gates are not saved for the end. When a stage's issues
  are closed, `/stage-gate vX.Y.Z "<stage>"` checks its exit test, repository-wide bugs, the feature
  matrix for the stage together with the stages already gated (a stage gate is cumulative, so a later
  stage's unfinished features never block it), the full test suite on `develop`, and the lifecycle of
  its RFCs, and commits a report. A stage that passes is closed, and a closed stage is a gated stage;
  one that does not stays open, and the release does not move past it. Stages are gated in the order
  they finish, not the order they were planned. `/gap-analysis` runs at the start of a stage the same
  way it runs at the start of a release.
- **The cut then has little left to find.** `/cut-release` requires every stage closed with a passing
  report (`tools/release_stages.py check vX.Y.Z --gated`), then runs the integration session once more
  over the whole release on the frozen tree. That run is the only place the pairs that span two
  stages are first exercised together, so a stage gate does not replace it. A stage that has not
  been gated can slip: delete its `Part of:` line, remove it from the `Stages:` list, drop the tag from
  its title, and move its registry features to the release they will ship in; it stays a theme. A gated
  stage's work is already on `develop`, so it stays in the release.

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

## Architecture

The surface language evolves independently of compiler implementation. The frontend elaborates supported constructs into an explicitly typed, ownership-aware Metel-Core, and the interpreter, the Core evaluator and the compiler target progressively larger subsets of it (RFC-0241 section 7). Core is one datatype with two phases, before and after ownership elaboration, and it contains no layout, calling-convention or SSA concepts. An execution IR for the compiler is a separate representation, built when a trigger requires it: drop flags with early exits, alias facts, effects lowering, an optimizer, or a second backend. The first backend is LLVM. Compiling does not wait on a language-wide freeze: each supported Core subset has its own correctness and execution contract, and the Stability commitment is a user-facing gate, not a compiler prerequisite.

Borrow safety is staged. B0 restricts references to parameters and block-scoped locals. B1 (Basic borrow-conflict checking) enforces many readers or one writer on that subset by default and makes no general memory-safety claim. B2 (Full Core borrow verification) adds origins, stored and returned references and the rest, and only then is general static memory safety claimed. What B1 accepts as stable, B2 accepts too. A compiled profile never relies on guarantees nothing has proved: no aliasing attributes, fast-math or overflow flags without a justification.

Memory and identity: borrow origins describe reference dependencies, row-polymorphic views describe structural access, and rigid generative brands distinguish authority domains. A universal allocator storage-identity kind (`@s`) and `T@a` placement are not part of the target design (decided 2026-11-20); the RFC reconciliation is tracked in Memory model settlement. A panic is a non-resumable effect handled by effect handlers and arrives with algebraic effects; Drop runs during recovery, and an unhandled panic exits immediately.

## Order

The numbered list is the priority order: each theme comes after the ones it lists in its
milestone description (`After:`). The first tag is its horizon, how near it is.

**Lanes.** The list is one priority order, but its themes are of two kinds. Most form the
*implementation lane*, a chain in which each theme is built after the ones it lists in `After:`.
The chain has three threads that share little code: ownership and safety (Drop and partial moves, Move check default-on,
Reference rules (B0), Basic borrow-conflict checking (B1), then Ownership-explicit core jointly with the compiler thread);
numeric (Numeric and operator model); and compiler (Core representation, Comptime, Instance preparation, Compiled kernel
experiment). They meet at the operand-mode decision, where an operator takes non-`Copy` operands, and at Ownership-explicit
core (decided 2026-11-19 and 2026-11-20).
A theme tagged `design lane` ends in accepted RFCs, not code; a theme tagged `settlement in design
lane` ends in an implementation but its RFCs can be settled earlier. Design-lane settlement starts
as soon as its *design* prerequisites are met and runs alongside the implementation chain; it does
not wait for the implementation themes listed before it, and its implementation then joins the
chain at its numbered position. Added 2026-11-19 (RFC-0241, #2095); until then the same overlap
was written into individual milestone descriptions ("design settlement can start during ...").

1. **v0.16.1** [now]: Defect fixes that make the implementation follow the unchanged spec: generic bodies are checked and run on the facts of their definition (#1704, #1751, #1752, #1770), module-qualified paths are order-independent (#1769), literals in generic bodies are typed and range-checked (#1774), and the website flow diagrams are fixed (#1760). A patch: the spec does not change. It is a patch that ships after v0.16.0 (decided 2026-11-06).
2. **v0.17.0** [next, staged release]: A large release of ten stages, each gated when it completes (`/stage-gate`, tracker #2132; the stages are listed in the release milestone). Effects and named records are the top priority, the rest is what they rest on. Nothing language-visible merges to `develop` until v0.16.1 is tagged; until then the work is RFC settlement and draft pull requests. In dependency order (each stage lists the stages it needs; `tools/release_stages.py check` fails on an order that breaks them):
   1. **Row visibility and named records** [stage, design then implementation]: Whether a struct's row is visible to structural matching follows field visibility, and the named record kind is retired or kept (RFC-0209, then RFC-0243); the decision is implemented.
   2. **Function types** [stage]: A written function type is a regular type, `dyn Callable` with marker aspects, and `once`, `var` and `copy` are markers (RFC-0161 Phase A, RFC-0232, RFC-0155, RFC-0163). The marker set is open so effect rows use the same mechanism, and function types satisfy `Linear` through the auto-impl mechanism.
   3. **Unconditional derivation** [stage, design then implementation]: A `derives` entry with no arguments is unconditional and `?` asks the compiler to compute the condition from the fields; `copy` is `derives Clone, Copy`, `copy?` its computed form, and the `copy(T)` and `copy()` forms are removed (RFC-0244, tracker #2150; amends RFC-0227, RFC-0239, RFC-0234, RFC-0207 and RFC-0224, with RFC-0238 taking the same default). Before Linear types because the `linear` class keyword shares its grammar rule, and coordinated with Row visibility and named records, whose option O4 uses `derives` as its vehicle.
   4. **Drop and partial moves** [stage]: Types with Drop run it in the right order and can be partially moved. Drop is inert today, so this stage makes it run, for normal and early exits, with cleanup paths and drop flags shaped so panic recovery can be added. What Drop does on a recovered panic is specified by RFC-0014 in Effects design settlement and takes effect with Algebraic effects, which are not in this release; an unhandled panic exits without running Drop. Before Linear types, because linear-type implementation follows it.
   5. **Linear types** [stage, design then implementation]: The linear-type design (multiplicity, `Linear`, partial consumption, linear closures and captures, the rule under panic and handler abandonment: a linear value has no implicit drop, reconciled with RFC-0014 in Effects design settlement) is settled and implemented (RFC-0089, RFC-0194, RFC-0215, RFC-0220).
   6. **Narrowed drop receivers** [stage, design then implementation]: A `Drop` impl can take only the fields it needs (`&var self: Self.{ fd }`), so a type with a `Drop` impl can be partially moved and its residual dropped, with row-bounded Drop dispatch against a narrowed residual (RFC-0109, RFC-0147, #949). No narrowed receiver exists today. After Drop and partial moves, and after Row visibility and named records, because RFC-0109's open opacity question is RFC-0243's V2. Until it lands, moving out of a field of a type with a `Drop` impl stays rejected.
   7. **Effects design settlement** [stage, design lane]: Effect rows, markers, capability objects and handler control behaviour are settled as RFCs that share one calculus. Also decides panic recovery (RFC-0014, RFC-0164): a panic is a non-resumable effect with handlers, arriving with effects; Drop runs during recovery; `Panic` is ambient in v0.17.0 as the working position (2026-11-22, #2121; RFC-0245 leaves open whether it is ambient or tracked in rows) and a no-panic guarantee is available where asked (working name `NoPanic`; whether it is spelled as a marker or as the negative entry `!.Panic` is decided in #1672). The surface is the keywords `effect` and `effects`, not RFC-0140's `^`. Reconciles the panic clauses of Drop and partial moves and of Linear types (neither waits on it). The dependency audit of RFC-0140 is done (#2139); the first task is the row-calculus RFC (#1672), at full scope.
   8. **Effect rows and markers** [stage]: The first slice of Effect markers and capabilities: rows and markers are checked through functions, closures, generics and dispatch, and std `native` declarations carry checked effect metadata (markers only, on the working position that `Panic` is ambient). It also defines and checks the no-panic guarantee (working name `NoPanic`, #2163), and implements the row binder `<..R>` of RFC-0208 (#1789, #2167, moved here from Views and row-polymorphic borrowing): an effect row is not a value, so a row parameter must stand only for a row, and `record E` would let it be used as a type. Known limit, accepted 2026-11-22: it ships without useful integer arithmetic, because plain integer arithmetic is unavailable in such a body until checked arithmetic (RFC-0142, #841, not in this release) exists. It waits on the row-calculus RFC (#1672) and Function types, not on capability objects, restricted interpolation or the rest of RFC-0140's reconciliation. Handlers and resumption are not in this release.
   9. **Pipelines** [stage]: `x |> f(a)` and hole sections lower to ordinary calls and closures (RFC-0204, RFC-0205). `.then`, operator functions and the composition operator are not in this release.
   10. **Metel-Core and MIR design** [stage, design only]: The design of Metel-Core and of the low-level IR (MIR) is settled as integrated RFCs and an ADR, with no compiler code (RFC-0241 split into direction, Core IR and MIR contract; its open questions 25 to 34 resolved or deferred). Finalized last: it waits on Row visibility and named records, Effects design settlement and Function types.

   If the release must shrink, stages slip in this order: Pipelines, then the implementation half of Row visibility and named records (the design stays), then Effect rows and markers. A stage that has passed its gate cannot slip.
3. **Surface settlement** [next, design lane]: The surface forms that must stop changing before the stability commitment are decided: `let` and `var` hoisting (RFC-0131), module layout (RFC-0099 and the `mod.mtl` question) and the overload-resolution rules (#2112). The named record kind (RFC-0243, RFC-0209) and function types (RFC-0232) are settled in v0.17.0 stages. Implementation of each decision goes to the parallel surface themes.
4. **Storage contract** [next, design lane]: The roles of `T[N]`, `T[]` and `List<T>` (inline fixed storage, borrowed contiguous view, owning runtime-sized buffer) are settled before the stability commitment. The same settlement covers text: `String`, a borrowed `&str` view and the type of a string literal (#2113), which must be decided before Move check default-on completes.
5. **Memory model settlement** [next, design lane]: The memory and identity model is settled as RFCs: origins, rigid brands, privileged std reference types, typed handles and custody, without a universal storage-identity kind (`@s` dropped, decided 2026-11-20). Tracker #2116.
6. **Core representation** [next]: Metel-Core exists as the compiler's typed representation (L2 of RFC-0241 section 7): lowered from the typed AST, checked by a well-formedness lint, and run by a reference evaluator that agrees with the tree-walking interpreter on the whole fixture corpus and follows ownership by construction. The same evaluator is the execution model Comptime needs. Core has two phases (before and after ownership elaboration) and no layout or ABI concepts; the shape of generics in Core is left open (RFC-0241 open question 25) and the first lowering emits monomorphic instances only. Thread C of the implementation lane, not waiting on move-check default-on. It is the implementation of the design the v0.17.0 stage Metel-Core and MIR design settles, and starts when that is integrated. The design tracker is #2095.
7. **Numeric and operator model** [next]: Scalar types, the equality and ordering aspects and the operators are std aspects with native scalar bodies, so `1 + 2`, `a < b` and `x?` dispatch through aspects, and f32 and f64 follow IEEE 754. The second implementation thread; it is the release after v0.17.0 (decided 2026-11-22), and meets Move check default-on at the operand modes.
8. **Move check default-on** [next]: The move check runs by default on every program. It waits on the string-literal decision in Storage contract and on the operand modes in Numeric and operator model. The interpreter stops deep-cloning (#277, moved here from Core representation on 2026-11-20).
9. **Comptime** [next]: Comptime execution, comptime-known generic parameters and `comptime for` over a record's fields are settled and built, so fixed-size arrays and record `Clone` no longer need typechecker or native special cases.
10. **Structural kinds after comptime** [later]: Arrays, the native record `Clone` hook and the remaining structural kinds become std impls, so the compiler rules that v0.16.0 keeps for them are deleted.
11. **Reference rules (B0)** [next, settlement in design lane]: References are second-class under a minimal safe rule set: parameters and block-scoped locals (B0a, #1361), never stored, returned or captured outside an explicit list, with no flag that permits stored references (#1360, #274).
12. **Basic borrow-conflict checking (B1)** [next, settlement in design lane]: Shared and exclusive borrows are checked on by default (many readers or one writer, field-sensitive, including closure-capture loans) for the B0 reference subset. It makes no general memory-safety claim; its guarantee inventory is written down (#2118), and the closure in-call guard R0015 is removed with it if capture loans are modeled (#1712).
13. **Ownership-explicit core** [next]: Moves, copies, clones and drops are explicit operations in Core (L4 of RFC-0241), with dynamic drop flags, and the move check runs over that layer instead of the surface-shaped typed AST.
14. **Instance preparation** [next]: Frozen, monomorphized instances and an InstanceKey cache, with no run-time generic reconstruction. Pulled ahead of Borrow checking on 2026-11-19: instances are the Core-to-Core pass L3 of RFC-0241 section 7.1, so the theme follows Core representation.
15. **Compiled kernel experiment** [next]: A deliberately small monomorphic kernel compiles and runs end to end, as an independently scoped experiment that does not wait on the stability commitment. The first backend is LLVM, emitted from monomorphic Core with no second IR and no aliasing, fast-math or overflow assumptions without a justification; references are absent or B0-only; panics abort. The integration choice stays open (#2120).
16. **Abstract ownership solver** [later]: The hybrid end state of the Copy and Clone design: nominal types get stored ownership interfaces (explicit conditions first, then computed once per declaration by the obligation solver), generic bodies consult only stored interfaces, witnesses are carried to elaboration, and the v0.16.0 limitation (an undecided abstract ownership is a diagnostic in generic bodies) is lifted for what is proven. Epic #1821.
17. **Spec and audit hygiene** [next]: The spec claims only what the implementation does, before the stability commitment.
18. **Usability** [next]: A newcomer can install Metel and finish the first tutorial without hand-rolled workarounds. (Added to this list 2026-11-19; the milestone already existed.)
19. **Effect markers and capabilities** [later]: Effect rows are checked through functions, closures, generics and dispatch, native declarations in std carry checked effect metadata, and capability APIs pass authority explicitly. Its first slice (rows and markers checked, native effect metadata) is the v0.17.0 stage Effect rows and markers; this theme keeps capability APIs, filesystem delegation and implicit formatting.
20. **Algebraic effects** [later]: Handlers run with specified resumption, abandonment, borrowing and cleanup.
21. **Stability commitment** [later]: The language surface and std API are declared stable for users (user-declared native, slice validity and the std redesign excluded); a package design and a conformance corpus exist. A user-facing gate, not a prerequisite for compiler, Interop or Godot work.
22. **Interop** [later]: User libraries declare native functions through a backend-neutral contract (which types cross, ownership at the call, errors, opaque handles, key checking), extending the effect metadata std natives already carry. Panics never cross a native boundary.
23. **Linear records** [later, design lane]: Per-field multiplicity and automatic downgrade are settled against the borrow and drop rules.
24. **Origins and stored references** [later, settlement in design lane]: Reference origins across storage, function boundaries and slices are expressible and checked, so stored and returned references, including `T[]` and `&str`, are allowed. The first step is an opt-in `--origin-check` mode (#2124), on the interpreter and Core evaluator only.
25. **Generative brands and identity domains** [later, design lane]: Rigid generative brands identify authority domains without being a lifetime, a permission or a storage-validity proof; there is no universal storage-identity kind.
26. **Full Core borrow verification (B2)** [later, settlement in design lane]: A borrow checker over Metel-Core verifies origins, stored and returned references, reborrowing, partial moves, closures and unwind and abandonment edges, and only then is general static memory safety claimed. What B1 accepts as stable, B2 accepts too.
27. **Compiled profile v0** [later]: A first program compiles end to end, including the compiled Godot bridge. Stays behind Interop, for the bridge; the earlier compiled target is Compiled kernel experiment.
28. **Godot integration** [later]: Godot embeds Metel through the Interop contract.
29. **Raw storage, typed handles and custody** [later]: Raw storage allocation is separated from typed initialized allocation; allocators and handles are library types whose validity is carried by ownership, origin dependency or custody protocols.
30. **Views and row-polymorphic borrowing** [later]: Generic structural views compose and preserve the access footprint, the returned origins and the nominal identity; disjoint simultaneous borrows are expressible through disjointness bounds and opaque views.
31. **Metel-backed List** [later]: A runtime-sized buffer.
32. **Tracing GC (experimental)** [later]: Local tracing GC.
33. **Compiler expansion** [later]: Broad end-to-end code generation.
34. **Compiler MVP** [later]: Standalone multi-module compilation.
35. **Standard library redesign** [later]: A usable, separately versioned std API.
36. **Concurrency** [later, design lane]: The concurrency model (RFC-0003) is settled.
37. **Standard library additions** [parallel]: Small std additions that do not wait on the redesign.
38. **Aspects and generics** [parallel]: Aspect system gaps: alias syntax, method constraints, where clauses, overlap, dyn Callable.
39. **Metaprogramming and derive** [parallel]: Type-as-value reflection, derive, attributes and auto-impl aspects designed and built on the comptime core.
40. **Records and surface syntax** [parallel]: Surface-syntax additions: conversions, unions, closure ergonomics, hoisting.
41. **Patterns and receivers** [parallel]: Destructuring assignment, field renaming, mutable-by-value receivers.
42. **Playground and interactive docs** [parallel]: Run Metel in the browser.
43. **Website content and experience** [parallel]: The website and tutorials are current.
44. **Docs and RFC tooling** [parallel]: The RFC and docs tooling is reliable.
45. **Engineering hygiene** [parallel]: Small repo-hygiene and lint debt.

Dependencies behind this order:

- v0.17.0 is a staged release (`ROADMAP.md`, "How milestones work"). The order of its stages is a dependency order, derived from each stage's `Needs:` line (2026-11-22, #2160): it puts the stages with no prerequisites first (Row visibility and named records, Function types, Unconditional derivation, Drop and partial moves, with Pipelines free anywhere), then Linear types and Narrowed drop receivers, then Effects design settlement, then Effect rows and markers and Metel-Core and MIR design. It is not a strict sequence: stages run in parallel by thread, a stage can start before the stages it needs finish (Effects design needs only Linear types' design, so it can be gated before Linear types' implementation is), and each stage is gated when it completes. Row visibility and named records is first because it has no prerequisites and gates three other stages. The real dependencies: Linear types waits on Drop and partial moves, on Function types, and on Unconditional derivation (the `linear` class keyword and `copy?` change the same grammar rule, so it goes first); Unconditional derivation coordinates with Row visibility and named records, because RFC-0243's option O4 uses `derives` as its vehicle and the `derives` argument model should be settled once; Narrowed drop receivers waits on Drop and partial moves and on Row visibility and named records (RFC-0109's open opacity question is RFC-0243's V2), and until it lands a partial move out of a type with a `Drop` impl stays rejected; Effect rows and markers waits on Effects design settlement and Function types; the panic clauses do not gate anything (Drop on a recovered panic is RFC-0014's, specified in Effects design settlement and taking effect with Algebraic effects, and Linear types states its own rule, which Effects design settlement reconciles); Metel-Core and MIR design is finalized after Row visibility and named records (RFC-0243 fixes the nominal-with-row kind in Core), Effects design settlement (handler abandonment decides MIR's cleanup edges) and Function types (closure lowering). Numeric and operator model, algebraic effect handlers, `.then`, operator functions and surface cleanup (`let` and `var` hoisting, overload spec) are not in it.
- Move check default-on waits on the Copy decisions of #741, settled in v0.16.0, which stay on the critical path. Copy migration also waits on them and is a stage of v0.16.0, so it ships in the same release.
- Comptime design settlement runs alongside the Copy decisions, Drop and Move check, and its implementation follows Move check default-on: RFC-0132 (execution model and comptime-known generic parameters) first, then RFC-0174 (`comptime for`). Structural kinds after comptime consumes it: `[T; N]: Copy` cannot leave the typechecker without RFC-0132 §3 (the array half of #263, now #1811), and the native record `Clone` hook (#1390) waits on RFC-0174. v0.16.0 keeps arrays and that hook as named compiler rules, which that theme deletes. The rest of metaprogramming (type-as-value, `typeinfo` and `emit`, derive, attributes, auto-impl) stays parallel.
- Linear types follows the Copy decisions of v0.16.0. It is design settlement and implementation in v0.17.0 (RFC-0089, then RFC-0194 on linear closures and captures, which needs RFC-0089 and function types satisfying `Linear` via the auto-impl mechanism, #739); the implementation follows Drop and partial moves and Function types, which is why both are stages of the same release. Linear records (RFC-0091) also waits on Basic borrow-conflict checking (B1) (its open question is the type of a borrow taken before a downgrade) and on Narrowed drop receivers.
- Core representation (RFC-0241 section 7) is thread C of the implementation lane. Its design is a v0.17.0 stage with no code (Metel-Core and MIR design, #2095), and the implementation starts when that design is integrated; the Core datatype, lint, lowering and evaluator do not wait on move-check default-on (#277, which stops the interpreter deep-cloning, is the closing item of Move check default-on). Its first lowering emits monomorphic instances taken from today's per-instance reconstruction, so it does not wait on the shape of generics in Core (RFC-0241 open question 25).
- Comptime runs on the Core evaluator, so it follows Core representation; its design settlement still runs alongside. Ownership-explicit core (the move check over a Core with explicit moves, copies and drops) follows Core representation, Drop and partial moves and Move check default-on, and spikes drop elaboration with early exits on structured Core.
- Instance preparation is the Core-to-Core pass L3 and follows Core representation. Compiled kernel experiment is the thin backend over it: monomorphic Core to LLVM IR directly, no second IR, references absent or B0-only, panics abort, no aliasing, fast-math or overflow assumptions without a justification. Both were pulled ahead of the borrow-checking themes on 2026-11-19, because a compiled path does not need the borrow checker (an accepted program means the same under the reference semantics). Neither waits on the stability commitment.
- Borrow checking is staged. Reference rules (B0) comes first, with the rejection inventory of #1360 and #274 and the lexical locals of B0a (#1361). Basic borrow-conflict checking (B1) follows Move check default-on and B0; it is the first borrow checker on by default and makes no general memory-safety claim. Full Core borrow verification (B2) follows Origins and stored references and Ownership-explicit core, and is the only theme that claims general static safety. The stable subset B1 accepts must be accepted by B2 (monotone). No compiled profile relies on guarantees B1 has not proved.
- Effects design settlement draws on Linear types (exactly-once consumption, one-shot resumption) and the Copy decisions (callable multiplicity). Its exit is a set of accepted RFCs, and no effects implementation starts before them. Effect rows and markers, the first implementation slice, follows it and Function types (the marker mechanism carries effect rows); RFC-0140's dependency audit (#2139, 2026-11-22) found that the slice needs only Function types and the row-calculus RFC #1672 (which, at full scope, needs RFC-0140's open questions 4, the Koka `fun`/`ctl` split, and 6, handler nesting against RFC-0113's uniqueness rule). RFC-0113 context parameters, the allocator RFCs, borrow checking, linear types, concurrency, B1 and Core representation gate handlers or the rest of the theme, not the slice. Handlers and resumption (Algebraic effects) are not in v0.17.0: RFC-0140's sections 2, 3, 6, 7 and 8 rest on allocator tags that Memory model settlement (#2116) amends, so they cannot be specified yet.
- Panic recovery is decided with effects (decided 2026-11-20): a panic is a non-resumable effect, no special-case `catch` is added before effects exist, Drop runs during recovery, an unhandled panic exits immediately, and panics never cross a native boundary. Effects design settlement owns RFC-0014 and RFC-0164. `Panic` is ambient in v0.17.0 as the working position (2026-11-22, #2121): effect rows list declared markers only and handlers can still catch a panic. RFC-0245 leaves open whether it stays ambient or is tracked as `.Panic` in rows, and the slice is built on the ambient position. A no-panic guarantee (working name `NoPanic`, built on the RFC-0232 marker mechanism; spelled as a marker or as the negative entry `!.Panic`, to be decided in #1672) is available where asked, for RFC-0202 and restricted interpolation, and the ambient default is revisited before the Stability commitment, because tracking `Panic` later breaks explicit rows that omitted it. The spec says integer overflow panics unconditionally, so a `NoPanic` body cannot use plain integer arithmetic until checked arithmetic (RFC-0142, #841) exists. The compiled kernel stays `panic=abort`.
- Effect markers and capabilities covers the `native` declarations std already has: each carries checked effect metadata, so a native cannot silently erase an effect. Interop extends that to user-declared natives as an additive surface.
- The Stability commitment (#1358) is a user-facing stability gate, not a compiler prerequisite. It waits for Algebraic effects, so the model is validated by a working implementation before it is promised, and for Surface settlement, Storage contract, Basic borrow-conflict checking (B1), Narrowed drop receivers and Spec and audit hygiene. It covers std's own `native` bindings; user-declared `native`, slice validity and the std redesign are outside it. Interop (#1344, #1355) waits on Effect markers and capabilities and the scalar natives contract (#2111), not on the freeze; Compiled profile v0 waits on the kernel, Instance preparation and Interop; the Godot prototype follows Interop and Compiled profile v0.
- Storage contract (#1292, with the `T[]` nominal question #1123) is settled before the stability commitment: it fixes the roles of `T[N]`, `T[]` and `List<T>` and promises no allocation or interpreter fallback in compiled programs. It coordinates RFC-0053, RFC-0124, RFC-0126 and RFC-0133, and its sized-array half uses Comptime (RFC-0132 §3). The slice half of RFC-0124 (#932) waits on the lifetime-anchor design and moves to Origins and stored references, so slice validity rules are not frozen; `List<T>` itself (#276) stays behind Allocator foundation.
- Memory model settlement is a design-lane theme (#2116): it drops `@s`, supersedes or amends RFC-0063 (accepted), rewrites RFC-0143 and RFC-0242, narrows RFC-0076 and re-scopes RFC-0159, and decides whether references are privileged std types (#2117). Raw storage, typed handles and custody needs Full Core borrow verification (B2), Origins and stored references and Memory model settlement; Generative brands and identity domains needs Memory model settlement and Basic borrow-conflict checking (B1) and is independent of the allocator theme.
- Surface settlement is a design-lane theme: its exit is accepted RFCs, and it must finish before the stability commitment, which promises the surface it decides. RFC-0243 and RFC-0209 left it for the v0.17.0 stage Row visibility and named records, which also implements the decision (RFC-0243 builds on RFC-0209, so 0209 goes first), and RFC-0232 for Function types; opaque views (RFC-0243) wait on Reference rules (B0) and Basic borrow-conflict checking (B1).
- Numeric and operator model is thread B of the implementation lane. Its internal order is float semantics (#2110), then the Eq, PartialEq, Ord, PartialOrd split (RFC-0168), then scalar natives (#2111), then operators and `?` as aspects (RFC-0011, RFC-0190). The overload audit (#2112, in Surface settlement) comes before the operator desugaring. Operator desugaring is the frontend half of Core's L1 to L2 rule (RFC-0241 section 7.4), so Core inherits it.
- Storage contract now includes `String` and `&str` (#2113). The string-literal decision must finish before Move check default-on completes: a string literal is an affine `String` today, so reuse fails the move check.
- Parallel themes are off the critical path and can be taken whenever their prerequisites are met.

## Unscheduled design work

Draft RFCs with no tracking issue. They are listed here so they are not lost; each gets a tracker in its theme when the RFC is committed to a release (RFC process). The home is a proposal, not a commitment, and a draft that is stale is refused in the draft-RFC cleanup (#1671).

- **Aspects and generics**
  - RFC-0038: impl Aspect in Struct Fields and Existential Types
  - RFC-0104: Multi-Aspect Extend Blocks with Shared Bodies
  - RFC-0105: Struct-Embedded Aspect Lists
  - RFC-0114: Constructor Aspect and Canonical Construction
- **Records and surface syntax** (RFC-0183, RFC-0189, RFC-0191, RFC-0221 and RFC-0223 moved to the v0.16.0 stage "Call and record syntax" on 2026-11-07; RFC-0100 moved with them and left the stage exit on 2026-11-11, when it was reopened as a release-level review, #807; the rest stay in this theme)
  - RFC-0151: Tuples as Numeric-Label Rows (moved to the v0.16.0 stage "Copy migration" on 2026-11-12, under review: #1956)
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
- **Raw storage, typed handles and custody, Origins and stored references**
  - RFC-0074: Shared Pointers — Rc and Arc
  - RFC-0075: Region Inference — Local AutoRegion
  - RFC-0145: Static Storage Duration
- **Storage contract**
  - RFC-0172: Sized and Unsized Kinds, and a Generalized Unsizing Coercion
- **No theme yet**
  - RFC-0017: Language Edition System

## Retired numbering

The numbers below were used before 2026-10-19. They appear in older issues, RFCs and
release notes; read them through this table. On 2026-10-20 the mixed theme milestones were
regrouped (below); a number in an issue body names the old grouping, so the issue's current
milestone is authoritative. The retired `v0.17.0` (Compiler-ready pipeline) is not the live
`v0.17.0`, the staged release numbered on 2026-11-22; an older reference to it names the retired grouping.

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

### Regrouping of 2026-11-20

The architecture review (Metel-Core as a layered representation, staged borrow checking, no universal storage identity, a compiler thread with LLVM first) renamed and rescoped these themes. Core surface freeze is no longer a prerequisite for compiler, Interop or Godot work.

| Before | Now |
|---|---|
| Borrow checking | Basic borrow-conflict checking (B1), and a new Full Core borrow verification (B2) |
| Core surface freeze | Stability commitment (a user-facing gate) |
| Lifetimes and regions | Origins and stored references |
| Storage identity | Generative brands and identity domains |
| Allocator foundation | Raw storage, typed handles and custody |
| Views and projections | Views and row-polymorphic borrowing |
| New | Memory model settlement (design lane) |

Runtime value semantics (#277) now closes Move check default-on, after being merged into Core representation on 2026-11-19. RFC-0014 and RFC-0164 left the unscheduled list for Effects design settlement.

### Planning of v0.17.0, 2026-11-22

v0.17.0 was numbered as a staged release of eight stages (#2132), after the staged-release process changed to gate each stage when it completes and to link a stage and its release in both directions (#2130). Three themes became stages under their own names (Drop and partial moves, Linear types, Effects design settlement); five stages are new (Function types, Row visibility and named records, Effect rows and markers, Pipelines, Metel-Core and MIR design). Linear types gained its implementation, which pulled Drop and partial moves and Function types into the release. Numeric and operator model moved to the release after. Core's implementation waits for its design: Core representation no longer starts now, and the v0.17.0 stage settles Metel-Core and the low-level IR as RFCs with no code. Issues moved into stages: #2060, #904, #936, #923, #893 and #894 (Function types); #1790 and #2099 (Row visibility and named records); #1754 (Pipelines); #2095 (Metel-Core and MIR design). The same day RFC-0244 (unconditional derivation and the conditional marker, a draft on docs `main`) was added as a ninth stage, Unconditional derivation (#2150), placed before Linear types. A review of the stage dependencies then found two gaps (#2155): the Drop stage listed #949 (row-bounded Drop dispatch against a narrowed residual), which needs a narrowed `drop` receiver that does not exist (RFC-0109 and RFC-0147 are under review), so Narrowed drop receivers became a tenth stage after Row visibility and named records and #949 moved into it; and the Drop stage claimed to specify Drop on a recovered panic, which is RFC-0014's and takes effect only with Algebraic effects, so the stage now only shapes its cleanup paths for recovery. The stages were then ordered by dependency, with a checked `Needs:` line per stage (#2160), and the effects dependency audit (#2139) settled four points: `Panic` is ambient as the working position for the v0.17.0 slice, with a no-panic guarantee, working name `NoPanic`, whose spelling (a marker or the negative entry `!.Panic`) is left to #1672 (#2121, #2163), and RFC-0245 leaves open whether `Panic` is ambient or tracked in rows; the effects surface is the keywords `effect` and `effects`, not `^`; the row-calculus RFC (#1672) is at full scope, so RFC-0140's open questions 4 and 6 are decided with it; and the slice waits on #1672 and Function types, not on the whole Effects design stage. A review of RFC-0245's example then found that an effect row is not a value, so its row parameter needs RFC-0208's row binder `<..R>` and not `record E`; #1789 moved into Effect rows and markers, with an implementation issue (#2167), and Views and row-polymorphic borrowing no longer lists RFC-0155, RFC-0163 or RFC-0208 in its exit.
