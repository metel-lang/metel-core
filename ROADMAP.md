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

1. **v0.16.0** [now]: One release, staged. The shape of the Copy/Clone model is decided (RFC-0162: an explicit `Clone` and a sealed `Copy` that brings a provided `Clone`, specified in RFC-0206 and settled against RFC-0089's multiplicity lattice (the class keywords `copy`, `affine`, `linear`; `linear` reserved), with RFC-0207's `derives` clause, RFC-0212's aspect properties, RFC-0213's super-aspects and RFC-0158 `Share` settled alongside it; RFC-0135 is refused) and its follow-ups are built. The numbered milestone holds the decisions and reconciliation; the stages (milestones that say `Part of: v0.16.0`) are, in order: Call and record syntax (first, added 2026-11-07: the `pub` spelling, RFC-0218; keyword arguments at every call, RFC-0223, and the constructor-syntax review (RFC-0100 reopened and its call implementation rolled back under #1945; replacement design consolidated into RFC-0100, review #807; RFC-0226, #1944, superseded; RFC-0225, dot-prefixed anonymous records, #1943, implemented 2026-11-12 as the stage's last sweep (#1949); the stage has met its exit and closes with the release cut); dotted row labels, RFC-0221; initialization-only `:=`, RFC-0183; one-field record update, RFC-0191; per-label negative row bounds, RFC-0189), then Declarations and derivation (#1799 aspect identity, a behaviour-preserving refactor with no dependency, may start at once), Copy migration (structural kinds as std impls), and Copy and Clone in std. The surface stage goes first because it does not depend on the Copy/Clone model, so the model-defining stages that follow keep their review time (decided 2026-11-07). The Row machinery stage was emptied on 2026-11-06: RFC-0211 was split, its v0.16.0 rule is implemented in Declarations and derivation, and the row-template half (RFC-0217, with RFC-0209 and RFC-0210) moved to "Structural kinds after comptime".
2. **v0.16.1** [next]: Defect fixes that make the implementation follow the unchanged spec: generic bodies are checked and run on the facts of their definition (#1704, #1751, #1752, #1770), module-qualified paths are order-independent (#1769), literals in generic bodies are typed and range-checked (#1774), and the website flow diagrams are fixed (#1760). A patch: the spec does not change. It is a patch that ships after v0.16.0 (decided 2026-11-06).
3. **Linear types** [next, design lane]: The linear-type design (multiplicity, `Linear`, partial consumption) and its closure rules (RFC-0194: a closure that captures a linear value is linear) are settled, so exactly-once consumption is available to effects and capabilities. The rule for linear values under panic and handler abandonment is part of it.
4. **Surface settlement** [next, design lane]: The surface forms that must stop changing before the stability commitment are decided: whether the named record kind is retired (RFC-0243, RFC-0209), function types (RFC-0232), `let` and `var` hoisting (RFC-0131), module layout (RFC-0099 and the `mod.mtl` question) and the overload-resolution rules (#2112). Implementation of each decision goes to the parallel surface themes.
5. **Storage contract** [next, design lane]: The roles of `T[N]`, `T[]` and `List<T>` (inline fixed storage, borrowed contiguous view, owning runtime-sized buffer) are settled before the stability commitment. The same settlement covers text: `String`, a borrowed `&str` view and the type of a string literal (#2113), which must be decided before Move check default-on completes.
6. **Memory model settlement** [next, design lane]: The memory and identity model is settled as RFCs: origins, rigid brands, privileged std reference types, typed handles and custody, without a universal storage-identity kind (`@s` dropped, decided 2026-11-20). Tracker #2116.
7. **Drop and partial moves** [next]: Types with Drop run it in the right order and can be partially moved. Drop behaviour on panic (it runs during recovery) is specified.
8. **Core representation** [next]: Metel-Core exists as the compiler's typed representation (L2 of RFC-0241 section 7): lowered from the typed AST, checked by a well-formedness lint, and run by a reference evaluator that agrees with the tree-walking interpreter on the whole fixture corpus and follows ownership by construction. The same evaluator is the execution model Comptime needs. Core has two phases (before and after ownership elaboration) and no layout or ABI concepts; the shape of generics in Core is left open (RFC-0241 open question 25) and the first lowering emits monomorphic instances only. Thread C of the implementation lane, not waiting on move-check default-on. Tracker #2095.
9. **Numeric and operator model** [next]: Scalar types, the equality and ordering aspects and the operators are std aspects with native scalar bodies, so `1 + 2`, `a < b` and `x?` dispatch through aspects, and f32 and f64 follow IEEE 754. The second implementation thread, beside Drop and partial moves; it meets Move check default-on at the operand modes.
10. **Move check default-on** [next]: The move check runs by default on every program. It waits on the string-literal decision in Storage contract and on the operand modes in Numeric and operator model. The interpreter stops deep-cloning (#277, moved here from Core representation on 2026-11-20).
11. **Comptime** [next]: Comptime execution, comptime-known generic parameters and `comptime for` over a record's fields are settled and built, so fixed-size arrays and record `Clone` no longer need typechecker or native special cases.
12. **Structural kinds after comptime** [later]: Arrays, the native record `Clone` hook and the remaining structural kinds become std impls, so the compiler rules that v0.16.0 keeps for them are deleted.
13. **Reference rules (B0)** [next, settlement in design lane]: References are second-class under a minimal safe rule set: parameters and block-scoped locals (B0a, #1361), never stored, returned or captured outside an explicit list, with no flag that permits stored references (#1360, #274).
14. **Basic borrow-conflict checking (B1)** [next, settlement in design lane]: Shared and exclusive borrows are checked on by default (many readers or one writer, field-sensitive, including closure-capture loans) for the B0 reference subset. It makes no general memory-safety claim; its guarantee inventory is written down (#2118), and the closure in-call guard R0015 is removed with it if capture loans are modeled (#1712).
15. **Ownership-explicit core** [next]: Moves, copies, clones and drops are explicit operations in Core (L4 of RFC-0241), with dynamic drop flags, and the move check runs over that layer instead of the surface-shaped typed AST.
16. **Instance preparation** [next]: Frozen, monomorphized instances and an InstanceKey cache, with no run-time generic reconstruction. Pulled ahead of Borrow checking on 2026-11-19: instances are the Core-to-Core pass L3 of RFC-0241 section 7.1, so the theme follows Core representation.
17. **Compiled kernel experiment** [next]: A deliberately small monomorphic kernel compiles and runs end to end, as an independently scoped experiment that does not wait on the stability commitment. The first backend is LLVM, emitted from monomorphic Core with no second IR and no aliasing, fast-math or overflow assumptions without a justification; references are absent or B0-only; panics abort. The integration choice stays open (#2120).
18. **Effects design settlement** [next, design lane]: Effect rows, markers, capability objects and handler control behaviour are settled as RFCs that share one calculus. Also decides panic recovery (RFC-0014, RFC-0164): a panic is a non-resumable effect with handlers, arriving with effects; Drop runs during recovery; whether `Panic` is tracked in effect rows is open (#2121).
19. **Abstract ownership solver** [later]: The hybrid end state of the Copy and Clone design: nominal types get stored ownership interfaces (explicit conditions first, then computed once per declaration by the obligation solver), generic bodies consult only stored interfaces, witnesses are carried to elaboration, and the v0.16.0 limitation (an undecided abstract ownership is a diagnostic in generic bodies) is lifted for what is proven. Epic #1821.
20. **Narrowed drop receivers** [next]: A `Drop` impl can take only the fields it needs (`&var self: Self.{ fd }`).
21. **Spec and audit hygiene** [next]: The spec claims only what the implementation does, before the stability commitment.
22. **Usability** [next]: A newcomer can install Metel and finish the first tutorial without hand-rolled workarounds. (Added to this list 2026-11-19; the milestone already existed.)
23. **Effect markers and capabilities** [later]: Effect rows are checked through functions, closures, generics and dispatch, native declarations in std carry checked effect metadata, and capability APIs pass authority explicitly.
24. **Algebraic effects** [later]: Handlers run with specified resumption, abandonment, borrowing and cleanup.
25. **Stability commitment** [later]: The language surface and std API are declared stable for users (user-declared native, slice validity and the std redesign excluded); a package design and a conformance corpus exist. A user-facing gate, not a prerequisite for compiler, Interop or Godot work.
26. **Interop** [later]: User libraries declare native functions through a backend-neutral contract (which types cross, ownership at the call, errors, opaque handles, key checking), extending the effect metadata std natives already carry. Panics never cross a native boundary.
27. **Linear records** [later, design lane]: Per-field multiplicity and automatic downgrade are settled against the borrow and drop rules.
28. **Origins and stored references** [later, settlement in design lane]: Reference origins across storage, function boundaries and slices are expressible and checked, so stored and returned references, including `T[]` and `&str`, are allowed. The first step is an opt-in `--origin-check` mode (#2124), on the interpreter and Core evaluator only.
29. **Generative brands and identity domains** [later, design lane]: Rigid generative brands identify authority domains without being a lifetime, a permission or a storage-validity proof; there is no universal storage-identity kind.
30. **Full Core borrow verification (B2)** [later, settlement in design lane]: A borrow checker over Metel-Core verifies origins, stored and returned references, reborrowing, partial moves, closures and unwind and abandonment edges, and only then is general static memory safety claimed. What B1 accepts as stable, B2 accepts too.
31. **Compiled profile v0** [later]: A first program compiles end to end, including the compiled Godot bridge. Stays behind Interop, for the bridge; the earlier compiled target is Compiled kernel experiment.
32. **Godot integration** [later]: Godot embeds Metel through the Interop contract.
33. **Raw storage, typed handles and custody** [later]: Raw storage allocation is separated from typed initialized allocation; allocators and handles are library types whose validity is carried by ownership, origin dependency or custody protocols.
34. **Views and row-polymorphic borrowing** [later]: Generic structural views compose and preserve the access footprint, the returned origins and the nominal identity; disjoint simultaneous borrows are expressible through disjointness bounds and opaque views.
35. **Metel-backed List** [later]: A runtime-sized buffer.
36. **Tracing GC (experimental)** [later]: Local tracing GC.
37. **Compiler expansion** [later]: Broad end-to-end code generation.
38. **Compiler MVP** [later]: Standalone multi-module compilation.
39. **Standard library redesign** [later]: A usable, separately versioned std API.
40. **Concurrency** [later, design lane]: The concurrency model (RFC-0003) is settled.
41. **Copy migration** [stage of v0.16.0]: Hardcoded Copy/Clone rules for tuples and function types leave the typechecker and live in std. RFC-0151 (tuples as numeric-label rows, #1956) is under review in this stage: adopted, it shrinks the tuple half to confirming the row impls cover tuples (decision #1848).
42. **Standard library additions** [parallel]: Small std additions that do not wait on the redesign.
43. **Aspects and generics** [parallel]: Aspect system gaps: alias syntax, method constraints, where clauses, overlap, dyn Callable.
44. **Metaprogramming and derive** [parallel]: Type-as-value reflection, derive, attributes and auto-impl aspects designed and built on the comptime core.
45. **Records and surface syntax** [parallel]: Surface-syntax additions: conversions, unions, closure ergonomics, hoisting.
46. **Patterns and receivers** [parallel]: Destructuring assignment, field renaming, mutable-by-value receivers.
47. **Playground and interactive docs** [parallel]: Run Metel in the browser.
48. **Website content and experience** [parallel]: The website and tutorials are current.
49. **Docs and RFC tooling** [parallel]: The RFC and docs tooling is reliable.
50. **Engineering hygiene** [parallel]: Small repo-hygiene and lint debt.

Dependencies behind this order:

- Move check default-on waits on the Copy decisions of #741, settled in v0.16.0, which stay on the critical path. Copy migration also waits on them and is a stage of v0.16.0, so it ships in the same release.
- Comptime design settlement runs alongside the Copy decisions, Drop and Move check, and its implementation follows Move check default-on: RFC-0132 (execution model and comptime-known generic parameters) first, then RFC-0174 (`comptime for`). Structural kinds after comptime consumes it: `[T; N]: Copy` cannot leave the typechecker without RFC-0132 §3 (the array half of #263, now #1811), and the native record `Clone` hook (#1390) waits on RFC-0174. v0.16.0 keeps arrays and that hook as named compiler rules, which that theme deletes. The rest of metaprogramming (type-as-value, `typeinfo` and `emit`, derive, attributes, auto-impl) stays parallel.
- Linear types follows the Copy decisions of v0.16.0. It is design settlement only (RFC-0089, then RFC-0194 on linear closures and captures, which needs RFC-0089 and function types satisfying `Linear` via the auto-impl mechanism, #739); implementation follows Drop and partial moves. Linear records (RFC-0091) also waits on Basic borrow-conflict checking (B1) (its open question is the type of a borrow taken before a downgrade) and on Narrowed drop receivers.
- Core representation (RFC-0241 section 7, #2095) is thread C of the implementation lane and starts now: the Core datatype, lint, lowering and evaluator do not wait on move-check default-on (#277, which stops the interpreter deep-cloning, is the closing item of Move check default-on). Its first lowering emits monomorphic instances taken from today's per-instance reconstruction, so it does not wait on the shape of generics in Core (RFC-0241 open question 25).
- Comptime runs on the Core evaluator, so it follows Core representation; its design settlement still runs alongside. Ownership-explicit core (the move check over a Core with explicit moves, copies and drops) follows Core representation, Drop and partial moves and Move check default-on, and spikes drop elaboration with early exits on structured Core.
- Instance preparation is the Core-to-Core pass L3 and follows Core representation. Compiled kernel experiment is the thin backend over it: monomorphic Core to LLVM IR directly, no second IR, references absent or B0-only, panics abort, no aliasing, fast-math or overflow assumptions without a justification. Both were pulled ahead of the borrow-checking themes on 2026-11-19, because a compiled path does not need the borrow checker (an accepted program means the same under the reference semantics). Neither waits on the stability commitment.
- Borrow checking is staged. Reference rules (B0) comes first, with the rejection inventory of #1360 and #274 and the lexical locals of B0a (#1361). Basic borrow-conflict checking (B1) follows Move check default-on and B0; it is the first borrow checker on by default and makes no general memory-safety claim. Full Core borrow verification (B2) follows Origins and stored references and Ownership-explicit core, and is the only theme that claims general static safety. The stable subset B1 accepts must be accepted by B2 (monotone). No compiled profile relies on guarantees B1 has not proved.
- Effects design settlement draws on Linear types (exactly-once consumption, one-shot resumption) and the Copy decisions (callable multiplicity). It overlaps the ownership implementation themes; its exit is a set of accepted RFCs, and no effects implementation starts before them.
- Panic recovery is decided with effects (decided 2026-11-20): a panic is a non-resumable effect, no special-case `catch` is added before effects exist, Drop runs during recovery, an unhandled panic exits immediately, and panics never cross a native boundary. Effects design settlement owns RFC-0014 and RFC-0164 and the open question of whether `Panic` is tracked in effect rows (#2121). The compiled kernel stays `panic=abort`.
- Effect markers and capabilities covers the `native` declarations std already has: each carries checked effect metadata, so a native cannot silently erase an effect. Interop extends that to user-declared natives as an additive surface.
- The Stability commitment (#1358) is a user-facing stability gate, not a compiler prerequisite. It waits for Algebraic effects, so the model is validated by a working implementation before it is promised, and for Surface settlement, Storage contract, Basic borrow-conflict checking (B1), Narrowed drop receivers and Spec and audit hygiene. It covers std's own `native` bindings; user-declared `native`, slice validity and the std redesign are outside it. Interop (#1344, #1355) waits on Effect markers and capabilities and the scalar natives contract (#2111), not on the freeze; Compiled profile v0 waits on the kernel, Instance preparation and Interop; the Godot prototype follows Interop and Compiled profile v0.
- Storage contract (#1292, with the `T[]` nominal question #1123) is settled before the stability commitment: it fixes the roles of `T[N]`, `T[]` and `List<T>` and promises no allocation or interpreter fallback in compiled programs. It coordinates RFC-0053, RFC-0124, RFC-0126 and RFC-0133, and its sized-array half uses Comptime (RFC-0132 §3). The slice half of RFC-0124 (#932) waits on the lifetime-anchor design and moves to Origins and stored references, so slice validity rules are not frozen; `List<T>` itself (#276) stays behind Allocator foundation.
- Memory model settlement is a design-lane theme (#2116): it drops `@s`, supersedes or amends RFC-0063 (accepted), rewrites RFC-0143 and RFC-0242, narrows RFC-0076 and re-scopes RFC-0159, and decides whether references are privileged std types (#2117). Raw storage, typed handles and custody needs Full Core borrow verification (B2), Origins and stored references and Memory model settlement; Generative brands and identity domains needs Memory model settlement and Basic borrow-conflict checking (B1) and is independent of the allocator theme.
- Surface settlement is a design-lane theme: its exit is accepted RFCs, and it must finish before the stability commitment, which promises the surface it decides. RFC-0243 builds on RFC-0209; opaque views (RFC-0243) wait on Reference rules (B0) and Basic borrow-conflict checking (B1).
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
