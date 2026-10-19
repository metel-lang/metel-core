# /gap-analysis

Analyse a version milestone's open issues for description gaps, scope ambiguities, and
missing work. Gather every question in a single batched pass, then update the issues so
the milestone can be executed without further clarification.

**Arguments:** `$ARGUMENTS` — the milestone: the numbered release in progress (`v0.14.1`) or a
theme (`Ownership core`) about to be promoted to it (see `ROADMAP.md`).

**Complete the full analysis before asking the user anything.** All questions are batched
into one interaction, not asked one at a time.

The milestone is the unit of grouping (AGENTS.md § Task Tracking) — there is no sprint to
analyse, and no cycle object anywhere.

---

## Step 1 — Load milestone context

```bash
gh issue list --milestone  --state open
```

Read each issue in full (`gh issue view <N>`) — description, labels, referenced issue numbers.
Then read `docs/reports/strategy/OBJECTIVES.md` §2 (current priorities) and §3 (open
triggers) for anything bearing on this milestone, and the spec sections in
`docs/reference/spec/` the milestone's theme is likely to touch.

### 1a. RFC lifecycle pre-check (hard gate)

Before analysing any individual issue, scan `docs/internal/rfcs/` for every RFC referenced
in a milestone issue (`rfc-NNNN`), plus every RFC at `2-accepted` or `3-integrated`.

The RFC's **directory** is the source of truth for its stage; frontmatter `status` must
match it. Run the mechanical check first:

```bash
python3 docs/internal/rfcs/tools/rfc.py check
```

Then report two classes of blocker at the top of the Step 4 output:

**Class 1 — Not yet integrated (`2-accepted` or below).** Implementation work does not
start below `3-integrated`: the spec has not been updated and the worked examples have not
been checked against everything else already integrated. Any issue implementing such an
RFC is blocked on integrating it first.

**Class 2 — Integrated but untracked.** An RFC at `3-integrated` or beyond whose
`impl_status`/`impl_tracking` frontmatter is missing, stale, or points at a closed issue.
This is tracking debt and must be resolved before the milestone closes.

```
### RFC blockers (must be resolved before the milestone can proceed)

**rfc-NNNN — <title>**
- Class: [Not yet integrated | Integrated but untracked]
- Finding: <one sentence>
- Required action: <what to do>
```

Do not proceed to issue-level analysis until the user confirms how blockers resolve.

---

## Step 2 — Analyse each issue

For every open issue in the milestone, silently evaluate all of the following. Record
every finding — present them together in Step 4.

### 2a. Description completeness
Could an agent implement this from the description alone, without asking questions? Flag
if any of these is missing or vague:
- **What** specifically changes (which file, function, grammar rule, type, or behaviour)
- **Why** — the motivation or constraint driving it
- **Acceptance criteria** — explicit, testable conditions for "done", not "it works"
- **Edge cases** — empty input, type mismatch, recursive structure, generic instantiation
- **Error behaviour** — which error code or message an invalid input produces

### 2b. Scope
Flag any issue holding more than one concern that could fail or be deferred separately.
This matters more than it used to: one issue is one branch is one pull request, so an
over-scoped issue produces exactly the omnibus diff that retiring sprint branches was
meant to eliminate. Signs:
- The description says "and also…" about unrelated behaviour
- Implementing it touches more than two unrelated modules
- It splits cleanly into a spec change plus an implementation

### 2c. Spec and RFC alignment
- Is there a section in `docs/reference/spec/` governing this behaviour? Does it
  already describe the target behaviour, or must the spec change first?
- Does this need an RFC? If so, does one exist, and is it at `3-integrated` or beyond?
- Does it implement an already-integrated RFC? Note the id and check `impl_tracking`
  points at this issue.

Flag: missing spec section, RFC below `3-integrated`, RFC not written, spec/RFC conflict.

### 2d. Dependencies
- Does it depend on another issue (look for `#N`, "Blocked by", "Depends on")?
- Is that dependency scheduled to land first?
- For a *closed* dependency, does the code actually provide the contract this issue
  assumes? A closed issue whose implementation diverged is the failure mode; "it's closed"
  is not the check.
- Does it require a spec change not tracked as its own issue?

### 2e. Test requirements
Flag if:
- No acceptance criterion maps to a concrete fixture
- It touches the typechecker or evaluator with no negative-case requirement stated
- It changes a builtin without mentioning the `runtime.md` table update
- The needed fixture is a directory fixture and nobody has said so — the sidecar is
  `test.toml` there and `<name>.toml` for a single file, and getting it wrong makes the
  sidecar silently inert

---

## Step 3 — Analyse the milestone as a whole

### 3a. Coverage
Read the milestone's intent (from `OBJECTIVES.md` and the issues themselves). List every
concern it implies, and flag each one with no issue tracking it.

### 3b. Implementation order
Derive the natural order from the dependency graph. Flag ordering conflicts, and flag any
**release gate** in an RFC — a §-level "must not ship without X" clause (RFC-0071 §9c is
the live example) is a hard blocker on the release, not a preference.

### 3c. Missing scaffolding
Flag if the milestone needs any of these with no issue for it:
- A spec section that does not exist yet
- A new error code or error variant
- A new AST node, typed AST node, or grammar rule
- A fixture directory that does not exist yet

### 3d. Risk items
Flag any issue that:
- Touches `src/typeinference/mod.rs` or `src/typechecker/` (high blast radius)
- Changes `src/grammar.pest` (ripples into parser and AST)
- Introduces a static check over an existing fixture corpus — that has its own pattern,
  see AGENTS.md § Landing an Enforcement Pass Over an Existing Corpus
- Has no prior art in the codebase

For each, decide whether an investigation issue should precede the implementation issue.

---

## Step 4 — Batch all questions

Compile every finding from Steps 2 and 3 into one report. Do not ask piecemeal.

```
## Gap Analysis — $ARGUMENTS

### RFC blockers
…(from Step 1a)

### Issue gaps
**#N — <title>**
- Gap type: [Description / Scope / Spec / RFC / Dependency / Test]
- Finding: <one sentence>
- Question: <the specific question that fills it>

### Milestone-level gaps
**[Coverage / Order / Scaffolding / Risk]**
- Finding: <what is missing or risky>
- Question: <the decision needed>

### Proposed new issues
**Proposed: <title>**
- Reason: <why it is separate>
- Suggested description: <draft>
- Question: add to $ARGUMENTS, defer to a later milestone, or already covered?
```

Wait for answers to **all** questions before changing anything.

---

## Step 5 — Update the issues

Using the answers, for each flagged issue:

```bash
gh issue edit <N> --body "<rewritten body>"
```

- Extend the original intent; do not replace it.
- Add explicit acceptance criteria, edge cases, and error behaviour.
- Add `RFC: rfc-NNNN` and `Spec: docs/reference/spec/<section>.md` where identified.
- Note the dependency direction explicitly (`Blocked by #N` / `Blocks #N`) — GitHub
  renders these as links but does not enforce them, so they are documentation.

## Step 6 — Create new issues

For each confirmed gap:

```bash
gh issue create --title "<title>" --description "<full body>" --milestone $ARGUMENTS
```

Write the body in full from Steps 2–4, not as a stub. For gaps deferred past this
milestone, create them with a later milestone or none.

**Rate limit:** GitHub rate limits are reported by the API; inspect them before bulk operations.
Run `gh` from the repository root, never from `docs/`.

## Step 7 — Verify and report

```bash
gh issue list --milestone $ARGUMENTS --state open
```

```
## $ARGUMENTS — ready for execution

### Issues, in dependency order
- #N — <title> [labels]
  Acceptance criteria: <1-line summary>

### Deferred past this milestone
- #N — <title> (reason)

### Risk items requiring extra care
- #N — <title>: <risk>

### Release gates
- <RFC §clause>: #N must not ship without #M
```

Then: run `/start-issue <N>` on the first item.

---

## Notes

- The goal is **zero surprises during implementation**. Every question that could arise
  mid-implementation should be answered here.
- Do not update any issue until the user has answered everything in Step 4. No partial
  updates.
- If an issue turns out to be out of scope for this milestone, re-milestone it rather than
  leaving it attached to a version it will not ship in — the release gate checks this.
- If the milestone's own intent is unclear after analysis, surface that as the first
  question; a milestone with an unclear goal cannot be gap-analysed.
