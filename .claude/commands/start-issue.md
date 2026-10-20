# /start-issue

Begin work on a GitHub issue: read it, verify its dependencies are real, create the
issue branch, and summarise the work before any code is written.

**Arguments:** `$ARGUMENTS` — issue number, e.g. `314`

See AGENTS.md § Branch Workflow ("Starting an Issue") and § Task Workflow — this command
mechanises those, it does not define them.

## Steps

1. **Read the issue.**

```bash
gh issue view $ARGUMENTS
```

Surface its title, body, acceptance criteria, labels, and milestone. If it has no
milestone, ask which version it targets — the milestone is the unit of grouping, and the
release gate reads from it.

2. **Check dependencies for real, not just for closed.** Find every `#N` reference and
   "Blocked by"/"Depends on" line in the body. For each, read the dependency issue *and*
   confirm the code actually provides the contract this issue assumes. A closed
   dependency whose implementation diverged from what was agreed is the failure mode
   here; "it's closed" is not the check.

   If a dependency is genuinely unmet, stop and report it rather than branching.

3. **Confirm `develop` is the base and is current.**

```bash
git checkout develop
git pull --recurse-submodules
```

Never branch from `main` (it lags by design), or from another issue branch unless the
dependency is genuine — and if it is, say so in the pull request body.

4. **Create and push the branch**, named `<type>/<issue>-<slug>` with the same type
   vocabulary as the commit convention (`feat`, `fix`, `refactor`, `test`, `docs`,
   `chore`):

```bash
git checkout -b <type>/$ARGUMENTS-<slug>
git push -u origin <type>/$ARGUMENTS-<slug>
```

5. **Read the substance before touching code**, per AGENTS.md § Task Workflow:
   - every spec section the issue touches, from `docs/reference/spec/`
   - any RFC in `docs/rfcs/` the issue implements or depends on — and check its
     lifecycle stage: implementation work does not start on an RFC below `3-integrated`
   - ADRs in `metel-interpreter/docs/decisions/` governing the area
   - the code, by label: `evaluator` → `src/evaluator/` + `docs/evaluator.md`;
     `typechecker` → `src/typechecker/` + `docs/typechecker.md`; `type-inference` →
     `src/typeinference/`; `generics`/`aspects` → `src/types/`; `architecture` →
     `docs/architecture/architecture.md`

6. **Summarise in 2–3 bullets** what will be done, derived from the acceptance criteria,
   and name the regression test each change will need — deciding this now (per-PR gate
   item 3) is cheaper than retrofitting it at the end.

## Notes

- Do not start implementing until the user confirms after seeing the summary.
- If the spec is missing or ambiguous on something this issue needs, update the spec
  first. If the design choice is non-obvious, write an ADR before implementing.
- Commit messages for this issue follow `type(#$ARGUMENTS): description`.
- One issue, one branch, one pull request. If a second concern surfaces mid-branch, file
  it as its own issue — do not widen this one.
