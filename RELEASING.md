# Releasing

Cutting a `vX.Y.Z` tag here triggers the entire public-facing release chain, end to
end, writing to `metel-website` (the only repo this chain writes to as of ADR-0051 —
it reads `metel-core`'s own pinned `docs` submodule commit, which points at the public
`metel-docs`, but doesn't write there anymore). This document describes that chain;
the workflows themselves are `.github/workflows/release.yml` here and
[`metel-website`'s `deploy.yml`](https://github.com/metel-lang/metel-website/blob/main/.github/workflows/deploy.yml).

For the release chain in the context of every other script and CI workflow across all
four repos — including the per-PR checks and the manual docs-only path this document
doesn't cover — see [`PROCESSES.md`](PROCESSES.md).

The contracts this chain keeps are stated in the
[Operations Specification](docs/operations/spec/release.md) (`PROC-RELEASE-*`); this document
describes the chain, the specification states what must hold.

**Before the tag:** the milestone passes two gates that this chain assumes are already
green — `/milestone-integration-test <version>` (cross-feature testing, commits
`docs/release-notes/integration/<version>.md`) and then `/cut-release <version>` (the
repo-wide release gate, which checks for that report). This document picks up at the
`git push origin vX.Y.Z` those produce.

## The chain

```
metel-core tag vX.Y.Z pushed
        │
        ▼
release.yml (here, Stage A)
  1. checks out this repo's docs submodule (metel-docs, public,
     unauthenticated — ADR-0051 retired the private-submodule sync this step
     used to perform first; metel-docs is directly edited, nothing to mirror)
  2. reads this repo's own pinned docs submodule commit
  3. in a fresh metel-website checkout: bumps its docs submodule pointer to
     that commit; for a minor release (patch component 0) renders the
     architecture evidence into that docs working copy, pinned to this tag
     (ADR-0064), and runs `docusaurus docs:version X.Y.Z`; commits the generated
     versioned_docs/ + versioned_sidebars/ + versions.json (skipped if nothing
     changed), pushes to main. A patch release cuts no snapshot.
  4. tags that commit vX.Y.Z in metel-website — skipped if the tag already
     exists there (safe to re-run this whole workflow after fixing a failure)
        │
        ▼  (a real tag push — GitHub's own trigger, not a synthetic dispatch)
deploy.yml (metel-website, Stage B)
  1. builds the site once
  2. deploys that build to Vercel staging, posts the URL to the run summary
        │
        ▼  (manual: a human reviews the staging URL, then runs promote.yml)
promote.yml (metel-website, Stage C — workflow_dispatch only)
  1. promotes that exact staged build (no rebuild) to production
  2. verifies both the staging URL and https://metel-lang.org are reachable
```

## Why it's split this way

The rules are stated in the Operations Specification, `PROC-RELEASE-009` (each step writes to
one repository, with a credential scoped to it) and `PROC-DEPLOY-003` (production changes only
by promoting a reviewed staging build). The reasons behind them:

- No single credential spans more than one repository. The secrets are `WEBSITE_TOKEN`
  (`metel-core`, write to `metel-website` only) and the three Vercel secrets (`metel-website`).
  `DOCS_REPO_TOKEN` and `DOCS_PUBLIC_TOKEN` are retired (ADR-0051): `metel-docs` is public and
  `release.yml` no longer writes to it. They should be removed from `metel-core`'s repository
  settings, not left provisioned and unused.
- `release.yml` starts `deploy.yml` by pushing a real tag, not a synthetic `repository_dispatch`,
  so `metel-website`'s pipeline stays independently triggerable: a `vX.Y.Z` tag pushed to
  `metel-website` runs the same pipeline, which tests that side without a `metel-core` release.
- Promotion is manual so that automation does not remove the review checkpoint before something
  goes live on `metel-lang.org`. A GitHub Environment required-reviewer gate was the design, but
  that feature needs a paid plan for private repositories (`422`: "Please ensure the billing plan
  supports the required reviewers protection rule"), so a person running `promote.yml` after
  reviewing the staging URL is the approval.

## Failure handling

There is no cross-repo rollback. If the chain fails partway — e.g. `release-chain`'s
`metel-website` commit lands but `github-release`'s binary build errors (the two run
independently) — the run fails loudly (visible via
`gh run list --repo metel-lang/metel-core`) and stops there, leaving a partial but
inspectable state rather than a silent inconsistency. Every write step diffs before
committing, and the final tag step checks for the tag's existence first, so re-running
`release.yml` on the same tag after fixing whatever broke is safe: steps that already
completed become no-ops, and only the step that failed (and anything after it) does
real work the second time.

## Provisioning the required secrets

None of these can be created by an assistant holding only a personal access token
scoped to this repo — each needs to be set up by hand, once. (`DOCS_REPO_TOKEN` and
`DOCS_PUBLIC_TOKEN` used to be provisioned here too — retired by ADR-0051, see "Why
it's split this way" above; nothing to provision for `docs` submodule access anymore.)

- **`WEBSITE_TOKEN`**: a GitHub fine-grained PAT, "Only select repositories" →
  `metel-website`, `Contents: Read and write`. Store as a `metel-core` repo secret.
- **`VERCEL_TOKEN`**: from the Vercel dashboard (Account Settings → Tokens), scoped to
  the project backing `metel-website` if Vercel's token scoping allows it. Store as a
  `metel-website` repo secret.
- **`VERCEL_ORG_ID`** / **`VERCEL_PROJECT_ID`**: from that same project's Vercel
  dashboard settings, or by running `vercel link` locally against it once and reading
  `.vercel/project.json`. Store as `metel-website` repo secrets.

No GitHub Environment or reviewer setup is needed — see the previous section for why.

## Promoting a staged release to production

After `deploy.yml` runs, its job summary (`metel-website`'s Actions tab → the run →
Summary) prints the staging URL and the exact command to promote it. Review the
staging URL, then either:

- **Actions tab** → `metel-website` → "Promote to production" → Run workflow, filling
  in `deployment_url` and `tag`, or
- `gh workflow run promote.yml --repo metel-lang/metel-website -f
  deployment_url=<url> -f tag=vX.Y.Z`
