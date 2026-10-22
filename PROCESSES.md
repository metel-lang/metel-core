# Scripts and CI Processes

What every workflow, script, hook and command across the four repositories does, which
requirement it implements and which repository owns it is stated in the
**[Operations Specification](docs/operations/index.md)** (`operations/` in `metel-docs`):

- [`inventory.md`](docs/operations/inventory.md) maps every asset to the `PROC-*`
  requirements it implements. `check_operations.py` discovers the assets and fails or warns when
  one is unmapped or a row names something that no longer exists (PROC-CI-008).
- The requirements state each trigger, product, owner and verification, including the secrets by
  class (PROC-RELEASE-009), the example-checker exclusions (PROC-DOCS-010) and the manual docs-only
  publish procedure (PROC-DEPLOY-006).
- [`RELEASING.md`](RELEASING.md) is the release runbook and [`AGENTS.md`](AGENTS.md) the working
  rules.

This file used to carry per-asset tables that duplicated the inventory and drifted from it
(metel-core#687, #1528, #1533). It now holds only the cross-repository diagram below, which moves
into the specification with checks against drift in metel-core#1534. Treat it as an overview, not as
the reference: where it and the specification disagree, the specification wins.

```mermaid
flowchart TD
    subgraph MDI["metel-docs-internal (private, trunk-based, no CI)"]
        direction TB
        MDI_main["main\n(internal/, reports/)"]
    end

    subgraph MC["metel-core"]
        direction TB
        MC_branch["issue branch"]
        MC_ci["ci.yml\n(test/clippy/fmt, rfc-check,\ngrammar-doc-check, stdlib-doc-check,\ndoc-examples, inventory,\nclippy-allow-ratchet, resolution-freeze-check,\npublish-develop-binary)"]
        MC_develop["develop"]
        MC_tag["tag vX.Y.Z on main"]
        MC_rel["release.yml\nvalidate-release -> release-chain\n+ github-release"]
        MC_branch --> MC_ci --> MC_develop --> MC_tag --> MC_rel
    end

    subgraph MDPub["metel-docs (public, directly edited)"]
        direction TB
        MD_main["main"]
        MD_ci1["check-examples.yml"]
        MD_ci2["check-mdx.yml"]
        MD_ci3["rfc-check.yml"]
        MD_main --> MD_ci1
        MD_main --> MD_ci2
        MD_main --> MD_ci3
    end

    subgraph MW["metel-website"]
        direction TB
        MW_branch["PR branch"]
        MW_ci["check-showcases.yml"]
        MW_main["main\n(docs submodule pointer)"]
        MW_tag["tag vX.Y.Z"]
        MW_deploy["deploy.yml\n(build + Vercel staging)"]
        MW_promote["promote.yml\n(manual, workflow_dispatch)"]
        MW_branch --> MW_ci
        MW_main --> MW_tag --> MW_deploy --> MW_promote
    end

    PROD(["metel-lang.org"])

    MC_ci -. "fetches check_doc_examples.py\n+ downloads develop-latest binary\nfrom metel-core@develop" .-> MD_ci1
    MC_ci -. "fetches check_doc_examples.py\n+ downloads develop-latest binary\nfrom metel-core@develop" .-> MW_ci

    MC_rel -->|"bump docs pointer to MC's pinned\nmetel-docs commit, docusaurus\ndocs:version (WEBSITE_TOKEN)"| MW_main
    MW_deploy -->|"staging URL in job summary"| MW_promote
    MW_promote -->|"human reviews, then approves"| PROD

    MD_main -. "manual docs-only bump\n(no version tag — see below)" .-> MW_main
```

Solid arrows are automated triggers or writes. Dashed arrows are a runtime fetch or the one manual
path that has no workflow (PROC-DEPLOY-006).
