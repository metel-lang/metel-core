# Scripts and CI Processes

This file is a pointer. What every workflow, script, hook and command across the four repositories
does, which requirement it implements and what each flow looks like is in the
**[Operations Specification](docs/operations/index.md)** (`operations/` in `metel-docs`):

- [Flows](docs/operations/flows.md): the implementation flow (issue to `develop`) and the release flow
  (`develop` to production), drawn from the requirements and checked against the repositories for
  staleness (PROC-CI-008).
- [Inventory](docs/operations/inventory.md): every asset and the requirements it implements.
- The requirements themselves, by area: release, deployment, documentation, CI and work management.

[`RELEASING.md`](RELEASING.md) is the release runbook and [`AGENTS.md`](AGENTS.md) the working rules.
