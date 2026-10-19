# Roadmap

Planned work is organised by **theme**, not by version number. A version number is a
statement about what shipped, so it is chosen when a release is cut (`/cut-release`), by
the rule in `RELEASING.md`: a spec change needs at least a minor bump, a patch never
changes the language. Until then nothing refers to a future number.

## How milestones work

- **One numbered milestone is the release in progress** (`vX.Y.Z`, horizon **now**). Its
  issues are what the next tag will contain; `/gap-analysis`, the integration session and
  `/cut-release` run on it.
- **Every other milestone is a theme**, named for the capability it delivers and carrying no
  version number. The first line of its description is `Horizon: next`, `later` or
  `parallel`, then `Formerly vX.Y.Z` for the ones renamed from the old numbering, then the
  scope. `parallel` is work that does not sit on the language critical path (website,
  documentation, project).
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

## Order

Horizon **now**
1. `v0.14.1`: CI and documentation-tooling reliability, plus the language fixes already
   assigned to it.

Horizon **next**
2. **Copy/Clone settlement**: decisions only (RFC-0162, RFC-0135, RFC-0158, #741), before
   the ownership implementation.
3. **Ownership core**: real `Drop`, drop order, partial moves, ownership-faithful runtime
   values, `Copy` migrations into the standard library.

Horizon **later** (in intended order, not a schedule)
4. **Ownership on by default**: the move check on by default, B0 reference rules, spec
   audit, native contract, Godot prototype.
5. **Compiler-ready pipeline**: frontend monomorphization, frozen instances, core surface
   freeze, package design, conformance corpus.
6. **Compiled profile v0**: first end-to-end compiled program and the compiled Godot bridge.
7. **Ownership extensions and views**: self-view narrowing, reference destructuring, nested
   narrowing, function-type multiplicity.
8. **Borrow checking**: RFC-0122 shared versus exclusive borrowing, NLL.
9. **Lifetimes and abstract regions**: lifetime anchors, abstract regions and stored
   references after borrow checking.
10. **Storage identity**: storage identity and ownership stabilisation after borrowing.
11. **Allocator foundation**: placement, allocator-selected handles, associated handle
    families.
12. **Language expansion**: language expansion and cleanup, metaprogramming design
    settlements, outside the critical path.
13. **Metel-backed List**: a runtime-sized buffer after allocation.
14. **Tracing GC (experimental)**: local tracing GC after the allocator foundation.
15. **Compiler expansion**: typed IR and broad end-to-end code generation.
16. **Compiler MVP**: standalone multi-module compilation and release artifacts.

Horizon **parallel**
- **Website, docs and project**: website, documentation and project-foundation work; not a
  dependency of the language or compiler themes.

## Retired numbering

The numbers below were used before 2026-10-19. They appear in older issues, RFCs and
release notes; read them through this table.

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
