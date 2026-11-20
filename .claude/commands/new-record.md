# /new-record

Create a gap or limitation record. A `LIMIT-*` record says what the implementation falls short of;
a `GAP-*` record says what the Language Spec leaves open (ADR-0055 section 4, ADR-0057). The record
is created by `record.py new`, which numbers it and compares it with every existing record before
writing it, so a duplicate, a contradiction or a record about a program that already works is caught
at creation (PROC-DOCS-014).

**Arguments:** `$ARGUMENTS` — the record's title, e.g. `Closures cannot capture a row variable`

## Steps

1. **Look first.** Search the existing records for the same ground:

```bash
python3 docs/architecture/tools/record.py check
```

   and read `docs/architecture/limitations/` and `docs/architecture/gaps/` for the area. A rule
   that is already recorded, or a fixed limitation, is not a new record.

2. **Decide the kind.** `--kind limit` when the spec says something and the implementation does
   not do it; `--kind gap` when the spec is silent or ambiguous. The tool rejects a `LIMIT` that
   describes the spec and a `GAP` that describes the implementation.

3. **Create it with the tool**, never by hand. Build `target/release/metel` first when giving a
   reproduction, so the tool can run it and confirm it does what the record says:

```bash
cargo build --release -p metel
python3 docs/architecture/tools/record.py new --kind limit --area TYPE-INFERENCE \
  --title "$ARGUMENTS" --summary "<one line>" \
  --description "<what falls short; also what similarity is measured on>" \
  --scope architecture/spec/<file>.md#<requirement> --affects arch.<x>.requirement-N \
  --tracked-by metel-core#NNNN \
  --repro prog.mtl --repro-expect T0002 --core .
```

   Use `--dry-run` first to see the findings. A *blocking* finding (an exact duplicate, a
   reproduction that contradicts its claim, a wrong kind) refuses the write. An *overlap* with an
   existing record refuses it until acknowledged with `--relates ID="why this is not a duplicate"`;
   the reason is stored in the record. Do not acknowledge an overlap without reading the other record.

4. **Validate.**

```bash
python3 docs/architecture/tools/record.py check
python3 docs/architecture/tools/check_architecture.py --core . --check
```

5. **Commit in the submodule through a pull request, then bump the pointer** in this repo on an
   issue branch, as for any `docs/` change. The record names its tracking issue;
   the code item it marks with a `// limit:` comment stays in the same pull request as the code.
