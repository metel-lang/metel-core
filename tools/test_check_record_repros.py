#!/usr/bin/env python3
"""Self-test for check_record_repros.py: a fake interpreter, synthetic records, no build needed."""
import os
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_record_repros as crr

FAKE = """#!/usr/bin/env python3
import sys
src = open(sys.argv[1]).read()
if "REJECTED" in src:
    sys.stderr.write("[T0002] type error: cannot infer\\n"); sys.exit(1)
if "NOCODE" in src:
    sys.stderr.write("boom\\n"); sys.exit(3)
if "SLOW" in src:
    import time; time.sleep(5)
"""

RECORD = """---
id: {id}
title: "t"
disposition: {disp}
---

## Limitation

```metel{attr}
{body}
```
"""


class RunnerTests(unittest.TestCase):
    def setUp(self):
        self.td = tempfile.TemporaryDirectory()
        self.root = Path(self.td.name)
        (self.root / "docs/architecture/limitations").mkdir(parents=True)
        (self.root / "docs/architecture/gaps").mkdir(parents=True)
        self.metel = self.root / "fake-metel"
        self.metel.write_text(FAKE)
        self.metel.chmod(self.metel.stat().st_mode | stat.S_IEXEC)

    def tearDown(self):
        self.td.cleanup()

    def record(self, name, disp="known", attr="", body="fun main() {}", kind="limitations"):
        (self.root / f"docs/architecture/{kind}/{name.lower()}.md").write_text(RECORD.format(id=name, disp=disp, attr=attr, body=body))

    def cli(self, *args):
        out = subprocess.run(
            [sys.executable, str(Path(crr.__file__)), "--metel", str(self.metel), "--root", str(self.root), *args],
            capture_output=True, text=True,
        )
        return out.returncode, out.stdout

    def test_a_reproduction_that_still_gives_its_result_is_quiet(self):
        self.record("LIMIT-A-001", attr=" repro=T0002", body="REJECTED")
        self.record("LIMIT-A-002", attr=" repro=ok")
        code, out = self.cli("--strict")
        self.assertEqual(code, 0, out)
        self.assertIn("2 run for 2 of 2 active records; 0 stale", out)

    def test_a_fixed_limitation_is_a_warning_and_a_strict_failure(self):
        self.record("LIMIT-A-001", attr=" repro=T0002", body="fun main() {}")
        code, out = self.cli()
        self.assertEqual(code, 0)
        self.assertIn("warning: LIMIT-A-001: its reproduction is recorded as `repro=T0002` but now gives `ok`", out)
        self.assertEqual(self.cli("--strict")[0], 1)

    def test_a_changed_diagnostic_is_stale_too(self):
        self.record("LIMIT-A-001", attr=" repro=T0001", body="REJECTED")
        self.assertIn("now gives `T0002`", self.cli()[1])

    def test_a_failure_without_a_code_is_reported_as_such(self):
        self.record("LIMIT-A-001", attr=" repro=ok", body="NOCODE")
        self.assertIn("exit 3 with no diagnostic code", self.cli()[1])

    def test_resolved_and_superseded_records_are_not_run(self):
        self.record("LIMIT-A-001", disp="resolved", attr=" repro=T0002", body="fun main() {}")
        self.record("LIMIT-A-002", disp="superseded", attr=" repro=T0002", body="fun main() {}")
        code, out = self.cli("--strict")
        self.assertEqual(code, 0, out)
        self.assertIn("0 run for 0 of 0 active records", out)

    def test_a_malformed_expectation_is_always_an_error(self):
        self.record("LIMIT-A-001", attr=" repro=")
        code, out = self.cli()
        self.assertEqual(code, 1)
        self.assertIn("`repro=` must be `ok` or a diagnostic code", out)

    def test_gap_records_are_run_as_well(self):
        self.record("GAP-A-001", attr=" repro=T0002", body="fun main() {}", kind="gaps")
        self.assertIn("warning: GAP-A-001", self.cli()[1])

    def test_a_fence_without_repro_is_ignored_unless_suggesting(self):
        self.record("LIMIT-A-001", body="REJECTED")
        code, out = self.cli()
        self.assertEqual((code, "0 run for 0 of 1 active records" in out), (0, True))
        self.assertIn("LIMIT-A-001: T0002", self.cli("--suggest")[1])

    def test_a_missing_interpreter_is_an_error_not_a_pass(self):
        self.metel.unlink()
        self.assertEqual(self.cli()[0], 2)


if __name__ == "__main__":
    unittest.main()
