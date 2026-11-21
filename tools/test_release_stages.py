import tempfile
import unittest
from pathlib import Path

from tools.release_stages import (
    Milestone, declared_stages, gated_stage_names, listed_stages, part_of, problems, report_path, scope, slug,
    stage_name,
)

V = "v0.17.0"


def release(*titles, **kw):
    body = "Horizon: now. Outcome.\n\nStages:\n" + "\n".join(f"- {t}" for t in titles) + "\n"
    return Milestone(V, body, **kw)


def stage(name, version=V, **kw):
    kw.setdefault("description", f"Horizon: now.\nPart of: {version}\n\nOutcome. Exit: x.")
    return Milestone(f"[{version}] {name}", **kw)


class Parsing(unittest.TestCase):
    def test_part_of_is_an_exact_line_and_tolerates_crlf(self):
        self.assertEqual(part_of("Horizon: now.\r\nPart of: v0.17.0\r\n\r\nx"), V)
        self.assertIsNone(part_of("see Part of: v0.17.0 in the text"))
        self.assertIsNone(part_of("Part of: v0.17"))

    def test_the_stages_block_ends_at_the_first_line_that_is_not_an_item(self):
        text = "Stages:\n- [v0.17.0] A\n- [v0.17.0] B\n\n- not a stage\n"
        self.assertEqual(listed_stages(text), ["[v0.17.0] A", "[v0.17.0] B"])
        self.assertEqual(listed_stages("no block here"), [])

    def test_stage_name_drops_the_tag_and_slug_is_a_file_name(self):
        self.assertEqual(stage_name("[v0.17.0] Row visibility and named records"), "Row visibility and named records")
        self.assertEqual(stage_name("Plain theme"), "Plain theme")
        self.assertEqual(slug("Metel-Core and MIR design"), "metel-core-and-mir-design")


class Links(unittest.TestCase):
    def test_a_release_and_its_stages_that_agree_have_no_problems(self):
        a, b = stage("Linear types"), stage("Function types")
        self.assertEqual(problems(V, [release(a.title, b.title), a, b]), [])

    def test_a_release_with_no_stages_is_not_a_problem(self):
        self.assertEqual(problems(V, [Milestone(V, "Horizon: now.")]), [])

    def test_a_stage_the_release_does_not_list_is_found(self):
        a = stage("Linear types")
        found = problems(V, [release(), a])
        self.assertTrue(any("does not list it" in p for p in found), found)

    def test_a_listed_stage_that_does_not_exist_or_does_not_declare_the_release_is_found(self):
        a = stage("Linear types", description="Horizon: now.")
        found = problems(V, [release(a.title, "[v0.17.0] Ghost"), a])
        self.assertTrue(any("not a milestone" in p for p in found), found)
        self.assertTrue(any("does not say `Part of" in p for p in found), found)

    def test_the_title_must_carry_the_release_tag(self):
        a = Milestone("Linear types", "Part of: v0.17.0")
        found = problems(V, [release("Linear types"), a])
        self.assertTrue(any("does not start with" in p for p in found), found)

    def test_a_stage_listed_twice_is_found(self):
        a = stage("Linear types")
        self.assertTrue(any("more than once" in p for p in problems(V, [release(a.title, a.title), a])))

    def test_due_dates_must_follow_release_then_stages_in_list_order(self):
        a = stage("A", due_on="2027-01-03T00:00:00Z")
        b = stage("B", due_on="2027-01-02T00:00:00Z")
        r = release(a.title, b.title, due_on="2027-01-01T00:00:00Z")
        self.assertTrue(any("due dates" in p for p in problems(V, [r, a, b])))
        b2 = stage("B", due_on="2027-01-04T00:00:00Z")
        self.assertEqual(problems(V, [release(a.title, b2.title, due_on="2027-01-01T00:00:00Z"), a, b2]), [])

    def test_a_missing_release_milestone_is_reported(self):
        self.assertEqual(problems(V, [stage("A")]), [f"no milestone named {V}"])

    def test_listed_order_comes_first_then_unlisted_declarers(self):
        a, b, c = stage("A"), stage("B"), stage("C")
        self.assertEqual([m.title for m in declared_stages(V, [release(b.title, a.title), a, b, c])],
                         [b.title, a.title, c.title])


class Gates(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.reports = Path(self._tmp.name)
        self.addCleanup(self._tmp.cleanup)

    def write_report(self, name, result="PASS"):
        path = report_path(self.reports, V, name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"# Stage gate\n\n**Result:** {result}\n")

    def test_a_gated_release_needs_every_stage_closed_with_no_open_issue_and_a_passing_report(self):
        a = stage("Linear types", state="closed")
        b = stage("Function types", state="open", open_issues=2)
        found = problems(V, [release(a.title, b.title), a, b], gated=True, reports=self.reports)
        self.assertTrue(any("Linear types" in p and "no passing report" in p for p in found), found)
        self.assertTrue(any("Function types" in p and "not closed" in p for p in found), found)
        self.assertTrue(any("Function types" in p and "2 open issue" in p for p in found), found)
        self.write_report("Linear types")
        found = problems(V, [release(a.title), a], gated=True, reports=self.reports)
        self.assertEqual(found, [])

    def test_a_failing_report_is_not_a_gate(self):
        a = stage("Linear types", state="closed")
        self.write_report("Linear types", "BLOCKED")
        self.assertTrue(problems(V, [release(a.title), a], gated=True, reports=self.reports))

    def test_the_scope_is_the_stage_and_the_stages_already_gated_never_the_open_ones(self):
        a = stage("Linear types", state="closed")
        b = stage("Function types", state="closed")
        c = stage("Effects", state="open")
        d = stage("Pipelines", state="open")
        ms = [release(a.title, b.title, c.title, d.title), a, b, c, d]
        self.write_report("Linear types")  # gated
        # Function types is closed but has no passing report, so it is not gated
        self.assertEqual(gated_stage_names(V, ms, self.reports), ["Linear types"])
        self.assertEqual(scope(V, ms, "[v0.17.0] Effects", self.reports), ["Effects", "Linear types"])
        self.write_report("Function types")
        self.assertEqual(scope(V, ms, "Effects", self.reports), ["Effects", "Linear types", "Function types"])

    def test_scoping_an_unknown_stage_is_an_error(self):
        a = stage("Linear types")
        with self.assertRaisesRegex(ValueError, "not a stage"):
            scope(V, [release(a.title), a], "Nonsense", self.reports)


if __name__ == "__main__":
    unittest.main()
