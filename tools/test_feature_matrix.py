import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

from tools.feature_matrix import (
    TABLE_END, TABLE_START, Feature, Fixture, apply_bulk, check_table, compute_metrics, evaluate_pair, gate_blockers,
    load_bulk, load_registry, load_states, render_table,
)


def feature(identifier, rules, subsystems=("ownership",), introduced="v0.16.0"):
    return Feature(
        identifier, identifier.title(), introduced, ("test source",),
        frozenset(subsystems), frozenset(rules),
    )


class PairScoring(unittest.TestCase):
    def setUp(self):
        self.a = feature("a", ["spec.ownership.a.legality-1", "spec.ownership.a.legality-2"])
        self.b = feature("b", ["spec.ownership.b.legality-1", "spec.ownership.b.legality-2"])

    def test_score_accumulates_distinct_rules_from_joint_fixtures(self):
        fixtures = [
            Fixture("one", frozenset({"spec.ownership.a.legality-1", "spec.ownership.b.legality-1"})),
            Fixture("two", frozenset({"spec.ownership.a.legality-2", "spec.ownership.b.legality-1"})),
        ]
        cell = evaluate_pair(self.a, self.b, fixtures, {}, set())
        self.assertEqual(cell.score, Fraction(3, 4))
        self.assertEqual(cell.status, "partial")
        self.assertEqual(cell.evidence, ("one", "two"))

    def test_single_feature_fixture_does_not_count_as_pair_evidence(self):
        fixtures = [Fixture("one", frozenset({"spec.ownership.a.legality-1"}))]
        cell = evaluate_pair(self.a, self.b, fixtures, {}, set())
        self.assertEqual(cell.score, Fraction(0, 1))
        self.assertEqual(cell.status, "open")

    def test_removed_or_retagged_fixture_reopens_the_cell(self):
        covered = [Fixture("one", frozenset({"spec.ownership.a.legality-1", "spec.ownership.a.legality-2",
                                             "spec.ownership.b.legality-1", "spec.ownership.b.legality-2"}))]
        self.assertEqual(evaluate_pair(self.a, self.b, covered, {}, set()).status, "covered")
        stale = [Fixture("one", frozenset({"spec.ownership.a.legality-1"}))]
        self.assertEqual(evaluate_pair(self.a, self.b, stale, {}, set()).status, "open")

    def test_explicit_state_is_stable_when_fixture_evidence_changes(self):
        pair = ("a", "b")
        state = {pair: {"state": "deferred", "reason": "known gap", "issue": "https://github.com/o/r/issues/1"}}
        cell = evaluate_pair(self.a, self.b, [], state, set())
        self.assertEqual(cell.status, "deferred")
        self.assertEqual(cell.issue, "https://github.com/o/r/issues/1")


class Gate(unittest.TestCase):
    def setUp(self):
        self.a = feature("a", ["spec.ownership.a.legality-1", "spec.ownership.a.legality-2"])
        self.b = feature("b", ["spec.ownership.b.legality-1"])

    def test_open_tier_a_cell_blocks(self):
        cell = evaluate_pair(self.a, self.b, [], {}, set())
        self.assertEqual(gate_blockers([cell]), [cell])

    def test_partial_tier_a_cell_does_not_block(self):
        fixtures = [Fixture("one", frozenset({"spec.ownership.a.legality-1", "spec.ownership.b.legality-1"}))]
        cell = evaluate_pair(self.a, self.b, fixtures, {}, set())
        self.assertEqual(cell.status, "partial")
        self.assertEqual(gate_blockers([cell]), [])

    def test_deferred_and_n_a_do_not_block(self):
        for state in ("n/a", "deferred"):
            manual = {("a", "b"): {"state": state, "reason": "r", "issue": "https://github.com/o/r/issues/1"}}
            cell = evaluate_pair(self.a, self.b, [], manual, set())
            self.assertEqual(gate_blockers([cell]), [])

    def test_open_tier_b_cell_does_not_block(self):
        far = feature("c", ["spec.types.c.legality-1"], subsystems=("types",))
        cell = evaluate_pair(self.a, far, [], {}, {("ownership", "types")})
        self.assertEqual(cell.tier, "B")
        self.assertEqual(gate_blockers([cell]), [])


class BulkDeferral(unittest.TestCase):
    ISSUE = "https://github.com/o/r/issues/9"

    def setUp(self):
        self.a = feature("a", ["spec.ownership.a.legality-1"])
        self.old = feature("old", ["spec.ownership.o.legality-1"], introduced="v0.15.0")
        self.bulk = [{"release": "v0.16.0", "tier": "A", "reason": "sweep", "issue": self.ISSUE}]

    def test_open_tier_a_cell_of_the_release_is_deferred(self):
        cell = apply_bulk(evaluate_pair(self.a, self.old, [], {}, set()), self.bulk)
        self.assertEqual((cell.status, cell.bulk, cell.issue), ("deferred", True, self.ISSUE))
        self.assertEqual(gate_blockers([cell]), [])

    def test_fixture_evidence_wins_over_the_bulk_deferral(self):
        fixtures = [Fixture("one", frozenset({"spec.ownership.a.legality-1", "spec.ownership.o.legality-1"}))]
        cell = apply_bulk(evaluate_pair(self.a, self.old, fixtures, {}, set()), self.bulk)
        self.assertEqual((cell.status, cell.bulk), ("covered", False))

    def test_other_release_or_tier_is_not_deferred(self):
        old2 = feature("old2", ["spec.ownership.p.legality-1"], introduced="v0.14.0")
        cell = apply_bulk(evaluate_pair(old2, self.old, [], {}, set()), self.bulk)
        self.assertEqual(cell.status, "open")
        other_tier = [{**self.bulk[0], "tier": "B"}]
        self.assertEqual(apply_bulk(evaluate_pair(self.a, self.old, [], {}, set()), other_tier).status, "open")

    def test_bulk_entry_needs_an_issue_and_a_reason(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "states.toml"
            path.write_text('[[bulk]]\nrelease = "v0.16.0"\ntier = "A"\nreason = "x"\n')
            with self.assertRaisesRegex(ValueError, "GitHub issue URL"):
                load_bulk(path)


class Metrics(unittest.TestCase):
    def setUp(self):
        self.new_a = feature("a", ["spec.ownership.a.legality-1", "spec.ownership.a.legality-2"])
        self.new_b = feature("b", ["spec.ownership.b.legality-1"])
        self.old = feature("old", ["spec.ownership.o.legality-1"], introduced="v0.15.0")
        self.features = {f.id: f for f in (self.new_a, self.new_b, self.old)}
        self.fixtures = [Fixture("one", frozenset({"spec.ownership.a.legality-1", "spec.ownership.b.legality-1"}))]

    def metrics(self, bulk=()):
        return compute_metrics("v0.16.0", self.features, self.fixtures, {}, set(), list(bulk))

    def test_new_by_new_and_new_by_older_are_counted_apart(self):
        m = self.metrics()
        self.assertEqual(m["new_by_new"]["A"]["pairs"], 1)
        self.assertEqual(m["new_by_new"]["A"]["partial"], 1)
        self.assertEqual(m["new_by_older"]["A"]["pairs"], 2)
        self.assertEqual(m["new_by_older"]["A"]["open"], 2)

    def test_bulk_deferral_is_reported_apart_from_computed_evidence(self):
        bulk = [{"release": "v0.16.0", "tier": "A", "reason": "r", "issue": "https://github.com/o/r/issues/1"}]
        m = self.metrics(bulk)
        self.assertEqual(m["new_by_older"]["A"]["open"], 2)
        self.assertEqual(m["gate"]["tier_a_bulk_deferred"], 2)
        self.assertEqual(m["gate"]["verdict"], "PASS")
        self.assertEqual(self.metrics()["gate"]["verdict"], "BLOCKED")

    def test_rule_coverage_counts_owned_and_cited_rules(self):
        self.assertEqual(self.metrics()["rules"], {"owned": 3, "cited": 2})

    def test_table_is_marked_and_lists_the_features_on_request(self):
        table = render_table(self.metrics(), per_feature=True)
        self.assertTrue(table.startswith(TABLE_START))
        self.assertTrue(table.rstrip().endswith(TABLE_END))
        self.assertIn("| A |", table.replace("A (same subsystem)", "A"))

    def test_check_table_accepts_a_current_table_and_rejects_a_missing_or_stale_one(self):
        expected = render_table(self.metrics())
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "changelog.md"
            path.write_text(f"## v0.16.0 (unreleased)\n\ntext\n\n{expected}\n## v0.15.0\n\nolder\n")
            self.assertIsNone(check_table(path, "v0.16.0", expected))
            path.write_text("## v0.16.0 (unreleased)\n\ntext\n\n## v0.15.0\n")
            self.assertIn("no feature-matrix table", check_table(path, "v0.16.0", expected))
            path.write_text(f"## v0.16.0\n\n{expected.replace('1 (', '2 (')}\n## v0.15.0\n")
            self.assertIn("stale", check_table(path, "v0.16.0", expected))
            self.assertIn("no `## v0.17.0` section", check_table(path, "v0.17.0", expected))


class RegistryValidation(unittest.TestCase):
    def test_rejects_unknown_rule_format(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "registry.toml"
            path.write_text('''[[features]]\nid = "x"\nname = "X"\nintroduced = "v0.16.0"\nsource = ["test"]\nsubsystems = ["ownership"]\nrules = ["not-a-spec-id"]\n''')
            with self.assertRaisesRegex(ValueError, "invalid spec rule"):
                load_registry(path)

    def test_deferred_state_requires_issue_link(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "states.toml"
            path.write_text('''[[cells]]\nleft = "a"\nright = "b"\nstate = "deferred"\nreason = "later"\n''')
            features = {"a": feature("a", []), "b": feature("b", [])}
            with self.assertRaisesRegex(ValueError, "GitHub issue URL"):
                load_states(path, features)


if __name__ == "__main__":
    unittest.main()
