import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

from tools.feature_matrix import Feature, Fixture, evaluate_pair, load_registry, load_states


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
