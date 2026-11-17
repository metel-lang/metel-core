#!/usr/bin/env python3
"""Compute persistent feature-interaction evidence from the registry and fixtures."""

from __future__ import annotations

import argparse
import itertools
import re
import sys
import tomllib
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_REGISTRY = ROOT / "tools/feature-matrix/registry.toml"
DEFAULT_STATES = ROOT / "tools/feature-matrix/states.toml"
DEFAULT_FIXTURES = ROOT / "metel-interpreter/tests/integration/sources"
DEFAULT_SPEC = ROOT / "docs/reference/spec"
RULE_RE = re.compile(r"^spec\.[a-z0-9_.-]+\.(?:legality|dynamics)-\d+$")


@dataclass(frozen=True)
class Feature:
    id: str
    name: str
    introduced: str
    source: tuple[str, ...]
    subsystems: frozenset[str]
    rules: frozenset[str]


@dataclass(frozen=True)
class Fixture:
    path: str
    rules: frozenset[str]


@dataclass(frozen=True)
class Cell:
    left: Feature
    right: Feature
    tier: str
    status: str
    score: Fraction | None
    evidence: tuple[str, ...]
    cited_rules: frozenset[str]
    reason: str = ""
    issue: str = ""


def load_toml(path: Path) -> dict:
    try:
        with path.open("rb") as stream:
            return tomllib.load(stream)
    except (OSError, tomllib.TOMLDecodeError) as exc:
        raise ValueError(f"cannot read TOML {path}: {exc}") from exc


def load_registry(path: Path) -> tuple[dict[str, Feature], set[tuple[str, str]]]:
    raw = load_toml(path)
    declared_subsystems = set(raw.get("subsystems", []))
    features: dict[str, Feature] = {}
    for entry in raw.get("features", []):
        feature = Feature(
            id=entry.get("id", ""),
            name=entry.get("name", ""),
            introduced=entry.get("introduced", ""),
            source=tuple(entry.get("source", [])),
            subsystems=frozenset(entry.get("subsystems", [])),
            rules=frozenset(entry.get("rules", [])),
        )
        if not feature.id or feature.id in features:
            raise ValueError(f"missing or duplicate feature id: {feature.id!r}")
        if not feature.name or not feature.introduced or not feature.source:
            raise ValueError(f"{feature.id}: name, introduced, and source are required")
        if feature.introduced != "unresolved" and not re.fullmatch(r"v\d+\.\d+\.\d+", feature.introduced):
            raise ValueError(f"{feature.id}: introduced must be a version or 'unresolved'")
        if not feature.subsystems:
            raise ValueError(f"{feature.id}: at least one subsystem tag is required")
        if declared_subsystems and not feature.subsystems <= declared_subsystems:
            unknown = sorted(feature.subsystems - declared_subsystems)
            raise ValueError(f"{feature.id}: unknown subsystem tag(s): {', '.join(unknown)}")
        invalid = sorted(rule for rule in feature.rules if not RULE_RE.fullmatch(rule))
        if invalid:
            raise ValueError(f"{feature.id}: invalid spec rule id(s): {', '.join(invalid)}")
        features[feature.id] = feature
    adjacency = {
        tuple(sorted((entry["left"], entry["right"])))
        for entry in raw.get("adjacent_subsystems", [])
    }
    known_subsystems = declared_subsystems or {tag for f in features.values() for tag in f.subsystems}
    unknown = sorted({tag for pair in adjacency for tag in pair} - known_subsystems)
    if unknown:
        raise ValueError(f"adjacency refers to unknown subsystem tag(s): {', '.join(unknown)}")
    return features, adjacency


def load_states(path: Path, features: dict[str, Feature]) -> dict[tuple[str, str], dict[str, str]]:
    raw = load_toml(path)
    result: dict[tuple[str, str], dict[str, str]] = {}
    for entry in raw.get("cells", []):
        left, right = entry.get("left", ""), entry.get("right", "")
        if left not in features or right not in features or left == right:
            raise ValueError(f"state entry has unknown or identical feature ids: {left!r}, {right!r}")
        pair = tuple(sorted((left, right)))
        if pair in result:
            raise ValueError(f"duplicate hand-set cell state: {pair[0]} × {pair[1]}")
        state = entry.get("state", "")
        if state not in {"n/a", "deferred"}:
            raise ValueError(f"{pair[0]} × {pair[1]}: state must be n/a or deferred")
        reason = entry.get("reason", "").strip()
        issue = entry.get("issue", "").strip()
        if not reason:
            raise ValueError(f"{pair[0]} × {pair[1]}: {state} requires a reason")
        if state == "deferred" and not re.search(r"https://github\.com/.+/issues/\d+", issue):
            raise ValueError(f"{pair[0]} × {pair[1]}: deferred state requires a GitHub issue URL")
        result[pair] = {"state": state, "reason": reason, "issue": issue}
    return result


def load_fixtures(root: Path) -> list[Fixture]:
    fixtures: list[Fixture] = []
    for path in sorted(root.rglob("*.toml")):
        if path.name == "test.toml":
            continue
        raw = load_toml(path)
        rules = raw.get("spec", raw.get("options", {}).get("spec", []))
        if not isinstance(rules, list) or not all(isinstance(rule, str) for rule in rules):
            raise ValueError(f"{path}: spec must be an array of rule ids")
        rel = path.relative_to(root).with_suffix("").as_posix()
        fixtures.append(Fixture(rel, frozenset(rules)))
    # Group fixtures use test.toml metadata and source files in the same directory.
    for path in sorted(root.rglob("test.toml")):
        raw = load_toml(path)
        rules = raw.get("spec", raw.get("options", {}).get("spec", []))
        if not isinstance(rules, list) or not all(isinstance(rule, str) for rule in rules):
            raise ValueError(f"{path}: spec must be an array of rule ids")
        if not any(p.suffix == ".mtl" for p in path.parent.iterdir()):
            continue
        rel = path.parent.relative_to(root).as_posix()
        fixtures.append(Fixture(rel, frozenset(rules)))
    return fixtures


def validate_spec_rules(features: dict[str, Feature], fixtures: list[Fixture], spec_root: Path) -> None:
    spec_rule_re = re.compile(r"\b(spec\.[a-z0-9_.-]+\.(?:legality|dynamics)-\d+)\b")
    actual = {
        rule for path in spec_root.rglob("*.md")
        for rule in spec_rule_re.findall(path.read_text(encoding="utf-8"))
    }
    declared = {rule for feature in features.values() for rule in feature.rules}
    fixture_rules = {rule for fixture in fixtures for rule in fixture.rules}
    unknown = sorted((declared | fixture_rules) - actual)
    if unknown:
        raise ValueError("unknown spec rule id(s): " + ", ".join(unknown))


def pair_tier(left: Feature, right: Feature, adjacent: set[tuple[str, str]]) -> str:
    if left.subsystems & right.subsystems:
        return "A"
    if any(tuple(sorted((a, b))) in adjacent for a in left.subsystems for b in right.subsystems):
        return "B"
    return "C"


def evaluate_pair(
    left: Feature,
    right: Feature,
    fixtures: list[Fixture],
    states: dict[tuple[str, str], dict[str, str]],
    adjacent: set[tuple[str, str]],
) -> Cell:
    pair_key = tuple(sorted((left.id, right.id)))
    tier = pair_tier(left, right, adjacent)
    manual = states.get(pair_key)
    if manual:
        return Cell(left, right, tier, manual["state"], None, (), frozenset(), manual["reason"], manual["issue"])

    left_rules, right_rules = left.rules, right.rules
    matches: list[Fixture] = []
    cited: set[str] = set()
    for fixture in fixtures:
        if fixture.rules & left_rules and fixture.rules & right_rules:
            matches.append(fixture)
            cited.update(fixture.rules & (left_rules | right_rules))
    denominator = left_rules | right_rules
    if not denominator:
        score = None
        status = "open"
    else:
        score = Fraction(len(cited), len(denominator))
        status = "open" if score == 0 else "partial" if score < 1 else "covered"
    return Cell(
        left, right, tier, status, score,
        tuple(f.path for f in matches), frozenset(cited),
    )


def select_cells(
    release: str,
    features: dict[str, Feature],
    fixtures: list[Fixture],
    states: dict[tuple[str, str], dict[str, str]],
    adjacent: set[tuple[str, str]],
) -> tuple[list[Cell], list[Feature]]:
    current = sorted((f for f in features.values() if f.introduced == release), key=lambda f: f.id)
    if not current:
        raise ValueError(f"registry has no features introduced in {release}")
    all_features = sorted(features.values(), key=lambda f: f.id)
    cells = [evaluate_pair(a, b, fixtures, states, adjacent)
             for a, b in itertools.combinations(all_features, 2)
             if a.introduced == release or b.introduced == release]
    return cells, current


def render(
    release: str,
    cells: list[Cell],
    features: list[Feature],
    details: bool = False,
    blockers_only: bool = False,
) -> str:
    within_release = [c for c in cells if c.left.introduced == release and c.right.introduced == release]
    counts = {status: sum(c.status == status for c in within_release) for status in ("covered", "partial", "open", "n/a", "deferred")}
    risk = [c for c in cells if c.tier in {"A", "B"}]
    high_gaps = sum(c.tier == "A" and c.status == "open" for c in within_release)
    high_risk_gaps = sum(c.tier in {"A", "B"} and c.status == "open" for c in within_release)
    blockers = [c for c in cells if c.tier == "A" and c.status in {"open", "partial"}]
    scored = [c.score for c in within_release if c.score is not None]
    mean_score = sum(scored, Fraction()) / len(scored) if scored else None
    lines = [
        f"Feature matrix for {release}",
        f"Milestone-only baseline: {len(features)} features · {len(within_release)} pairs · evidence in "
        f"{counts['covered'] + counts['partial']} pairs ({counts['covered']} complete, {counts['partial']} partial) · "
        f"no evidence: {counts['open']} · mean rule coverage: {float(mean_score):.1%}" if mean_score is not None else "no scoreable pairs",
        f"Baseline Tier A open gaps: {high_gaps} · Tier A/B open gaps: {high_risk_gaps}",
        f"Release gate scope: {len(cells)} new-vs-registry pairs · "
        f"Tier A/B pairs: {len(risk)} · Tier A blockers (open or partial): {len(blockers)}",
    ]
    if details or blockers_only:
        visible = cells if details else blockers
        lines += ["", "| Feature A | Feature B | Tier | Rule coverage | State | Fixtures / disposition |",
                  "|---|---|:---:|---:|---|---|"]
        for cell in visible:
            score = "—" if cell.score is None else f"{len(cell.cited_rules)}/{len(cell.left.rules | cell.right.rules)} ({float(cell.score):.0%})"
            evidence = ", ".join(f"`{path}`" for path in cell.evidence) or cell.issue or cell.reason or "—"
            lines.append(f"| {cell.left.name} | {cell.right.name} | {cell.tier} | {score} | {cell.status} | {evidence} |")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("release", help="release identifier, e.g. v0.16.0")
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY)
    parser.add_argument("--states", type=Path, default=DEFAULT_STATES)
    parser.add_argument("--fixtures", type=Path, default=DEFAULT_FIXTURES)
    parser.add_argument("--spec", type=Path, default=DEFAULT_SPEC)
    parser.add_argument("--details", action="store_true", help="print every new-feature pair")
    parser.add_argument("--blockers", action="store_true", help="print only blocking Tier A cells")
    args = parser.parse_args(argv)
    try:
        features, adjacent = load_registry(args.registry)
        states = load_states(args.states, features)
        fixtures = load_fixtures(args.fixtures)
        validate_spec_rules(features, fixtures, args.spec)
        cells, current = select_cells(args.release, features, fixtures, states, adjacent)
        sys.stdout.write(render(args.release, cells, current, args.details, args.blockers))
        missing = sorted(feature.id for feature in features.values() if not feature.rules)
        unresolved = sorted(feature.id for feature in features.values() if feature.introduced == "unresolved")
        print(f"Registry: {len(features)} features · {len(missing)} without spec rule IDs · {len(unresolved)} unresolved introduction releases")
        if missing:
            print("Features without spec rules: " + ", ".join(missing))
        if unresolved:
            print("Features with unresolved introductions: " + ", ".join(unresolved))
        blockers = [c for c in cells if c.tier == "A" and c.status in {"open", "partial"}]
        print(f"Gate: {'BLOCKED' if blockers else 'PASS'} ({len(blockers)} Tier A cells need full rule coverage)")
        return 1 if blockers else 0
    except ValueError as exc:
        print(f"feature-matrix: error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
