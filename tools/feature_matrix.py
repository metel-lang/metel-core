#!/usr/bin/env python3
"""Compute persistent feature-interaction evidence from the registry and fixtures."""

from __future__ import annotations

import argparse
import itertools
import json
import re
import sys
import tomllib
from dataclasses import dataclass, replace
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
    stage: str = ""


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
    bulk: bool = False


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
            stage=entry.get("stage", ""),
        )
        if not feature.id or feature.id in features:
            raise ValueError(f"missing or duplicate feature id: {feature.id!r}")
        if not feature.name or not feature.introduced or not feature.source:
            raise ValueError(f"{feature.id}: name, introduced, and source are required")
        if feature.introduced != "unresolved" and not re.fullmatch(r"v\d+\.\d+\.\d+", feature.introduced):
            raise ValueError(f"{feature.id}: introduced must be a version or 'unresolved'")
        if not feature.subsystems:
            raise ValueError(f"{feature.id}: at least one subsystem tag is required")
        if not isinstance(feature.stage, str):
            raise ValueError(f"{feature.id}: stage must be a string")
        if feature.stage and feature.introduced == "unresolved":
            raise ValueError(f"{feature.id}: a feature with a stage must name the release it is introduced in")
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


def load_bulk(path: Path) -> list[dict[str, str]]:
    """Bulk deferrals: every still-open cell of a tier for a release goes to one tracking issue."""
    bulk = []
    for entry in load_toml(path).get("bulk", []):
        release, tier = entry.get("release", ""), entry.get("tier", "")
        reason, issue = entry.get("reason", "").strip(), entry.get("issue", "").strip()
        if not re.fullmatch(r"v\d+\.\d+\.\d+", release) or tier not in {"A", "B", "C"}:
            raise ValueError(f"bulk deferral needs a release version and a tier A, B or C: {entry!r}")
        if not reason or not re.search(r"https://github\.com/.+/issues/\d+", issue):
            raise ValueError(f"bulk deferral for {release} tier {tier} needs a reason and a GitHub issue URL")
        bulk.append({"release": release, "tier": tier, "reason": reason, "issue": issue})
    return bulk


def apply_bulk(cell: Cell, bulk: list[dict[str, str]], release: str | None = None) -> Cell:
    """A bulk deferral covers only cells that are still open; fixture evidence always wins.

    It applies to the release it names, never to a later one (a later release's gate has its own cells)."""
    if cell.status != "open":
        return cell
    for entry in bulk:
        if release is not None and entry["release"] != release:
            continue
        if entry["tier"] == cell.tier and entry["release"] in {cell.left.introduced, cell.right.introduced}:
            return replace(cell, status="deferred", reason=entry["reason"], issue=entry["issue"], bulk=True)
    return cell


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
    bulk: list[dict[str, str]] | None = None,
) -> tuple[list[Cell], list[Feature]]:
    current = sorted((f for f in features.values() if f.introduced == release), key=lambda f: f.id)
    if not current:
        raise ValueError(f"registry has no features introduced in {release}")
    all_features = sorted(features.values(), key=lambda f: f.id)
    cells = [apply_bulk(evaluate_pair(a, b, fixtures, states, adjacent), bulk or [], release)
             for a, b in itertools.combinations(all_features, 2)
             if a.introduced == release or b.introduced == release]
    return cells, current


GATE_DEFAULTS = {"min_joint_fixtures": 2, "feature_tier_a_floor": 0.5, "tier_b_open_fails": True}


@dataclass(frozen=True)
class Violation:
    rule: str
    detail: str


def scope_to_stages(features: dict[str, Feature], release: str, stages: list[str] | None) -> dict[str, Feature]:
    """The registry as a stage gate sees it (`/stage-gate`): the features introduced in `release` whose stage is in
    `stages`, together with every feature of any other release. A stage gate is cumulative: `stages` names the stage
    being gated and every stage already gated, so a later stage's features, which are not done, are left out and
    cannot block it. `stages` of None is the whole release, which is the final gate.

    A staged release needs every one of its features to name its stage; one that does not has no place in a scoped
    gate, which is an error rather than a silent omission."""
    if stages is None:
        return features
    wanted = set(stages)
    unstaged = sorted(f.id for f in features.values() if f.introduced == release and not f.stage)
    if unstaged:
        raise ValueError(
            f"{release} features without a stage: {', '.join(unstaged)} "
            "(a scoped gate needs every feature of the release to name its stage)")
    return {i: f for i, f in features.items() if f.introduced != release or f.stage in wanted}


def load_gate_config(path: Path) -> dict:
    """The gate's thresholds, from the registry's `[gate]` table; a release can raise them."""
    raw = load_toml(path).get("gate", {})
    unknown = sorted(set(raw) - set(GATE_DEFAULTS))
    if unknown:
        raise ValueError(f"unknown [gate] setting(s): {', '.join(unknown)}")
    return {**GATE_DEFAULTS, **raw}


def _minor(version: str) -> tuple[int, int]:
    major, minor, _ = (int(part) for part in version.lstrip("v").split("."))
    return major, minor


def gate_violations(
    release: str,
    features: dict[str, Feature],
    fixtures: list[Fixture],
    states: dict[tuple[str, str], dict[str, str]],
    adjacent: set[tuple[str, str]],
    bulk: list[dict[str, str]],
    config: dict,
) -> list[Violation]:
    """Everything that fails the gate for `release` (ADR-0069). Computed evidence is judged without the bulk
    deferral, which excuses only the open-Tier-A rule."""
    raw, current = select_cells(release, features, fixtures, states, adjacent)
    gated, _ = select_cells(release, features, fixtures, states, adjacent, bulk)
    found: list[Violation] = []

    def pair(c: Cell) -> str:
        return f"{c.left.name} × {c.right.name}"

    for c in gate_blockers(gated):
        found.append(Violation("open-tier-a", f"{pair(c)}: no joint fixture, no n/a reason, no deferral issue"))
    own = [c for c in raw if c.left.introduced == c.right.introduced == release]
    for c in own:
        if c.tier == "A" and c.status in {"covered", "partial", "open"} and len(c.evidence) < config["min_joint_fixtures"]:
            found.append(Violation(
                "joint-fixtures",
                f"{pair(c)}: {len(c.evidence)} joint fixture(s), needs {config['min_joint_fixtures']}"))
        if c.tier == "B" and c.status == "open" and config["tier_b_open_fails"]:
            found.append(Violation("tier-b-evidence", f"{pair(c)}: no joint fixture and no n/a reason"))
    floor = config["feature_tier_a_floor"]
    for feature in current:
        tier_a = [c for c in raw if feature.id in {c.left.id, c.right.id} and c.tier == "A" and c.status != "n/a"]
        with_evidence = sum(c.status in {"covered", "partial"} for c in tier_a)
        if tier_a and with_evidence / len(tier_a) < floor:
            found.append(Violation(
                "feature-floor",
                f"{feature.name}: evidence in {with_evidence} of {len(tier_a)} Tier A pairs, needs {floor:.0%}"))
    for entry in bulk:
        if _minor(entry["release"]) < _minor(release):
            older, _ = select_cells(entry["release"], features, fixtures, states, adjacent)
            still_open = sum(c.tier == entry["tier"] and c.status == "open" for c in older)
            if still_open:
                found.append(Violation(
                    "expired-bulk",
                    f"the {entry['release']} tier {entry['tier']} bulk deferral ({entry['issue']}) expired: "
                    f"{still_open} cell(s) are still open"))
    return found


def gate_blockers(cells: list[Cell]) -> list[Cell]:
    """Open Tier A cells fail the gate. Partial coverage is reported and never blocks (#2082 ADR)."""
    return [c for c in cells if c.tier == "A" and c.status == "open"]


TABLE_START = "<!-- feature-matrix:start -->"
TABLE_END = "<!-- feature-matrix:end -->"
TIERS = ("A", "B", "C")


def _tier_row(cells: list[Cell]) -> dict:
    scored = [c.score for c in cells if c.score is not None]
    mean = sum(scored, Fraction()) / len(scored) if scored else Fraction()
    return {
        "pairs": len(cells),
        "covered": sum(c.status == "covered" for c in cells),
        "partial": sum(c.status == "partial" for c in cells),
        "open": sum(c.status == "open" for c in cells),
        "n/a": sum(c.status == "n/a" for c in cells),
        "deferred": sum(c.status == "deferred" for c in cells),
        "with_evidence": sum(c.status in {"covered", "partial"} for c in cells),
        "mean_rule_coverage": round(float(mean), 4),
    }


def compute_metrics(
    release: str,
    features: dict[str, Feature],
    fixtures: list[Fixture],
    states: dict[tuple[str, str], dict[str, str]],
    adjacent: set[tuple[str, str]],
    bulk: list[dict[str, str]],
    config: dict | None = None,
) -> dict:
    """The release's coverage metrics. Evidence is computed from fixtures; a bulk deferral is reported apart."""
    raw, current = select_cells(release, features, fixtures, states, adjacent)
    gated, _ = select_cells(release, features, fixtures, states, adjacent, bulk)
    new_by_new = [c for c in raw if c.left.introduced == c.right.introduced == release]
    new_by_older = [c for c in raw if not (c.left.introduced == c.right.introduced == release)]
    owned = set().union(*(f.rules for f in current))
    cited = set().union(*(fixture.rules for fixture in fixtures))
    blockers = gate_blockers(gated)
    violations = gate_violations(release, features, fixtures, states, adjacent, bulk, config or GATE_DEFAULTS)
    by_rule: dict[str, int] = {}
    for violation in violations:
        by_rule[violation.rule] = by_rule.get(violation.rule, 0) + 1
    per_feature = []
    for feature in current:
        tier_a = [c for c in raw if feature.id in {c.left.id, c.right.id} and c.tier == "A"]
        per_feature.append({
            "id": feature.id,
            "name": feature.name,
            "rules_owned": len(feature.rules),
            "rules_cited": len(feature.rules & cited),
            "tier_a_pairs": len(tier_a),
            "tier_a_with_evidence": sum(c.status in {"covered", "partial"} for c in tier_a),
        })
    return {
        "release": release,
        "features": len(current),
        "registry_features": len(features),
        "fixtures": len(fixtures),
        "new_by_new": {**{t: _tier_row([c for c in new_by_new if c.tier == t]) for t in TIERS},
                       "all": _tier_row(new_by_new)},
        "new_by_older": {**{t: _tier_row([c for c in new_by_older if c.tier == t]) for t in TIERS},
                         "all": _tier_row(new_by_older)},
        "rules": {"owned": len(owned), "cited": len(owned & cited)},
        "gate": {
            "verdict": "BLOCKED" if violations else "PASS",
            "violations": by_rule,
            "tier_a_open": len(blockers),
            "tier_a_partial": sum(c.tier == "A" and c.status == "partial" for c in gated),
            "tier_a_bulk_deferred": sum(c.tier == "A" and c.bulk for c in gated),
        },
        "per_feature": per_feature,
    }


def render_table(metrics: dict, per_feature: bool = False) -> str:
    """The markdown table published with a release, between the markers `--check-table` looks for."""
    def pct(part: int, whole: int) -> str:
        return f"{part / whole:.0%}" if whole else "n/a"

    def rows(group: dict) -> list[str]:
        out = []
        for tier, label in (("A", "A (same subsystem)"), ("B", "B (adjacent)"), ("C", "C (other)"), ("all", "**All**")):
            r = group[tier]
            out.append(
                f"| {label} | {r['pairs']} | {r['with_evidence']} ({pct(r['with_evidence'], r['pairs'])}) | "
                f"{r['covered']} | {r['partial']} | {r['open']} | {r['mean_rule_coverage']:.1%} |"
            )
        return out

    head = ("| Tier | Pairs | With evidence | Covered | Partial | Open | Mean rule coverage |\n"
            "|---|---:|---:|---:|---:|---:|---:|")
    gate = metrics["gate"]
    rules = metrics["rules"]
    lines = [
        TABLE_START,
        f"**Feature-interaction coverage for {metrics['release']}** "
        f"({metrics['features']} new features, a registry of {metrics['registry_features']}). "
        f"A pair has evidence when a fixture cites a rule of each feature.",
        "",
        "*New features against each other*", "", head, *rows(metrics["new_by_new"]), "",
        "*New features against older ones*", "", head, *rows(metrics["new_by_older"]), "",
        f"Rules owned by the new features: {rules['owned']}, cited by at least one fixture: "
        f"{rules['cited']} ({pct(rules['cited'], rules['owned'])}).",
        f"Release gate: **{gate['verdict']}**. Open Tier A cells: {gate['tier_a_open']}, "
        f"partial: {gate['tier_a_partial']}, bulk-deferred: {gate['tier_a_bulk_deferred']}. "
        + ("Violations: " + ", ".join(f"{rule} {n}" for rule, n in sorted(gate["violations"].items())) + "."
           if gate["violations"] else "No gate violations."),
    ]
    if per_feature:
        lines += ["", "| Feature | Rules cited / owned | Tier A pairs with evidence |", "|---|---:|---:|"]
        for f in metrics["per_feature"]:
            lines.append(f"| {f['name']} | {f['rules_cited']}/{f['rules_owned']} | "
                         f"{f['tier_a_with_evidence']}/{f['tier_a_pairs']} |")
    lines.append(TABLE_END)
    return "\n".join(lines) + "\n"


def check_table(path: Path, release: str, expected: str) -> str | None:
    """None when the file's `## <release>` section holds the table, else why it does not."""
    text = path.read_text(encoding="utf-8")
    match = re.search(rf"^## {re.escape(release)}\b.*?(?=^## v|\Z)", text, re.S | re.M)
    if not match:
        return f"{path}: no `## {release}` section"
    section = match.group(0)
    if TABLE_START not in section or TABLE_END not in section:
        return f"{path}: the {release} section has no feature-matrix table (markers {TABLE_START} … {TABLE_END})"
    published = section[section.index(TABLE_START): section.index(TABLE_END) + len(TABLE_END)]
    if published.strip() != expected.strip():
        return f"{path}: the {release} feature-matrix table is stale; regenerate it with `--table`"
    return None


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
    blockers = gate_blockers(cells)
    partial_a = sum(c.tier == "A" and c.status == "partial" for c in cells)
    bulk_a = sum(c.tier == "A" and c.bulk for c in cells)
    scored = [c.score for c in within_release if c.score is not None]
    mean_score = sum(scored, Fraction()) / len(scored) if scored else None
    lines = [
        f"Feature matrix for {release}",
        f"Milestone-only baseline: {len(features)} features · {len(within_release)} pairs · evidence in "
        f"{counts['covered'] + counts['partial']} pairs ({counts['covered']} complete, {counts['partial']} partial) · "
        f"no evidence: {counts['open']} · mean rule coverage: {float(mean_score):.1%}" if mean_score is not None else "no scoreable pairs",
        f"Baseline Tier A open gaps: {high_gaps} · Tier A/B open gaps: {high_risk_gaps}",
        f"Release gate scope: {len(cells)} new-vs-registry pairs · "
        f"Tier A/B pairs: {len(risk)} · Tier A open (blocking): {len(blockers)} · Tier A partial (reported): {partial_a} · Tier A bulk-deferred: {bulk_a}",
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
    parser.add_argument("--stage", action="append", metavar="NAME",
                        help="gate only the features of this stage of the release, and of every other --stage given "
                             "(a stage gate is cumulative); omit for the whole release")
    parser.add_argument("--details", action="store_true", help="print every new-feature pair")
    parser.add_argument("--blockers", action="store_true", help="print only the Tier A cells that block the gate (open)")
    parser.add_argument("--json", action="store_true", help="print the release's metrics as JSON, for the per-release snapshot")
    parser.add_argument("--table", action="store_true", help="print the markdown metrics table published with a release")
    parser.add_argument("--per-feature", action="store_true", help="with --table, add the per-feature rows")
    parser.add_argument("--check-table", type=Path, metavar="FILE",
                        help="fail unless FILE's section for the release holds the current --table output")
    args = parser.parse_args(argv)
    try:
        features, adjacent = load_registry(args.registry)
        states = load_states(args.states, features)
        fixtures = load_fixtures(args.fixtures)
        validate_spec_rules(features, fixtures, args.spec)
        features = scope_to_stages(features, args.release, args.stage)
        for name in args.stage or []:
            if not any(f.stage == name and f.introduced == args.release for f in features.values()):
                print(f"feature-matrix: note: no feature of {args.release} carries stage {name!r} "
                      "(a design-only stage has none)", file=sys.stderr)
        bulk = load_bulk(args.states)
        config = load_gate_config(args.registry)
        if args.json or args.table or args.check_table:
            metrics = compute_metrics(args.release, features, fixtures, states, adjacent, bulk, config)
            if args.json:
                sys.stdout.write(json.dumps(metrics, indent=2) + "\n")
            if args.table:
                sys.stdout.write(render_table(metrics, args.per_feature))
            if args.check_table:
                problem = check_table(args.check_table, args.release, render_table(metrics))
                if problem:
                    print(f"feature-matrix: {problem}", file=sys.stderr)
                    return 1
                print(f"feature-matrix: {args.check_table} holds the current table for {args.release}")
            return 0
        cells, current = select_cells(args.release, features, fixtures, states, adjacent, load_bulk(args.states))
        sys.stdout.write(render(args.release, cells, current, args.details, args.blockers))
        missing = sorted(feature.id for feature in features.values() if not feature.rules)
        unresolved = sorted(feature.id for feature in features.values() if feature.introduced == "unresolved")
        print(f"Registry: {len(features)} features · {len(missing)} without spec rule IDs · {len(unresolved)} unresolved introduction releases")
        if missing:
            print("Features without spec rules: " + ", ".join(missing))
        if unresolved:
            print("Features with unresolved introductions: " + ", ".join(unresolved))
        violations = gate_violations(args.release, features, fixtures, states, adjacent, bulk, config)
        by_rule: dict[str, int] = {}
        for violation in violations:
            by_rule[violation.rule] = by_rule.get(violation.rule, 0) + 1
        if args.blockers:
            print("\n| Rule | Detail |\n|---|---|")
            for violation in violations:
                print(f"| {violation.rule} | {violation.detail} |")
        summary = ", ".join(f"{rule} {n}" for rule, n in sorted(by_rule.items()))
        print(f"Gate: {'BLOCKED' if violations else 'PASS'} ({len(violations)} violation(s){': ' + summary if summary else ''})")
        return 1 if violations else 0
    except ValueError as exc:
        print(f"feature-matrix: error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
