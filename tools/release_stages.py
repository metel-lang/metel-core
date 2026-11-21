#!/usr/bin/env python3
"""A staged release and its stages (ROADMAP.md, "How milestones work"; metel-core#2130).

A staged release is a numbered milestone plus theme milestones called stages. The link runs both ways and this
script is the one place that reads it:

  * a stage says `Part of: vX.Y.Z` on its own line in its description, and carries the tag `[vX.Y.Z] ` in its title;
  * the release milestone lists its stages in a `Stages:` block, one `- <exact stage title>` per line.

A stage is gated when it completes (`/stage-gate`): its milestone is then closed, and its report in
`docs/release-notes/integration/vX.Y.Z/stage-<slug>.md` reads `**Result:** PASS`.

    release_stages.py list  vX.Y.Z           the stages in order: open issues, state, gate report
    release_stages.py open  vX.Y.Z           the open issues of the release milestone and of each stage
    release_stages.py check vX.Y.Z [--gated] the two links agree; with --gated, every stage is closed and gated
    release_stages.py scope vX.Y.Z STAGE     the stage names for `feature_matrix.py --stage`: STAGE and the stages
                                             already gated (a stage gate is cumulative)

`gh` must be authenticated. Exit status 1 when `check` finds a problem.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

REPO = "metel-lang/metel-core"
DEFAULT_REPORTS = Path("docs/release-notes/integration")
VERSION = r"v\d+\.\d+\.\d+"
PART_OF_RE = re.compile(rf"^Part of: ({VERSION})$")
TAG_RE = re.compile(rf"^\[({VERSION})\] (.+)$")
PASS_RE = re.compile(r"^\*\*Result:\*\*\s*PASS\b", re.MULTILINE)


@dataclass(frozen=True)
class Milestone:
    title: str
    description: str = ""
    state: str = "open"
    open_issues: int = 0
    due_on: str = ""


def description_lines(description: str) -> list[str]:
    return [line.rstrip("\r") for line in (description or "").split("\n")]


def part_of(description: str) -> str | None:
    """The release a stage declares, from its exact `Part of: vX.Y.Z` line."""
    for line in description_lines(description):
        match = PART_OF_RE.match(line)
        if match:
            return match.group(1)
    return None


def listed_stages(description: str) -> list[str]:
    """The stage titles under the release's `Stages:` line: the `- ` lines that follow it."""
    lines = description_lines(description)
    if "Stages:" not in lines:
        return []
    titles: list[str] = []
    for line in lines[lines.index("Stages:") + 1:]:
        if not line.startswith("- "):
            break
        titles.append(line[2:].strip())
    return titles


def stage_name(title: str) -> str:
    """A stage's title without its `[vX.Y.Z] ` tag: the name the registry's `stage` field uses."""
    match = TAG_RE.match(title)
    return match.group(2) if match else title


def slug(name: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-")


def report_path(reports: Path, version: str, name: str) -> Path:
    return reports / version / f"stage-{slug(name)}.md"


def report_passes(reports: Path, version: str, name: str) -> bool:
    try:
        return bool(PASS_RE.search(report_path(reports, version, name).read_text()))
    except OSError:
        return False


def declared_stages(version: str, milestones: list[Milestone]) -> list[Milestone]:
    """The stages in the release's `Stages:` order, then any that declare the release without being listed."""
    by_title = {m.title: m for m in milestones}
    release = by_title.get(version)
    listed = [by_title[t] for t in listed_stages(release.description) if t in by_title] if release else []
    extra = [m for m in milestones if part_of(m.description) == version and m not in listed]
    return listed + extra


def problems(version: str, milestones: list[Milestone], gated: bool = False, reports: Path = DEFAULT_REPORTS) -> list[str]:
    """Everything wrong with the link between a release and its stages, and with `gated` the gate state."""
    by_title = {m.title: m for m in milestones}
    release = by_title.get(version)
    if release is None:
        return [f"no milestone named {version}"]
    found: list[str] = []
    listed = listed_stages(release.description)
    declaring = [m for m in milestones if part_of(m.description) == version]
    for title in sorted({t for t in listed if listed.count(t) > 1}):
        found.append(f"{version} lists {title!r} more than once")
    for title in dict.fromkeys(listed):
        if title not in by_title:
            found.append(f"{version} lists {title!r}, which is not a milestone")
        elif part_of(by_title[title].description) != version:
            found.append(f"{version} lists {title!r}, which does not say `Part of: {version}`")
    for stage in declaring:
        if stage.title not in listed:
            found.append(f"{stage.title!r} says `Part of: {version}` but {version} does not list it under `Stages:`")
        tag = TAG_RE.match(stage.title)
        if not tag or tag.group(1) != version:
            found.append(f"{stage.title!r} is part of {version} but its title does not start with `[{version}] `")
    stages = declared_stages(version, milestones)
    dated = [(m.title, m.due_on) for m in [release, *stages] if m.due_on]
    if [d for _, d in dated] != sorted(d for _, d in dated):
        found.append("milestone due dates do not follow the release-then-stages order: "
                     + ", ".join(f"{t} ({d[:10]})" for t, d in dated))
    if gated:
        for stage in stages:
            name = stage_name(stage.title)
            if stage.state != "closed":
                found.append(f"{stage.title!r} is not closed (a stage is closed when its gate passes)")
            if stage.open_issues:
                found.append(f"{stage.title!r} has {stage.open_issues} open issue(s)")
            if not report_passes(reports, version, name):
                found.append(f"{stage.title!r} has no passing report at {report_path(reports, version, name)}")
    return found


def gated_stage_names(version: str, milestones: list[Milestone], reports: Path = DEFAULT_REPORTS) -> list[str]:
    """The names of the stages already gated: closed, with a passing report."""
    return [stage_name(m.title) for m in declared_stages(version, milestones)
            if m.state == "closed" and report_passes(reports, version, stage_name(m.title))]


def scope(version: str, milestones: list[Milestone], stage: str, reports: Path = DEFAULT_REPORTS) -> list[str]:
    """`stage` and the stages already gated, as the registry's stage names. `stage` may be a title or a name."""
    names = {stage_name(m.title): m for m in declared_stages(version, milestones)}
    wanted = stage_name(stage)
    if wanted not in names:
        raise ValueError(f"{stage!r} is not a stage of {version}; stages: {', '.join(names) or 'none'}")
    return [wanted] + [n for n in gated_stage_names(version, milestones, reports) if n != wanted]


def run(*args: str) -> str:
    result = subprocess.run(args, capture_output=True, text=True)
    if result.returncode != 0:
        raise ValueError(f"{' '.join(args[:3])} failed: {result.stderr.strip() or result.stdout.strip()}")
    return result.stdout


def fetch_milestones(repo: str) -> list[Milestone]:
    out = run("gh", "api", "--paginate", f"repos/{repo}/milestones?state=all&per_page=100", "--jq", ".[] | @json")
    milestones = []
    for line in out.splitlines():
        raw = json.loads(line)
        milestones.append(Milestone(raw["title"], raw.get("description") or "", raw["state"],
                                    raw["open_issues"], raw.get("due_on") or ""))
    return milestones


def open_issues(repo: str, title: str) -> list[str]:
    out = run("gh", "issue", "list", "-R", repo, "--milestone", title, "--state", "open", "--limit", "200",
              "--json", "number,title", "--jq", '.[] | "#\\(.number) \\(.title)"')
    return out.splitlines()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=["list", "open", "check", "scope"])
    parser.add_argument("version", help="the release, e.g. v0.17.0")
    parser.add_argument("stage", nargs="?", help="scope: the stage being gated (its title or its name)")
    parser.add_argument("--gated", action="store_true", help="check: every stage is closed and has a passing report")
    parser.add_argument("--repo", default=REPO)
    parser.add_argument("--reports", type=Path, default=DEFAULT_REPORTS, help="the integration reports directory")
    args = parser.parse_args(argv)
    if not re.fullmatch(VERSION, args.version):
        parser.error(f"{args.version!r} is not a version like v0.17.0")
    try:
        milestones = fetch_milestones(args.repo)
        release = next((m for m in milestones if m.title == args.version), None)
        if release is None:
            raise ValueError(f"no milestone named {args.version}")
        stages = declared_stages(args.version, milestones)
        if args.command == "check":
            found = problems(args.version, milestones, args.gated, args.reports)
            for line in found:
                print(f"release-stages: {line}", file=sys.stderr)
            if not found:
                print(f"release-stages: {args.version} and its {len(stages)} stage(s) agree"
                      + (" and are all gated" if args.gated else ""))
            return 1 if found else 0
        if args.command == "scope":
            if not args.stage:
                parser.error("scope needs the stage")
            print("\n".join(scope(args.version, milestones, args.stage, args.reports)))
            return 0
        if args.command == "open":
            for milestone in [release, *stages]:
                print(f"== {milestone.title}")
                print("\n".join(open_issues(args.repo, milestone.title)) or "(none)")
            return 0
        print(f"{release.title}  release milestone: {release.open_issues} open")
        for number, stage in enumerate(stages, 1):
            gate = "PASS" if report_passes(args.reports, args.version, stage_name(stage.title)) else "-"
            print(f"  {number}. {stage_name(stage.title):<36} {stage.state:<6} {stage.open_issues:>3} open   gate: {gate}")
        return 0
    except ValueError as exc:
        print(f"release-stages: error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
