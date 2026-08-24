#!/usr/bin/env python3
"""Every challenge config carries what the board and the verifier need.

Catches the failure mode where a new challenge is added and the site renders a
card full of blanks, or the verifier scores it with a missing exponent.
"""
from __future__ import annotations
import json, pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
REQUIRED = ("slug", "instance_name", "title", "blurb", "tags", "challenge_module",
            "solution_module", "solution_name", "solution_type", "score_source",
            "scoring", "par", "baseline", "permitted_axioms", "timeout_seconds")
REQUIRED_SCORING = ("advantage_exponent",)
REQUIRED_PAR = ("claimed_security_bits",)
REQUIRED_BASELINE = ("budget_log2", "advNum", "advDen")


def main() -> int:
    bad = 0
    seen: dict[str, pathlib.Path] = {}
    for d in sorted(p for p in (ROOT / "challenges").iterdir() if (p / "config.json").is_file()):
        cfg_path = d / "config.json"
        for f in ("Solve.template.lean", "config.json"):
            if not (d / f).exists():
                print(f"{d.name}: missing {f}", file=sys.stderr); bad += 1
        # the trusted statement is a Lean module under challenges/Challenges/
        for f in ("Challenge.lean",):
            if not (ROOT / "challenges" / "Challenges" / d.name / f).exists():
                print(f"{d.name}: missing Challenges/{d.name}/{f}", file=sys.stderr); bad += 1
        if not cfg_path.exists():
            continue
        cfg = json.loads(cfg_path.read_text())
        for k in REQUIRED:
            if k not in cfg:
                print(f"{d.name}: config missing {k!r}", file=sys.stderr); bad += 1
        for k in REQUIRED_SCORING:
            if k not in cfg.get("scoring", {}):
                print(f"{d.name}: scoring missing {k!r}", file=sys.stderr); bad += 1
        for k in REQUIRED_PAR:
            if k not in cfg.get("par", {}):
                print(f"{d.name}: par missing {k!r}", file=sys.stderr); bad += 1
        for k in REQUIRED_BASELINE:
            if k not in cfg.get("baseline", {}):
                print(f"{d.name}: baseline missing {k!r}", file=sys.stderr); bad += 1
        e = cfg.get("scoring", {}).get("advantage_exponent")
        if e not in (1, 2):
            print(f"{d.name}: advantage_exponent must be 1 or 2, got {e!r}", file=sys.stderr); bad += 1
        slug = cfg.get("slug")
        if slug in seen:
            print(f"{d.name}: slug {slug!r} already used by {seen[slug].name}", file=sys.stderr); bad += 1
        seen[slug] = d
        # the submitted name lives under the solution module; the cost fields do not
        ns = cfg.get("solution_module", "").rsplit(".", 1)[0]
        name = cfg.get("solution_name", "")
        if not name.startswith(ns + "."):
            print(f"{d.name}: solution_name {name!r} is not under {ns!r}", file=sys.stderr); bad += 1
        # the score MUST be inside the submitter's namespace: they declare it
        for k, v in cfg.get("score_source", {}).items():
            if k != "note" and not v.startswith(ns + "."):
                print(f"{d.name}: score source {v!r} is not under {ns!r}",
                      file=sys.stderr); bad += 1
    print(f"{len(seen)} challenge(s) checked, {bad} problem(s)")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
