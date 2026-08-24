#!/usr/bin/env python3
"""Derive docs/data/manifest.json from challenges/.

Same discipline as lean-golf's tools/manifest.py: the site never hand-maintains
the challenge list, and the statement never comes from a submitter. Everything
the board shows about a challenge is read out of that challenge's own
config.json and its trusted Challenge.lean.
"""
from __future__ import annotations
import json, math, pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
CHALLENGES = ROOT / "challenges"
OUT = ROOT / "docs" / "data" / "manifest.json"


def bits(budget: int, num: int, den: int, exponent: int) -> float:
    """log2(q / alpha**e) — the security level the attack refutes."""
    alpha = num / den
    return math.log2(budget / alpha**exponent)


def load() -> list[dict]:
    out = []
    for d in sorted(p for p in CHALLENGES.iterdir() if (p / "config.json").is_file()):
        cfg = json.loads((d / "config.json").read_text())
        scoring = cfg["scoring"]
        base = cfg["baseline"]
        out.append(
            {
                # shown on the card
                "slug": cfg["slug"],
                "title": cfg.get("title", cfg["instance_name"]),
                "blurb": cfg.get("blurb", ""),
                "tags": cfg.get("tags", []),
                "par_bits": cfg["par"]["claimed_security_bits"],
                "baseline_bits": bits(
                    2 ** base["budget_log2"], base["advNum"], base["advDen"],
                    scoring["advantage_exponent"],
                ),
                "files": cfg.get("files", []),
                "setup": cfg.get("setup", []),
                # used by tools/verify.py, not rendered
                "instance_name": cfg["instance_name"],
                "advantage_exponent": scoring["advantage_exponent"],
                "solution_name": cfg["solution_name"],
                "solution_type": cfg["solution_type"],
                "permitted_axioms": cfg["permitted_axioms"],
                "timeout_seconds": cfg["timeout_seconds"],
            }
        )
    return out


def main() -> int:
    manifest = {
        "generated_by": "tools/manifest.py",
        "note": "Generated. Edit challenges/<name>/config.json, never this file.",
        "challenges": load(),
    }
    text = json.dumps(manifest, indent=2) + "\n"
    if "--check" in sys.argv:
        if not OUT.exists() or OUT.read_text() != text:
            print("manifest.json is stale — run tools/manifest.py", file=sys.stderr)
            return 1
        print("manifest.json up to date")
        return 0
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(text)
    print(f"wrote {OUT.relative_to(ROOT)} ({len(manifest['challenges'])} challenge(s))")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
