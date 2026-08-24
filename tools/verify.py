#!/usr/bin/env python3
"""Verify a submission. Reads the submitted Lean on stdin, prints a JSON verdict.

    printf '%s' "$BODY" | python3 tools/verify.py spoc128            # shape only
    printf '%s' "$BODY" | python3 tools/verify.py spoc128 --build    # + Lean

Same interface as lean-golf's tools/verify.py: a challenge id as argv[1], the
untrusted body on stdin, one JSON object on stdout, exit 0 only when ok.

## The score comes out of Lean, not out of the issue

A submission declares its own `budget`, `advNum` and `advDen`, and the challenge's
`Solution` type is *indexed by them*. So this script never parses a score. It
builds the submission, then reads the three numbers back with `#eval` from the
same definitions that appear in the type of `wins`. A claimed score and a proved
score cannot differ, because they are the same definitions.

## What decides the verdict

  1. the submission elaborates, and `verified` binds it to the type the challenge
     pins at the submission's own numbers;
  2. `#print axioms verified` is within `permitted_axioms`;
  3. the advantage is positive, which the structure demands as a field.

The forbidden-token scan is a courtesy that produces a better error message, not
a security control: a `sorry` that slipped past it is still caught by (2).
"""
from __future__ import annotations
import argparse, json, math, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = json.loads((ROOT / "docs" / "data" / "manifest.json").read_text())
BY_SLUG = {c["slug"]: c for c in MANIFEST["challenges"]}
FORBIDDEN = ("native_decide", "maxHeartbeats", "maxRecDepth", "sorry", "admit")


def emit(obj: dict) -> int:
    print(json.dumps(obj))
    return 0 if obj.get("ok") else 1


def fail(reason: str, **extra) -> int:
    return emit({"ok": False, "reason": reason, **extra})


def build(challenge: dict, solve: str, timeout: int) -> dict:
    name = challenge["instance_name"]
    ns = f"Solution.{name}"
    sol_dir = ROOT / "solutions" / "Solution" / name
    sol_dir.mkdir(parents=True, exist_ok=True)
    solve_file = sol_dir / "Solve.lean"
    driver = ROOT / "solutions" / "Verify.lean"
    try:
        solve_file.write_text(solve)
        # Our driver is the top of the build: the trusted challenge is imported
        # FIRST, then the submission, and `verified` binds the two at the
        # submission's own numbers. A submission that declares its own
        # `Challenge.<N>.Solution` collides on import; one at any other type
        # fails to elaborate. Neither is reachable by choosing not to import us.
        driver.write_text(
            f"import Challenges.{name}.Challenge\n"
            f"import Solution.{name}.Solve\n\n"
            f"/-- The submission, at the type we pin, indexed by the score it\n"
            f"declares. `noncomputable` on purpose: a strategy may legitimately use\n"
            f"classical choice, and a plain `def` would reject it for code\n"
            f"generation rather than on the merits. -/\n"
            f"noncomputable def verified :\n"
            f"    Challenge.{name}.Solution {ns}.budget {ns}.advNum {ns}.advDen :=\n"
            f"  {ns}.solution\n\n"
            f"#eval ({ns}.budget, {ns}.advNum, {ns}.advDen)\n"
            f"#print axioms verified\n")

        r = subprocess.run(["lake", "build", "Solutions"], cwd=ROOT,
                           capture_output=True, text=True, timeout=timeout)
        out = r.stdout + r.stderr
        if r.returncode != 0:
            errs = [l for l in out.splitlines() if l.startswith("error:")][:6]
            reason = ("wrong_type"
                      if "already contains" in out or "Type mismatch" in out
                      else "does_not_elaborate")
            return {"ok": False, "reason": reason,
                    "expected": challenge["solution_type"], "lean_errors": errs}

        m = re.search(r"\((\d+),\s*(\d+),\s*(\d+)\)", out)
        if m is None:
            return {"ok": False, "reason": "score_not_readable",
                    "output": out[-400:]}
        budget, num, den = (int(x) for x in m.groups())

        a = re.search(r"depends on axioms: \[(.*?)\]", out, re.S)
        if a is None:
            found = [] if "does not depend on any axioms" in out else None
            if found is None:
                return {"ok": False, "reason": "axiom_audit_failed",
                        "output": out[-400:]}
        else:
            found = [x.strip() for x in a.group(1).replace("\n", " ").split(",") if x.strip()]
        extra = [x for x in found if x not in set(challenge["permitted_axioms"])]
        if extra:
            return {"ok": False, "reason": "forbidden_axioms", "axioms": found,
                    "not_permitted": extra}

        e = challenge["advantage_exponent"]
        bits = round(math.log2(budget / (num / den) ** e), 3)
        return {"ok": True, "proved": True,
                "budget": budget, "advantage": f"{num}/{den}", "bits": bits,
                "par": challenge["par_bits"], "under_par": bits < challenge["par_bits"],
                "axioms": found}
    finally:
        solve_file.unlink(missing_ok=True)
        driver.unlink(missing_ok=True)


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("challenge")
    ap.add_argument("--build", action="store_true",
                    help="run Lean, not just the shape checks")
    opts = ap.parse_args(argv[1:])

    challenge = BY_SLUG.get(opts.challenge)
    if challenge is None:
        return fail("unknown_challenge", challenge=opts.challenge, known=sorted(BY_SLUG))
    slug = opts.challenge
    body = sys.stdin.read()

    m = re.search(r"```lean\n(.*?)```", body, re.S)
    if m is None:
        return fail("no_lean_block", challenge=slug)
    solve = m.group(1)

    hits = [t for t in FORBIDDEN if re.search(rf"\b{t}\b", solve)]
    if hits:
        return fail("forbidden", challenge=slug, forbidden=hits)
    others = [c["solution_type"] for c in MANIFEST["challenges"]
              if c["slug"] != slug and c["solution_type"] in solve]
    if others:
        return fail("wrong_challenge", challenge=slug, names_instead=others)
    if challenge["solution_type"] not in solve:
        return fail("missing_solution_type", challenge=slug,
                    expected=challenge["solution_type"])

    if not opts.build:
        return emit({"ok": True, "challenge": slug, "proved": False,
                     "checked": "shape_only",
                     "note": "the score is read from Lean; run with --build"})
    try:
        result = build(challenge, solve, challenge["timeout_seconds"])
    except subprocess.TimeoutExpired:
        return fail("timeout", challenge=slug, seconds=challenge["timeout_seconds"])
    return emit({"challenge": slug, **result})


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
