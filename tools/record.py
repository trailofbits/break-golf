#!/usr/bin/env python3
"""Record a verified submission on the board.

    python3 tools/record.py --challenge spoc128 --issue 7 --solver alice \
        --assisted-by "Opus 5 max" --description "..." < verdict.json

Reads a verdict from `tools/verify.py --build` on stdin and appends it to
`scoring/ledger.json`, then regenerates the board. Refuses anything that is not
`ok` and `proved`: a shape-only pass never reaches the ledger.

Keyed by issue number, so re-running on an edited issue updates that record
rather than adding a second one.

Scores are not stored here — `tools/ledger.py` recomputes and re-sorts the whole
set, so a new record lands in the right place.
"""
from __future__ import annotations
import argparse, json, pathlib, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LEDGER = ROOT / "scoring" / "ledger.json"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--challenge", required=True)
    ap.add_argument("--issue", type=int, required=True)
    ap.add_argument("--solver", required=True)
    ap.add_argument("--assisted-by", default="")
    ap.add_argument("--description", default="")
    opts = ap.parse_args()

    verdict = json.load(sys.stdin)
    if not (verdict.get("ok") and verdict.get("proved")):
        print("not a verified submission; nothing recorded", file=sys.stderr)
        return 1

    num, den = (int(x) for x in verdict["advantage"].split("/"))
    record = {
        "solver": opts.solver,
        "assisted_by": opts.assisted_by or None,
        "budget": verdict["budget"],
        "advNum": num,
        "advDen": den,
        "verified_at": None,          # stamped by the caller's commit date
        "issue": opts.issue,
        "description": opts.description or None,
    }

    ledger = json.loads(LEDGER.read_text())
    records = ledger["records"].setdefault(opts.challenge, [])
    for i, r in enumerate(records):
        if r.get("issue") == opts.issue:
            record["verified_at"] = r.get("verified_at")
            records[i] = record
            break
    else:
        records.append(record)

    LEDGER.write_text(json.dumps(ledger, indent=2) + "\n")
    subprocess.run([sys.executable, str(ROOT / "tools" / "ledger.py")], check=True)
    print(f"recorded #{opts.issue} on {opts.challenge}: "
          f"{verdict['budget']} queries, {verdict['advantage']}, {verdict['bits']} bits")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
