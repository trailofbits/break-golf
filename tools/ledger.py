#!/usr/bin/env python3
"""Copy scoring/ledger.json to the site, scoring and sorting the records.

Best score first. Nothing here writes a record without a verified issue.
"""
from __future__ import annotations
import json, math, pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SRC = ROOT / "scoring" / "ledger.json"
OUT = ROOT / "docs" / "data" / "ledger.json"


def bits(r: dict, exponent: int) -> float:
    alpha = r["advNum"] / r["advDen"]
    return math.log2(r["budget"] / alpha**exponent)


def main() -> int:
    ledger = json.loads(SRC.read_text())
    manifest = json.loads((ROOT / "docs" / "data" / "manifest.json").read_text())
    exps = {c["slug"]: c["advantage_exponent"] for c in manifest["challenges"]}
    for slug, records in ledger["records"].items():
        e = exps.get(slug)
        if e is None:
            print(f"ledger names unknown challenge {slug!r}", file=sys.stderr)
            return 1
        for r in records:
            r.setdefault("verified_at", None)
            r.setdefault("issue", None)
            if r["advNum"] <= 0:
                print(f"{slug}: non-positive advantage", file=sys.stderr)
                return 1
            r["bits"] = round(bits(r, e), 3)
        records.sort(key=lambda r: r["bits"])
    text = json.dumps(ledger, indent=2) + "\n"
    if "--check" in sys.argv:
        ok = OUT.exists() and OUT.read_text() == text
        print("ledger up to date" if ok else "ledger is stale — run tools/ledger.py")
        return 0 if ok else 1
    OUT.write_text(text)
    n = sum(len(v) for v in ledger["records"].values())
    print(f"wrote {OUT.relative_to(ROOT)} ({n} record(s))")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
