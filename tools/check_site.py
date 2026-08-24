#!/usr/bin/env python3
"""The static site can load and render its own generated data.

Every id the script reaches for exists in the page, and every field the script
reads exists in the manifest. Cheap, and it catches the class of bug that only
shows up as a blank page in a browser.
"""
from __future__ import annotations
import json, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"


def main() -> int:
    bad = 0
    html = (DOCS / "index.html").read_text()
    js = (DOCS / "app.js").read_text()

    ids_html = set(re.findall(r'id="([^"]+)"', html))
    # both `$("f-x")` and any bare "f-x" string, which is how the previous
    # version of this check missed a live `addEventListener` on a removed id
    ids_js = set(re.findall(r'\$\("([^"]+)"\)', js)) | set(re.findall(r'"(f-[\w-]+)"', js))
    for missing in sorted(ids_js - ids_html):
        print(f"app.js reaches for #{missing}, which index.html does not define", file=sys.stderr); bad += 1

    for asset in ("style.css", "app.js", "data/site.json", "data/manifest.json", "data/ledger.json"):
        if not (DOCS / asset).exists():
            print(f"missing {asset}", file=sys.stderr); bad += 1

    manifest = json.loads((DOCS / "data" / "manifest.json").read_text())
    fields = set(re.findall(r"\bc\.([a-z_]+)", js))
    for c in manifest["challenges"]:
        for f in sorted(fields - set(c)):
            print(f"{c['slug']}: app.js reads c.{f}, absent from the manifest", file=sys.stderr); bad += 1

    ledger = json.loads((DOCS / "data" / "ledger.json").read_text())
    slugs = {c["slug"] for c in manifest["challenges"]}
    for slug in ledger["records"]:
        if slug not in slugs:
            print(f"ledger names unknown challenge {slug!r}", file=sys.stderr); bad += 1

    print(f"site checked, {bad} problem(s)")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
