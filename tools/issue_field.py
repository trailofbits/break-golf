#!/usr/bin/env python3
"""Read one field out of a submission issue body.

GitHub issue forms render a field as a `### Name` heading followed by its value;
issues opened before the form used `**Name:**` inline. Accept either, and print
nothing when the field is absent or GitHub's own "_No response_" placeholder.
"""
from __future__ import annotations
import re, sys

def main() -> int:
    name = sys.argv[1]
    body = sys.stdin.read()
    m = re.search(rf"^###\s+{re.escape(name)}\s*$\n(.*?)(?=^###\s|\Z)",
                  body, re.M | re.S)
    value = m.group(1) if m else None
    if value is None:
        m = re.search(rf"\*\*{re.escape(name)}:?\*\*\s*(.+)", body)
        value = m.group(1) if m else ""
    value = value.strip()
    if value in {"_No response_", "_none_", "_unstated_"}:
        value = ""
    print(" ".join(value.split())[:200])
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
