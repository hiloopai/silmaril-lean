#!/usr/bin/env python3
"""Cross-check a `silmaril.c-record-layout` v1 report against Clang through C itself.

Independent of the record-layout dump the report was made from: for every record and member
of the report this writes `_Static_assert`s on `sizeof`, `_Alignof` and `__builtin_offsetof`
(in bytes, so every bit quantity must be a multiple of 8), appends them to the report's own
`provenance.source`, and asks `clang -cc1 -triple <provenance.target> -fsyntax-only` to
accept the result. No headers are needed.

    check_offsetof.py REPORT.json... [--clang CLANG]
"""
from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
import tempfile


def asserts(report: dict) -> str:
    lines = []
    for r in report["records"]:
        ty = f'{r["kind"]} {r["name"]}'
        for key in ("size", "dataSize", "align"):
            if r[key] % 8:
                sys.exit(f"{ty}: {key} {r[key]} is not a whole number of bytes")
        lines.append(f'_Static_assert(sizeof({ty}) == {r["size"] // 8}, "sizeof {ty}");')
        lines.append(f'_Static_assert(_Alignof({ty}) == {r["align"] // 8}, "_Alignof {ty}");')
        for f in r["fields"]:
            if f["offset"] % 8:
                sys.exit(f'{ty}.{f["name"]}: offset {f["offset"]} is not a whole number of bytes')
            lines.append(f'_Static_assert(__builtin_offsetof({ty}, {f["name"]}) == '
                         f'{f["offset"] // 8}, "offsetof {ty}.{f["name"]}");')
    return "\n".join(lines) + "\n"


def check(path: pathlib.Path, clang: str) -> bool:
    report = json.loads(path.read_text())
    text = report["provenance"]["source"] + "\n" + asserts(report)
    with tempfile.TemporaryDirectory() as tmp:
        c = pathlib.Path(tmp) / "check.c"
        c.write_text(text)
        proc = subprocess.run(
            [clang, "-cc1", "-triple", report["provenance"]["target"], "-fsyntax-only", str(c)],
            capture_output=True, text=True, check=False)
    if proc.returncode != 0:
        print(f"{path}: clang rejects the report's layout:\n{proc.stderr}", file=sys.stderr)
        return False
    n = sum(2 + len(r["fields"]) for r in report["records"])
    print(f"{path}: {n} static assertions hold on {report['provenance']['target']}")
    return True


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("reports", type=pathlib.Path, nargs="+")
    ap.add_argument("--clang", default="clang")
    args = ap.parse_args()
    ok = [check(p, args.clang) for p in args.reports]
    return 0 if all(ok) else 1


if __name__ == "__main__":
    raise SystemExit(main())
