#!/usr/bin/env python3
"""Normalize Clang's record-layout dumps into `silmaril.c-record-layout` v1 JSON.

Clang prints record layouts only as text. This adapter runs two `clang -cc1` passes over one
C file and joins them:

* `-fdump-record-layouts-simple -fdump-record-layouts-complete`: per record, `Size`,
  `DataSize`, `Alignment` and `FieldOffsets`, in bits, without member names;
* `-ast-dump=json`: the records defined in the file, in definition order, with their member
  names in declaration order.

The output is the schema of `Silmaril.Data.Layout.Interchange` (see its module docstring and
docs/projects/c-record-layout.md). Lean re-checks every number against its own model, so an
adapter bug can make a check fail or misreport Clang, but cannot make Lean accept a layout
that disagrees with the JSON it is given. Whether the JSON faithfully reports Clang is this
script's job; `--check` re-derives committed fixtures to keep that reviewable.

Only the standard library is used. Usage:

    clang_record_layouts.py SOURCE.c --target TRIPLE [-o OUT.json] [--clang CLANG]
    clang_record_layouts.py --check FIXTURE.json SOURCE.c [--clang CLANG]
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys

ADAPTER = "tools/c-layout/clang_record_layouts.py v1"
DUMP_FLAGS = ["-fsyntax-only", "-fdump-record-layouts-simple", "-fdump-record-layouts-complete"]
AST_FLAGS = ["-fsyntax-only", "-ast-dump=json"]

LAYOUT_RE = re.compile(
    r"Type: (struct|union) (\w+)\s*\n\s*\nLayout: <ASTRecordLayout\s*\n"
    r"\s*Size:(\d+)\s*\n\s*DataSize:(\d+)\s*\n\s*Alignment:(\d+)\s*\n"
    r"\s*FieldOffsets: \[([0-9, ]*)\]>"
)


def run(clang: str, args: list[str]) -> str:
    proc = subprocess.run([clang, *args], capture_output=True, text=True, check=False)
    if proc.returncode != 0:
        sys.exit(f"{clang} {' '.join(args)} failed:\n{proc.stderr}")
    return proc.stdout


def defined_records(ast: dict) -> list[tuple[str, str, list[str]]]:
    """Records defined in the main file, in order: (kind, name, member names)."""
    out = []
    for node in ast.get("inner", []):
        if node.get("kind") != "RecordDecl" or not node.get("completeDefinition"):
            continue
        if node.get("isImplicit") or "includedFrom" in node.get("loc", {}):
            continue
        fields = []
        for member in node.get("inner", []):
            if member.get("kind") != "FieldDecl":
                continue
            if member.get("isBitfield") or "name" not in member:
                sys.exit(f"record {node.get('name')}: bit-fields and anonymous members are "
                         "outside schema v1")
            fields.append(member["name"])
        out.append((node["tagUsed"], node["name"], fields))
    return out


def report(source: pathlib.Path, target: str, clang: str) -> dict:
    text = source.read_bytes().decode("utf-8")
    dump = run(clang, ["-cc1", "-triple", target, *DUMP_FLAGS, str(source)])
    ast = json.loads(run(clang, ["-cc1", "-triple", target, *AST_FLAGS, str(source)]))
    layouts = {}
    for m in LAYOUT_RE.finditer(dump):
        kind, name, size, data_size, align, offsets = m.groups()
        offs = [int(x) for x in offsets.replace(" ", "").split(",") if x]
        layouts[(kind, name)] = (int(size), int(data_size), int(align), offs)
    records = []
    for kind, name, fields in defined_records(ast):
        if (kind, name) not in layouts:
            sys.exit(f"no layout dumped for {kind} {name}")
        size, data_size, align, offs = layouts[(kind, name)]
        if len(offs) != len(fields):
            sys.exit(f"{kind} {name}: {len(offs)} offsets for {len(fields)} members")
        records.append({
            "kind": kind, "name": name, "size": size, "dataSize": data_size, "align": align,
            "fields": [{"name": f, "offset": o} for f, o in zip(fields, offs)],
        })
    version = run(clang, ["--version"]).splitlines()[0].strip()
    method = "; ".join(" ".join(["clang", "-cc1", "-triple", target, *flags, source.name])
                       for flags in (DUMP_FLAGS, AST_FLAGS))
    return {
        "schema": "silmaril.c-record-layout", "version": 1, "unit": "bit",
        "provenance": {
            "producer": "clang", "producerVersion": version, "method": method,
            "target": target, "adapter": ADAPTER, "source": text,
        },
        "records": records,
    }


def dumps(obj: dict) -> str:
    """Stable, reviewable text: one line per member, ASCII only."""
    def j(v: object) -> str:
        return json.dumps(v, ensure_ascii=True, separators=(", ", ": "))
    prov = ",\n".join(f'    {j(k)}: {j(v)}' for k, v in obj["provenance"].items())
    recs = []
    for r in obj["records"]:
        keys = ("kind", "name", "size", "dataSize", "align")
        head = ", ".join(f"{j(k)}: {j(r[k])}" for k in keys)
        fields = ",\n".join(f"      {j(f)}" for f in r["fields"])
        recs.append(f'    {{{head}, "fields": [\n{fields}]}}')
    return (f'{{"schema": {j(obj["schema"])}, "version": {obj["version"]}, '
            f'"unit": {j(obj["unit"])},\n  "provenance": {{\n{prov}}},\n'
            f'  "records": [\n' + ",\n".join(recs) + "]}\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("source", type=pathlib.Path, nargs="?")
    ap.add_argument("--target")
    ap.add_argument("-o", "--output", type=pathlib.Path)
    ap.add_argument("--clang", default="clang")
    ap.add_argument("--check", type=pathlib.Path, metavar="FIXTURE",
                    help="re-derive FIXTURE from SOURCE and compare the layouts")
    args = ap.parse_args()
    if args.source is None:
        ap.error("SOURCE is required")
    if args.check:
        old = json.loads(args.check.read_text())
        new = report(args.source, old["provenance"]["target"], args.clang)
        keep = ("schema", "version", "unit", "records")
        same = all(old[k] == new[k] for k in keep) and \
            old["provenance"]["source"] == new["provenance"]["source"]
        if not same:
            print(f"{args.check}: layouts differ from {args.clang} "
                  f"({new['provenance']['producerVersion']})", file=sys.stderr)
            return 1
        print(f"{args.check}: agrees with {new['provenance']['producerVersion']}")
        return 0
    if not args.target:
        ap.error("--target is required")
    rep = report(args.source, args.target, args.clang)
    out = dumps(rep)
    assert json.loads(out) == rep
    if args.output:
        args.output.write_text(out)
    else:
        sys.stdout.write(out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
