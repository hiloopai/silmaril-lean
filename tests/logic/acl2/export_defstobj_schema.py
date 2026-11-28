#!/usr/bin/env python3
"""Export two ACL2 DEFSTOBJ events and check reuse of the pinned SIL-TOY bodies."""

import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from export_toy_defstobj import HERE, digest, run_acl2
from check_toy_defstobj import FIXTURE as TOY_FIXTURE, SUPPORT_DEFINITIONS, symbol


SHELVES = HERE / "schema-defstobj.lsp"


def export(checkout, output):
    commit, tree, native = run_acl2(
        checkout, output, [HERE / "toy-defstobj.lsp", SHELVES],
        [HERE / "toy-defstobj-world.lsp", HERE / "schema-defstobj-world.lsp"],
        "export-defstobj-schema",
    )
    toy_event, toy_rows, event, rows, observations = native
    toy = json.loads(TOY_FIXTURE.read_bytes())
    pinned = {symbol(row[0]): row for row in toy["definitions"] if symbol(row[0]) not in SUPPORT_DEFINITIONS}
    current = {symbol(row[0]): row for row in toy_rows}
    if any(current.get(name) != row for name, row in pinned.items()):
        raise ValueError("SIL-TOY bodies differ from the pinned fixture")
    toy_auxiliary = [row for row in toy_rows if symbol(row[0]) not in pinned]
    fields = {
        "schema": 1, "acl2_commit": commit, "acl2_tree": tree,
        "toy_fixture_sha256": digest(TOY_FIXTURE), "source_sha256": digest(SHELVES),
        "toy_event": toy_event, "event": event,
    }
    lines = [f"  {json.dumps(key)}: {json.dumps(value)}" for key, value in fields.items()]
    for key, data in [("toy_auxiliary", toy_auxiliary), ("definitions", rows),
                      ("observations", observations)]:
        lines.append(f'  "{key}": [\n    ' + ",\n    ".join(map(json.dumps, data)) + "\n  ]")
    output.write_text("{\n" + ",\n".join(lines) + "\n}\n", encoding="utf-8")
    print(f"{digest(output)}  {output}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    try:
        export(args.checkout, args.output)
    except ValueError as error:
        parser.exit(1, f"{error}\n")
