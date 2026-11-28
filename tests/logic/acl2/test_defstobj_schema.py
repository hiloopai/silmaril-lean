#!/usr/bin/env python3
"""Reject structural mutations of an admitted fixed-layout DEFSTOBJ fixture."""

from copy import deepcopy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_defstobj_schema import FIXTURE, TOY, checked_source, generate, quote, sym
from test_toy_defstobj import reject


def main():
    data = FIXTURE.read_bytes()
    native = json.loads(data)
    toy = json.loads(TOY.read_bytes())
    assert generate(native, toy) == checked_source(data)
    rows = {row[0][2]: ("definitions", i) for i, row in enumerate(native["definitions"])}
    items = ("event", 2)
    reader = rows["SHELF-ITEMSI"]
    updater = rows["UPDATE-SHELF-ITEMSI"]
    mutations = [
        ("unsupported element type", (*items, 2, 1), sym("STRING", "COMMON-LISP"),
         "unsupported field type"),
        ("multidimensional array", (*items, 2, 2), [2, 1], "one natural array dimension"),
        ("negative dimension", (*items, 2, 2, 0), -1, "one natural array dimension"),
        ("resizable array", items, native["event"][2] + [sym("RESIZABLE", "KEYWORD"), sym("T", "COMMON-LISP")],
         "unsupported or resizable array"),
        ("noninteger initializer", (*items, 4), sym("NIL", "COMMON-LISP"), "explicit integer initializer"),
        ("duplicate slot", ("event", 3, 0), native["event"][2][0], "duplicate slot name"),
        ("slot order", ("event",), native["event"][:2] + [native["event"][3], native["event"][2], native["event"][4]],
         "unexpected logical body"),
        ("capacity", (*items, 2, 2, 0), 3, "unexpected logical body"),
        ("initializer", (*items, 4), 5, "unexpected logical body for CREATE-SIL-SHELVES"),
        ("reader slot", (*reader, 5, 2, 1, 1), 1, "unexpected logical body for SHELF-ITEMSI"),
        ("updater slot", (*updater, 5, 1, 1), 1, "unexpected logical body for UPDATE-SHELF-ITEMSI"),
        ("updater formal", (*updater, 2, 0, 1), "COMMON-LISP", "unexpected signature or formals"),
        ("resize body", (*rows["RESIZE-SHELF-ITEMS"], 5), quote(sym("NIL", "COMMON-LISP")),
         "unexpected logical body for RESIZE-SHELF-ITEMS"),
    ]
    for label, path, value, diagnostic in mutations:
        changed = deepcopy(native)
        parent = changed
        for key in path[:-1]:
            parent = parent[key]
        assert parent[path[-1]] != value, label
        parent[path[-1]] = value
        reject(lambda document: generate(document, toy), changed, diagnostic)
        reject(checked_source, json.dumps(changed).encode(), "differs from its pin")
        print(f"Rejected DEFSTOBJ schema {label} mutation")


if __name__ == "__main__":
    main()
