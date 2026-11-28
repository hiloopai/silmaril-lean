#!/usr/bin/env python3
"""Test identity, arity, binding, layout and observation mutations."""

from copy import deepcopy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_toy_defstobj import FIXTURE, SOURCE, checked_source, generate, symbol


def reject(check, value, diagnostic):
    try:
        check(value)
    except ValueError as error:
        assert diagnostic in str(error), str(error)
    else:
        raise AssertionError(f"mutation accepted, expected {diagnostic}")


def main():
    data = FIXTURE.read_bytes()
    original = checked_source(data)
    assert original == SOURCE.read_text(encoding="utf-8")
    native = json.loads(data)
    names = {symbol(row[0])[1]: ("definitions", i) for i, row in enumerate(native["definitions"])}
    write = (*names["UPDATE-TOY-CELLSI"], 5)
    init = (*names["CREATE-SIL-TOY"], 5)
    mutations = [
        ("call package", (*write, 0, 1), "COMMON-LISP", "unresolved translated call"),
        ("call arity", write, native["definitions"][write[1]][5][:-1], "call arity mismatch"),
        ("index binder package", (*write, 2, 1), "COMMON-LISP", "unbound translated formal"),
        ("lost stobj output", (*names["UPDATE-TOY-CELLSI"], 4, 0, 2), "NIL",
         "unexpected stobj signature"),
        ("array slot", (*write, 1, 1), 0, None),
        ("constructor array capacity", (*init, 2, 1, 1, 1), 2, None),
        ("constructor scalar initializer", (*init, 1, 1), 0, None),
        ("off-guard observation", ("observations", 15, 1, 2, 1), 0, None),
    ]
    for label, path, value, diagnostic in mutations:
        changed = deepcopy(native)
        parent = changed
        for key in path[:-1]:
            parent = parent[key]
        assert parent[path[-1]] != value, label
        parent[path[-1]] = value
        if diagnostic:
            reject(generate, changed, diagnostic)
        else:
            assert generate(changed) != original, label
        reject(checked_source, json.dumps(changed).encode(), "differs from its pin")
        print(f"Rejected {label} mutation")


if __name__ == "__main__":
    main()
