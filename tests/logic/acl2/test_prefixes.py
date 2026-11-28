#!/usr/bin/env python3
"""Check changed projection definitions and observations under isolated Python."""

from copy import deepcopy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_prefixes import FIXTURE, SOURCE, checked_source, generate
from test_bit_selection import reject


def main():
    data = FIXTURE.read_bytes()
    original = checked_source(data)
    assert original == SOURCE.read_text(encoding="utf-8")
    native = json.loads(data)
    adr_selection = ("definitions", 3, 3, 0, 2)
    mutations = [
        ("selector package", (*adr_selection, 0, 1), "ACL2", "expected width/offset selection"),
        ("reader arity", ("definitions", 3, 1), 2, "expected a unary projection lambda"),
        ("selector arity", adr_selection, native["definitions"][3][3][0][2][:-1],
         "expected width/offset selection"),
        ("lambda scope", ("definitions", 3, 3, 0, 1, 0, 1), "X86ISA", "expected width/offset selection"),
        ("shared body", ("definitions", 0, 3, 2, 1, 2), "I", "shared bit selection body changed"),
        ("fixer width", ("definitions", 2, 3, 1, 1), 51, None),
        ("projection width", (*adr_selection, 2, 1), 7, None),
        ("projection offset", (*adr_selection, 3, 1), 35, None),
        ("off-guard observation", ("observations", 10, 2), 0, None),
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
