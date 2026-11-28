#!/usr/bin/env python3
"""Exercise Bitops source checking independently of the fixture digest."""

from copy import deepcopy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_bit_selection import FIXTURE, SOURCE, checked_source, generate


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
    low_high = ("definitions", 6, 3)
    mutations = [
        ("call package", (*low_high, 0, 1), "ACL2", "unresolved translated call"),
        ("call arity", low_high, native["definitions"][6][3][:-1], "call arity mismatch"),
        ("formal package", (*low_high, 3, 1), "ACL2", "unbound translated formal"),
        ("power base", ("definitions", 0, 3, 1, 1), 3, "expected EXPT of 2"),
        ("inclusive width", (*low_high, 2, 1, 1), 0, None),
        ("off-guard observation", ("observations", 22, 2), 0, None),
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
