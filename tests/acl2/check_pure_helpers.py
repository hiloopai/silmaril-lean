#!/usr/bin/env python3
"""Reject mutations of pure helper source bodies, identities and observations."""

from copy import deepcopy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools/acl2-x86isa"))
from check_pure_helpers import FIXTURE, MV_NTH, EQL, NOT, ATOM, checked_source, generate
from check_status_accessors import NIL, TRUTH, quote, sym


def reject(action, data, diagnostic):
    try:
        action(data)
    except ValueError as error:
        if diagnostic in str(error):
            return
        raise AssertionError(f"expected {diagnostic!r}, got {error}") from error
    raise AssertionError(f"mutation accepted, expected {diagnostic!r}")


def main():
    data = FIXTURE.read_bytes()
    native = json.loads(data)
    lean = checked_source(data)
    terms = {tuple(row[0][1:]): ("functions", i, 4) for i, row in enumerate(native["functions"])}
    mv, eql, neg, atom = (terms[name] for name in (MV_NTH, EQL, NOT, ATOM))
    cases = [
        ("recursive call package", (*mv, 3, 3, 0), sym("COMMON-LISP", "MV-NTH"), "undeclared function"),
        ("changed recursive increment", (*mv, 3, 3, 1, 1), quote(1), "unsupported quotation"),
        ("lost atomic remainder", (*mv, 2), quote(TRUTH), "translated"),
        ("EQL wrong call arity", (*eql, 0), sym("COMMON-LISP", "CAR"), "call arity mismatch"),
        ("EQL substituted operand", (*eql, 2), sym("ACL2", "X"), "translated"),
        ("NOT non-NIL result", (*neg, 2), quote(TRUTH), "translated"),
        ("ATOM drops negation", atom, native["functions"][atom[1]][4][1], "translated"),
        ("changed off-guard sample", ("mv_nth_observations", 4, 2), NIL, "translated"),
        ("changed termination formula", ("mv_nth_termination", 3), quote(TRUTH), None),
    ]
    for label, path, value, expected in cases:
        changed = deepcopy(native)
        parent = changed
        for index in path[:-1]:
            parent = parent[index]
        assert parent[path[-1]] != value, f"{label} mutation had no effect"
        parent[path[-1]] = value
        if expected == "translated":
            assert generate(changed) != lean, f"{label} did not change Lean"
        elif expected:
            reject(generate, changed, expected)
        reject(checked_source, json.dumps(changed).encode(), "differs from the pinned certified")
        print(f"Rejected {label}")


if __name__ == "__main__":
    main()
