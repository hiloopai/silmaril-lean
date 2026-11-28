#!/usr/bin/env python3
"""Reject mutations of the pinned environment recognizer and observations."""

from copy import deepcopy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools/acl2-x86isa"))
from check_environment import FIXTURE, NIL, TRUTH, checked_source, generate, quote, sym


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
    terms = {tuple(f[0][1:]): ("functions", i, 4) for i, f in enumerate(native["functions"])}
    env = terms["X86ISA", "ENV-ALISTP"]
    oracle = terms["X86ISA", "RIP-RET-ALISTP"]
    width = terms["X86ISA", "I48P$INLINE"]
    assoc = terms["ACL2", "ASSOC-EQUAL"]
    signed = terms["ACL2", "SIGNED-BYTE-P"]
    cases = [
        ("wrong environment key package", (*env, 0, 2, 3, 2, 2, 1, 1, 1, 1),
         sym("ACL2", "FILE-DESCRIPTORS"), "distinct package-qualified environment key"),
        ("changed field count", (*env, 0, 2, 3, 2, 1, 2), quote(4), "translated"),
        ("bad oracle tail test", (*oracle, 0, 2, 3, 2, 2, 1, 0),
         sym("ACL2", "ALISTP"), "RIP-RET-ALISTP logical body"),
        ("changed address width", (*width, 1), quote(47), "translated"),
        ("skipped first matching entry", (*assoc, 3, 2), quote(NIL), "ASSOC-EQUAL logical body"),
        ("signed exponent off by one", (*signed, 2, 2, 1, 2, 1), quote(0), "SIGNED-BYTE-P logical body"),
        ("changed native record result", ("observations", 2, 4), NIL, "translated"),
        ("changed native association result", ("helper_observations", 0, 2), NIL, "translated"),
        ("changed termination formula", ("termination", 0, 1), quote(TRUTH), None),
    ]
    for label, path, value, expected in cases:
        document = deepcopy(native)
        parent = document
        for index in path[:-1]:
            parent = parent[index]
        assert parent[path[-1]] != value, f"{label} mutation had no effect"
        parent[path[-1]] = value
        if expected == "translated":
            assert generate(document) != lean, f"{label} did not change Lean"
        elif expected:
            reject(generate, document, expected)
        reject(checked_source, json.dumps(document).encode(), "differs from the pinned certified")
        print(f"Rejected {label}")


if __name__ == "__main__":
    main()
