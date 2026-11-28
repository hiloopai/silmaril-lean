#!/usr/bin/env python3
"""Reject mutations of the translated TLB predicate, arithmetic, and proof evidence."""

from copy import deepcopy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools/acl2-x86isa"))
from check_tlb import FIXTURE, NIL, checked_source, generate, quote, sym


def reject(action, data, message):
    try:
        action(data)
    except ValueError as error:
        if message in str(error):
            return
        raise AssertionError(f"expected {message!r}, got {error}") from error
    raise AssertionError(f"mutation accepted, expected {message!r}")


def main():
    data = FIXTURE.read_bytes()
    native = json.loads(data)
    lean = checked_source(data)
    terms = {tuple(f[0][1:]): ("functions", i, 4) for i, f in enumerate(native["functions"])}
    quo = terms["ACL2", "NONNEGATIVE-INTEGER-QUOTIENT"]
    floor = terms["COMMON-LISP", "FLOOR"]
    mod = terms["COMMON-LISP", "MOD"]
    access = terms["X86ISA", "TLB-KEY->R-W-X$INLINE"]
    fix = terms["X86ISA", "TLB-KEY-FIX"]
    tlb = terms["X86ISA", "TLBP"]
    cases = [
        ("quotient base case", (*quo, 2), quote(1), "NONNEGATIVE-INTEGER-QUOTIENT logical body"),
        ("floor divisor product", (*floor, 1, 2, 0), sym("ACL2", "UNARY--"), "FLOOR logical body"),
        ("mod ignores denominator", (*mod, 2, 1, 2), quote(1), "MOD logical body"),
        ("bit offset without new proof", (*access, 0, 2, 3), quote(7), "bit selection formula"),
        ("key fix changes width", (*fix, 1), quote(45), "TLB-KEY-FIX logical body"),
        ("terminator package", (*tlb, 0, 2, 3, 2, 1), sym("ACL2", "TLB"), "keyword TLB terminator"),
        ("changed native quotient", ("arithmetic_observations", 1, 2), 1, "translated"),
        ("changed native key result", ("key_observations", 4, 2), NIL, "translated"),
        ("changed native record result", ("observations", 3, 3), NIL, "translated"),
        ("changed fix theorem", ("theorems", 0, 1, 2, 2), quote(NIL), "TLB key fix formula"),
        ("changed termination metadata", ("termination", 0, 1), quote(NIL), None),
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
