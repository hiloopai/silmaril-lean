#!/usr/bin/env python3
"""Exercise the translator and exact-export check on mutations of the real fixture."""

from copy import deepcopy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools/acl2-x86isa"))
from check_x86_run import FIXTURE, checked_source, generate


FAULT = ["symbol", "X86ISA", "FAULT"]
MS = ["symbol", "X86ISA", "MS"]
QUOTE = ["symbol", "COMMON-LISP", "QUOTE"]


def call_path(node, operator):
    """Find the path to the first application of a package-qualified operator."""
    if isinstance(node, list) and node:
        if node[0] == operator:
            return ()
        for i, child in enumerate(node):
            found = call_path(child, operator)
            if found is not None:
                return (i, *found)
    return None


def encode(document):
    """Match the native export format so only the named field changes."""
    fields = [f"  {json.dumps(key)}: {json.dumps(value, separators=(',', ':'))}"
              for key, value in document.items()]
    return ("{\n" + ",\n".join(fields) + "\n}\n").encode()


def replace(document, path, value):
    parent = document
    for part in path[:-1]:
        parent = parent[part]
    parent[path[-1]] = value


def reject(operation, value, reason):
    try:
        operation(value)
    except ValueError as error:
        if reason in str(error):
            return
        raise AssertionError(f"expected {reason!r}, got {error}") from error
    raise AssertionError(f"mutation accepted, expected {reason!r}")


def main():
    baseline = FIXTURE.read_bytes()
    original = json.loads(baseline)
    assert encode(original) == baseline
    expected = checked_source(baseline)
    body = original["body"]
    fault = ("body", *call_path(body, FAULT))
    quote = ("body", *call_path(body, QUOTE))

    tests = [
        ("same name in a different package", (*fault, 0, 1), "ACL2", "undeclared function"),
        ("call arity", fault, [FAULT], "call arity mismatch"),
        ("declared arity", ("references", 0, 1), 99, "unexpected reference or arity"),
        ("unbound variable", (*fault, 1, 2), "MISSING", "unbound variable"),
        ("decrement literal", (*quote, 1), 1, "unsupported quotation"),
        ("changed body test", (*fault, 0), MS, None),
        ("formal order", ("formals",), original["formals"][::-1], None),
        ("halted formula", ("halted", -1, -1), original["formals"][0], None),
        ("unnormalized body", ("unnormalized_body",), original["halted"], None),
        ("measure", ("measure",), original["formals"][1], None),
        ("justification", ("justification",), original["measure"], None),
        ("induction machine", ("induction_machine",), original["induction_machine"][::-1], None),
        ("termination theorem", ("termination_theorem",), original["halted"], None),
    ]
    for label, path, value, shape_error in tests:
        document = deepcopy(original)
        replace(document, path, value)
        data = encode(document)
        assert data != baseline, f"{label} was unchanged"
        if shape_error:
            reject(generate, document, shape_error)
        else:
            generated = generate(document)
            if path[0] in ("body", "formals", "halted"):
                assert generated != expected, f"{label} did not change the typed source"
        reject(checked_source, data, "differs from the pinned certified world artifact")
        print(f"Rejected {label}")


if __name__ == "__main__":
    main()
