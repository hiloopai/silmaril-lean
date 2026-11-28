#!/usr/bin/env python3
"""Reject mutations of the certified status-accessor export."""

from copy import deepcopy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools/acl2-x86isa"))
from check_status_accessors import FIXTURE, TRUTH, checked_source, generate, quote, sym


def index_of(document, name):
    return next(i for i, definition in enumerate(document["functions"])
                if definition[0] == sym("X86ISA", name))


def altered(document, path, value):
    result = deepcopy(document)
    parent = result
    for index in path[:-1]:
        parent = parent[index]
    parent[path[-1]] = value
    return result


def encode(document):
    fields = [f"  {json.dumps(key)}: {json.dumps(value, separators=(',', ':'))}"
              for key, value in document.items()]
    return ("{\n" + ",\n".join(fields) + "\n}\n").encode()


def reject(action, data, message):
    try:
        action(data)
    except ValueError as error:
        if message in str(error):
            return
        raise AssertionError(f"expected {message!r}, got {error}") from error
    raise AssertionError(f"mutation accepted, expected {message!r}")


def main():
    source = FIXTURE.read_bytes()
    document = json.loads(source)
    assert encode(document) == source
    lean_source = checked_source(source)

    wrap = ("functions", index_of(document, "FAULT"), 4)
    abstract = ("functions", index_of(document, "FAULT$A"), 4)
    concrete = ("functions", index_of(document, "FAULT$C"), 4)
    lookup = ("functions", index_of(document, "X86REC-GET1"), 4)
    project = ("functions", index_of(document, "X86REC-GET"), 4)
    order, key, entry = document["functions"][lookup[1]][4][1][3]
    cases = [
        ("crossed wrapper", (*wrap, 0), sym("X86ISA", "MS$A"), "FAULT wrapper"),
        ("wrong keyword package", (*abstract, 1), quote(sym("ACL2", "FAULT")),
         "FAULT abstract body"),
        ("changed NIL index", (*abstract, 2), quote(TRUTH), "FAULT abstract body"),
        ("wrong XR declaration arity", ("functions", index_of(document, "XR"), 1), 2,
         "invalid declaration"),
        ("bad projection from TO-MTR", (*project, 2, 0), sym("COMMON-LISP", "CDR"),
         "X86REC-GET logical body"),
        ("reversed key ordering", (*lookup, 1, 3), [order, entry, key],
         "X86REC-GET1 logical body"),
        ("wrong concrete slot", (*concrete, 1, 1), 0, None),
        ("changed native sample", ("samples", 1, 4), 99, None),
    ]
    for label, path, value, message in cases:
        document_mutation = altered(document, path, value)
        if message:
            reject(generate, document_mutation, message)
        else:
            assert generate(document_mutation) != lean_source, f"{label} did not change Lean"
        reject(checked_source, encode(document_mutation), "differs from the pinned certified")
        print(f"Rejected {label}")

    obligation = altered(document, ("correspondence_obligations", 0, 1, 1), quote(TRUTH))
    signature = altered(document, ("functions", index_of(document, "FAULT"), 6, 0), TRUTH)
    reject(generate, obligation, "correspondence obligations")
    for mutation in [obligation, signature]:
        reject(checked_source, encode(mutation), "differs from the pinned certified")
    print("Rejected changed correspondence premise and stobj signature")


if __name__ == "__main__":
    main()
