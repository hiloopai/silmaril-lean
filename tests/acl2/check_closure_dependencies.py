#!/usr/bin/env python3
"""Reject structural and provenance mutations of the pinned closure graph."""

from copy import deepcopy
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools/acl2-x86isa"))
from check_closure_dependencies import FIXTURE, analyse, check, context, encode, read_graph


def reject(action, diagnostic):
    try:
        action()
    except ValueError as error:
        assert diagnostic in str(error), str(error)
    else:
        raise AssertionError(f"mutation accepted, expected {diagnostic}")


def main():
    evidence = context()
    data = FIXTURE.read_bytes()
    original = read_graph(data)
    assert encode(original) == data
    indices = {tuple(row["id"][1:]): i for i, row in enumerate(original["declarations"])}
    table = original["declarations"]
    first_root = indices[tuple(original["roots"][0][0][1:])]
    constraint = indices["X86ISA", "CPUID-FLAG-FN"]
    owner = indices["X86ISA", "FEATURE-FLAG"]
    edge = next(i for i, (name, _) in enumerate(table[owner]["calls"]) if name == table[constraint]["id"])
    cases = [
        ("root package", ("roots", 0, 0, 1), "ACL2", "wrong closure roots"),
        ("root body hash", ("declarations", first_root, "body_sha256"), "0" * 64, "root metadata disagrees"),
        ("root edge loss", ("declarations", first_root, "calls"), [], "root metadata disagrees"),
        ("invented defining body", ("declarations", constraint, "world"), "definition", "wrong body metadata"),
        ("unresolved edge loss", ("summary", "unresolved_edges"), [], "incorrect closure summary"),
        ("SCC count", ("summary", "scc_counts", "self"), 0, "incorrect closure summary"),
    ]
    for label, path, value, diagnostic in cases:
        modified = deepcopy(original)
        parent = modified
        for part in path[:-1]:
            parent = parent[part]
        assert parent[path[-1]] != value, label
        parent[path[-1]] = value
        reject(lambda: check(modified, *evidence), diagnostic)
        reject(lambda: read_graph(encode(modified)), "differs from the pinned export")
        print(f"Rejected {label}")

    modified = deepcopy(original)
    modified["declarations"][owner]["calls"][edge][1] = 4
    unresolved = analyse(modified["declarations"], modified["roots"])["unresolved_edges"]
    assert {"from": table[owner]["id"], "to": table[constraint]["id"], "call_arity": 4, "world_arity": 5,
            "reasons": ["constrained", "arity-mismatch"]} in unresolved
    reject(lambda: check(modified, *evidence), "incorrect closure summary")
    reject(lambda: read_graph(encode(modified)), "differs from the pinned export")
    print("Detected arity mismatch on the constrained edge")

    modified = deepcopy(original)
    del modified["declarations"][constraint]
    reject(lambda: check(modified, *evidence), "missing declaration")
    reject(lambda: read_graph(encode(modified)), "differs from the pinned export")
    print("Rejected a missing deep target")


if __name__ == "__main__":
    main()
