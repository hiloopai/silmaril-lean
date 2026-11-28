#!/usr/bin/env python3
"""Reject mutations of the pinned immediate step frontier audit."""

from copy import deepcopy
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools/acl2-x86isa"))
from check_frontier_dependencies import AUDIT, check, encode, read_audit, root_selection


def reject(action, diagnostic):
    try:
        action()
    except (KeyError, TypeError, ValueError) as error:
        if diagnostic in str(error):
            return
        raise AssertionError(f"expected {diagnostic!r}, got {error}") from error
    raise AssertionError(f"mutation accepted, expected {diagnostic!r}")


def main():
    selection, book_sha = root_selection()
    original = read_audit(AUDIT.read_bytes(), selection, book_sha)
    indices = {row["id"][2]: i for i, row in enumerate(original["roots"])}
    prefixes = indices["GET-PREFIXES"]
    ms_write = indices["!MS"]
    adr = indices["PREFIXES->ADR$INLINE"]
    cases = [
        ("selector exclusion", ("excluded", 1, 1), 4, "wrong covered frontier"),
        ("root package", ("roots", adr, "id", 1), "ACL2", "wrong audited frontier"),
        ("call arity", ("roots", adr, "calls", 0, 1), 9, "world arity mismatch"),
        ("logical wrapper edge", ("roots", ms_write, "calls"), [], "lacks its direct logical call"),
        ("wrapper classification", ("roots", ms_write, "category"), "opaque-machine", "wrong frontier category"),
        ("self recursion", ("roots", prefixes, "recursive_clique"), [], "self-call without recursive metadata"),
        ("body witness", ("roots", adr, "body_sha256"), "0" * 64, None),
    ]
    for label, path, value, message in cases:
        changed = deepcopy(original)
        parent = changed
        for index in path[:-1]:
            parent = parent[index]
        assert parent[path[-1]] != value
        parent[path[-1]] = value
        if message:
            reject(lambda: check(changed, selection, book_sha), message)
        reject(lambda: read_audit(encode(changed), selection, book_sha), "differs from the pinned export")
        print(f"Rejected {label}")


if __name__ == "__main__":
    main()
