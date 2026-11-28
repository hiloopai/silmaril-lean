#!/usr/bin/env python3
"""Exercise semantic rejection on the certified dependency manifest."""

from copy import deepcopy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools/acl2-x86isa"))
from check_dependencies import CORPUS, RUN, STEP, check, symbol


def declaration(manifest, name):
    return next(row for row in manifest["declarations"] if symbol(row["id"]) == name)


def main():
    original = json.loads((CORPUS / "manifest.json").read_bytes())
    step = (CORPUS / "step-body.json").read_bytes()
    check(original, step)

    def reject(mutation, expected):
        try:
            check(mutation, step)
        except ValueError as error:
            if expected in str(error):
                return
            raise AssertionError(f"expected {expected!r}, got {error}") from error
        raise AssertionError(f"accepted mutation intended to cause {expected!r}")

    modified = deepcopy(original)
    run = declaration(modified, RUN)
    run["calls"] = [edge for edge in run["calls"] if symbol(edge[0]) != RUN]
    reject(modified, "dependency list disagrees")

    modified = deepcopy(original)
    step_name = symbol(next(row["resolved"] for row in original["roots"]
                            if symbol(row["requested"]) == STEP))
    declaration(modified, step_name)["calls"].pop()
    reject(modified, "dependency list disagrees")

    modified = deepcopy(original)
    fault = ("X86ISA", "FAULT")
    edge = next(edge for edge in declaration(modified, RUN)["calls"] if symbol(edge[0]) == fault)
    edge[0][1] = "ACL2"
    reject(modified, "dependency list disagrees")

    modified = deepcopy(original)
    declaration(modified, fault)["arity"] += 1
    reject(modified, "world arity mismatch")

    modified = deepcopy(original)
    modified["frontier"].pop()
    reject(modified, "frontier does not match")

    modified = deepcopy(original)
    declaration(modified, step_name)["kind"] = "checked"
    reject(modified, "wrong manifest classification")

    print("Certified x86isa dependency manifest passed and rejected six mutations")


if __name__ == "__main__":
    main()
