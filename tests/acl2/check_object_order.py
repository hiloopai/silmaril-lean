#!/usr/bin/env python3
"""Reject mutations of the certified order and entry-list recognizer slice."""

from copy import deepcopy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools/acl2-x86isa"))
from check_object_order import FIXTURE, NIL, TRUTH, checked_source, generate, quote, sym


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
    document = json.loads(data)
    lean_source = checked_source(data)
    terms = {tuple(f[0][1:]): ("functions", i, 4) for i, f in enumerate(document["functions"])}
    lt = terms["ACL2", "<<"]
    lex = terms["ACL2", "LEXORDER"]
    alpha = terms["ACL2", "ALPHORDER"]
    symbol = terms["ACL2", "SYMBOL<"]
    string = terms["COMMON-LISP", "STRING<"]
    p1 = terms["X86ISA", "X86REC-P1"]
    defaults = terms["X86ISA", "X86-ELEM-DEFAULT"]
    tty = terms["X86ISA", "TTY-BUFFERP"]
    cases = [
        ("nonstrict order", lt, quote(TRUTH), "<< logical body"),
        ("LEXORDER atom decision", (*lex, 2, 3), quote(NIL), "LEXORDER logical body"),
        ("ALPHORDER category precedence", (*alpha, 2, 3), quote(NIL), "ALPHORDER logical body"),
        ("symbol name/package priority", (*symbol, 1, 0), sym("ACL2", "SYMBOL-PACKAGE-NAME"),
         "SYMBOL< logical body"),
        ("STRING< starting offset", (*string, 3), quote(1), "STRING< logical body"),
        ("X86REC-P1 empty-list result", (*p1, 2), quote(NIL), "X86REC-P1 logical body"),
        ("default key package", (*defaults, 1, 2, 1), sym("ACL2", "MS"), "distinct package-qualified"),
        ("changed field default", (*defaults, 2), quote(1), "translation"),
        ("TTY range check", (*tty, 0, 2, 3, 2, 1, 1), quote(7), "TTY-BUFFERP logical body"),
        ("native order observation", ("order_observations", 0, 2), NIL, "translation"),
        ("native recognizer observation", ("entry_observations", 0, 1), NIL, "translation"),
        ("native order theorem statement", ("order_laws", 0, 1), quote(TRUTH), None),
    ]
    for label, path, value, expected in cases:
        changed = deepcopy(document)
        parent = changed
        for index in path[:-1]:
            parent = parent[index]
        assert parent[path[-1]] != value, f"{label} mutation had no effect"
        parent[path[-1]] = value
        if expected == "translation":
            assert generate(changed) != lean_source, f"{label} did not change Lean"
        elif expected:
            reject(generate, changed, expected)
        lines = [f"  {json.dumps(k)}: {json.dumps(v, ensure_ascii=False, separators=(',', ':'))}"
                 for k, v in changed.items()]
        reject(checked_source, ("{\n" + ",\n".join(lines) + "\n}\n").encode(),
               "differs from the pinned certified")
        print(f"Rejected {label}")


if __name__ == "__main__":
    main()
