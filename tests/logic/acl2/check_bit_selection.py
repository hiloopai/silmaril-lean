#!/usr/bin/env python3
"""Translate the pinned projected Bitops definitions and observations to Lean."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "tools/acl2-x86isa"))
from check_status_accessors import object_term
from check_x86_run import QUOTE, formals, is_symbol, symbol


FIXTURE = ROOT / "corpus/acl2/bit-selection/acl2-8.7.json"
SOURCE = ROOT / "Silmaril/Logic/ACL2/Standard/BitSelection/Source.lean"
PIN = "8f04b8d63eabca0824215f09ea488dfbf90cdc921986a54950c9d3d85c83a561"
DEFINITIONS = {
    ("ACL2", "EXPT2$INLINE"): ("expt2", 1),
    ("ACL2", "IFLOOR$INLINE"): ("ifloor", 2),
    ("ACL2", "IMOD$INLINE"): ("imod", 2),
    ("ACL2", "LOGHEAD$INLINE"): ("loghead", 2),
    ("ACL2", "LOGTAIL$INLINE"): ("logtail", 2),
    ("BITOPS", "PART-SELECT-WIDTH-LOW$INLINE"): ("partSelectWidthLow", 3),
    ("BITOPS", "PART-SELECT-LOW-HIGH$INLINE"): ("partSelectLowHigh", 3),
}
IFIX = ("ACL2", "IFIX")
NFIX = ("ACL2", "NFIX")
PRIMITIVES = {
    IFIX: ("Object.ifix", 1), NFIX: ("Object.nfix", 1),
    ("ACL2", "BINARY-+"): ("Object.binaryAdd", 2),
    ("ACL2", "UNARY--"): ("Object.unaryMinus", 1),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def call_is(node, name, arity):
    return (isinstance(node, list) and len(node) == arity + 1 and is_symbol(node[0])
            and symbol(node[0]) == name)


def term(node, scope, functions):
    if is_symbol(node):
        name = symbol(node)
        require(name in scope, f"unbound translated formal {name}")
        return scope[name]

    operator, *args = node
    name = symbol(operator)
    if name == QUOTE:
        require(len(args) == 1 and type(args[0]) is int, "expected a quoted integer")
        return object_term(args[0])
    if name == ("COMMON-LISP", "EXPT"):
        require(len(args) == 2 and call_is(args[0], QUOTE, 1) and args[0][1] == 2
                and call_is(args[1], NFIX, 1), "expected EXPT of 2 at a natural-fixed exponent")
        return f"Object.integer (Int.ofNat (2 ^ ({term(args[1], scope, functions)}).integerFix.toNat))"
    if name in {("COMMON-LISP", "FLOOR"), ("COMMON-LISP", "MOD")}:
        require(len(args) == 2 and all(call_is(a, IFIX, 1) for a in args),
                f"expected two integer-fixed arguments for {name}")
        application = " ".join(f"({term(arg, scope, functions)}).integerFix" for arg in args)
        arithmetic = "floorIntegers" if name[1] == "FLOOR" else "modIntegers"
        return f"{arithmetic} {application}"
    require(name in functions, f"unresolved translated call {name}")
    binding, arity = functions[name]
    require(len(args) == arity, f"translated call arity mismatch for {name}")
    return " ".join([binding, *(f"({term(arg, scope, functions)})" for arg in args)])


def generate(document):
    rows = document["definitions"]
    require([symbol(row[0]) for row in rows] == list(DEFINITIONS), "unexpected translated declarations")
    functions = dict(PRIMITIVES)
    definitions = []
    for name, arity, parameters, body in rows:
        identifier = symbol(name)
        binding, count = DEFINITIONS[identifier]
        parameters = formals(parameters)
        names = [p[1].lower() for p in parameters]
        require(arity == count == len(parameters), f"declaration arity mismatch for {identifier}")
        require(len(set(names)) == count and all(re.fullmatch(r"[a-z]+", n) for n in names),
                f"unsupported translated formals for {identifier}")
        rendered = term(body, dict(zip(parameters, names)), functions)
        definitions.append(f"def {binding} ({' '.join(names)} : Object) : Object :=\n  {rendered}")
        functions[identifier] = (binding, arity)

    observations = []
    for callee, args, result in document["observations"]:
        binding, count = DEFINITIONS[symbol(callee)]
        require(binding in {"loghead", "logtail", "partSelectWidthLow", "partSelectLowHigh"}
                and len(args) == count and type(result) is int, "unexpected native observation")
        call = f"Object.{binding} " + " ".join(f"({object_term(arg)})" for arg in args)
        observations.append(f"  ({call}, {object_term(result)})")
    bodies = "\n\n".join(definitions)
    samples = ",\n".join(observations)
    return f"""-- Generated from corpus/acl2/bit-selection by tests/logic/acl2/check_bit_selection.py.
module

public import Silmaril.Logic.ACL2.Standard.BitSelection.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.BitSelection.Source

{bodies}

def observations : List (Object × Object) := [
{samples}]

end Silmaril.Logic.ACL2.Standard.BitSelection.Source
"""


def checked_source(data):
    require(sha256(data).hexdigest() == PIN, "Bitops export differs from its pin")
    return generate(json.loads(data))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path, default=FIXTURE)
    parser.add_argument("--emit", type=Path)
    args = parser.parse_args()
    try:
        expected = checked_source(args.input.read_bytes())
        if args.emit:
            args.emit.write_text(expected, encoding="utf-8")
        else:
            require(SOURCE.read_text(encoding="utf-8") == expected,
                    "Lean Bitops source differs from the pinned translation")
            print("Lean Bitops source and observations match the pinned export")
    except (KeyError, TypeError, ValueError) as error:
        parser.exit(1, f"{error}\n")
