#!/usr/bin/env python3
"""Check the logical bitstruct projections and compile their exact bodies to Lean."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_bit_selection import (FIXTURE as BITOPS_FIXTURE, PIN as BITOPS_PIN, ROOT, QUOTE, call_is,
                                 formals, object_term, require, symbol, term)
from check_x86_run import LAMBDA


FIXTURE = ROOT / "corpus/acl2/prefixes-projections/acl2-8.7.json"
SOURCE = ROOT / "Silmaril/Logic/ACL2/Standard/FixedWidth/Source.lean"
PIN = "737cb12e2409b39cbab6fe0d755a37bf3bb5a597778c08affe5d529602188fda"
LOGHEAD = ("ACL2", "LOGHEAD$INLINE")
SELECT = ("BITOPS", "PART-SELECT-WIDTH-LOW$INLINE")
FIX = ("X86ISA", "PREFIXES-FIX$INLINE")
READERS = {
    ("X86ISA", "PREFIXES->ADR$INLINE"): "prefixesAdr",
    ("X86ISA", "PREFIXES->NUM$INLINE"): "prefixesNum",
    ("X86ISA", "PREFIXES->NXT$INLINE"): "prefixesNxt",
}


def natural_quote(node):
    return call_is(node, QUOTE, 1) and type(node[1]) is int and node[1] >= 0


def generate(document):
    generic_data = BITOPS_FIXTURE.read_bytes()
    require(sha256(generic_data).hexdigest() == BITOPS_PIN, "Bitops source differs from its pin")
    generic = json.loads(generic_data)
    require(document["schema"] == generic["schema"] and document["acl2_commit"] == generic["acl2_commit"]
            and document["acl2_tree"] == generic["acl2_tree"], "different pinned ACL2 world")
    generic_rows = {symbol(row[0]): row for row in generic["definitions"]}
    rows = document["definitions"]
    require([symbol(row[0]) for row in rows] == [LOGHEAD, SELECT, FIX, *READERS],
            "unexpected translated declarations")
    require(rows[:2] == [generic_rows[LOGHEAD], generic_rows[SELECT]], "shared bit selection body changed")

    _, arity, parameters, fix = rows[2]
    formal, = formals(parameters)
    require(arity == 1 and call_is(fix, LOGHEAD, 2) and natural_quote(fix[1]),
            "expected unary PREFIXES-FIX using LOGHEAD at a quoted width")
    fix_body = term(fix, {formal: "x"}, {LOGHEAD: ("BitSelection.Source.loghead", 2)})
    rendered = [f"def prefixesFix (x : Object) : Object :=\n  {fix_body}"]
    for (identifier, lean_name), (_, arity, parameters, body) in zip(READERS.items(), rows[3:]):
        formal, = formals(parameters)
        require(arity == 1 and len(body) == 2 and call_is(body[0], LAMBDA, 2),
                f"expected a unary projection lambda for {identifier}")
        (_, lambda_formals, selection), operand = body
        payload, = formals(lambda_formals)
        require(call_is(operand, FIX, 1) and symbol(operand[1]) == formal,
                f"expected projection on the fixed formal for {identifier}")
        require(call_is(selection, SELECT, 3) and symbol(selection[1]) == payload
                and all(natural_quote(arg) for arg in selection[2:]),
                f"expected width/offset selection of the lambda parameter for {identifier}")
        fixed = term(operand, {formal: "x"}, {FIX: ("prefixesFix", 1)})
        read = term(selection, {payload: "fixed"}, {SELECT: ("BitSelection.Source.partSelectWidthLow", 3)})
        rendered.append(f"def {lean_name} (x : Object) : Object :=\n  let fixed := {fixed}\n  {read}")

    observations = []
    for row in document["observations"]:
        require(len(row) == 5 and all(type(value) is int for value in row[1:]), "unexpected observation result")
        observations.append("  (" + ", ".join(map(object_term, row)) + ")")
    bodies = "\n\n".join(rendered)
    samples = ",\n".join(observations)
    return f"""-- Generated from corpus/acl2/prefixes-projections by tests/logic/acl2/check_prefixes.py.
module

public import Silmaril.Logic.ACL2.Standard.FixedWidth.Defs
public import Silmaril.Logic.ACL2.Standard.BitSelection.Source

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.FixedWidth.Source

{bodies}

def observations : List (Object × Object × Object × Object × Object) := [
{samples}]

end Silmaril.Logic.ACL2.Standard.FixedWidth.Source
"""


def checked_source(data):
    require(sha256(data).hexdigest() == PIN, "projection export differs from its pin")
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
                    "Lean projection source differs from the pinned translation")
            print("Lean projection bodies and observations match the pinned export")
    except (IndexError, KeyError, TypeError, ValueError) as error:
        parser.exit(1, f"{error}\n")
