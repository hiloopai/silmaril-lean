#!/usr/bin/env python3
"""Bind the pinned translated x86isa step body to its Lean source syntax."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_dependencies import CORPUS, ROOT, STEP, check, require
from check_x86_run import IF, LAMBDA, QUOTE, formals, is_symbol, symbol


SOURCE = ROOT / "Silmaril/Logic/ACL2/X86Step/Source.lean"
MANIFEST_SHA256 = "c36ab7c664fd850adc6d8c81f0d659eeb51fbe18bf06037af79ebeac5f4c9806"
BODY_SHA256 = "4aa5dcc4b81c2843d7e095c948ad89727248c08c1f37ef397ebd8ae46b328fea"


def name(parts):
    return "⟨" + ", ".join(map(json.dumps, parts)) + "⟩"


def names(items):
    return "[" + ", ".join(map(name, items)) + "]"


def term(node, indent="  "):
    if is_symbol(node):
        return f".var {name(symbol(node))}"
    operator, *actuals = node
    nested = indent + "  "

    def children(items):
        return "\n".join(f"{nested}({term(item, nested)})" for item in items)

    def vector():
        items = (term(item, nested + "  ") for item in actuals)
        return f"(RawArgs.ofList [\n{nested}  " + f",\n{nested}  ".join(items) + "])"

    if not is_symbol(operator):
        require(symbol(operator[0]) == LAMBDA, "expected a translated lambda")
        return (f".lambda {names(formals(operator[1]))}\n"
                f"{children([operator[2]])}\n{nested}{vector()}")

    callee = symbol(operator)
    if callee == QUOTE:
        value, = actuals
        if type(value) is int:
            return f".quote (.integer ({value}))"
        require(is_symbol(value), f"unsupported step quotation {value!r}")
        return f".quote (.symbol {name(symbol(value))})"
    if callee == IF:
        require(len(actuals) == 3, "IF arity mismatch")
        return ".ite\n" + children(actuals)
    return f".call {name(callee)}\n{nested}{vector()}"


def declarations(calls):
    return "[\n  " + ",\n  ".join(f"({name(symbol(callee))}, {arity})" for callee, arity in calls) + "]"


def generate(manifest_bytes, body_bytes):
    require(sha256(manifest_bytes).hexdigest() == MANIFEST_SHA256, "step manifest differs from the pin")
    require(sha256(body_bytes).hexdigest() == BODY_SHA256, "step body differs from the pin")
    manifest = json.loads(manifest_bytes)
    check(manifest, body_bytes)
    step = json.loads(body_bytes)
    require(symbol(step["name"]) == STEP, "unexpected step symbol")
    rows = {symbol(row["id"]): row for row in manifest["declarations"]}
    calls = rows[STEP]["calls"]
    external = []
    for callee, arity in calls:
        kind = rows[symbol(callee)]["kind"]
        if kind == "native-only":
            require(callee in manifest["frontier"], f"step call outside the frontier: {callee}")
            external.append((callee, arity))
        else:
            require(kind == "primitive", f"unexpected classification for step call {callee}")

    return f"""-- Generated from corpus/acl2/x86-dependencies by tools/acl2-x86isa/check_step.py.
module

public import Silmaril.Logic.ACL2.Translated.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Step

open Translated

def stepName : Name := {name(STEP)}

def formals : List Name := {names(formals(step["formals"]))}

def manifestCalls : List (Name × Nat) := {declarations(calls)}

def frontierEntries : List (Name × Nat) := {declarations(external)}

def source : Raw :=
  {term(step["body"])}

end Silmaril.Logic.ACL2.X86Step
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", type=Path, default=CORPUS)
    parser.add_argument("--emit", type=Path, help="write the generated Lean source")
    args = parser.parse_args()
    try:
        generated = generate((args.directory / "manifest.json").read_bytes(),
                             (args.directory / "step-body.json").read_bytes())
        if args.emit:
            args.emit.write_text(generated, encoding="utf-8")
        else:
            require(SOURCE.read_text(encoding="utf-8") == generated,
                    "Lean step source differs from the pinned translation")
            print("Lean step source matches the pinned translated body and frontier")
    except (KeyError, TypeError, ValueError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
