#!/usr/bin/env python3
"""Check and lower the pinned toy DEFSTOBJ logical declarations."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import sys
from textwrap import indent

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(ROOT / "tools/acl2-x86isa"))
from check_status_accessors import object_term
from check_x86_run import EQUAL, IF, NIL, QUOTE, formals, is_symbol, symbol


FIXTURE = ROOT / "corpus/acl2/toy-defstobj/acl2-8.7.json"
SOURCE = ROOT / "Silmaril/Logic/ACL2/Standard/FixedLayout/Source.lean"
TOY_SOURCE = Path(__file__).with_name("toy-defstobj.lsp")
PIN = "fcc10ed9d708f4c755f8e2d974e00c505cf8bbbb2e52ad82dc89414b68f82015"
TOY = ["symbol", "ACL2", "SIL-TOY"]
# Generated Lean name, arity, call interpretation, recursive body.
SUPPORT_DEFINITIONS = {
    ("ACL2", "LEN"): ("lenBody", 1, "Object.len", True),
    ("COMMON-LISP", "LENGTH"): ("length", 1, "length", False),
    ("COMMON-LISP", "="): ("numericEqual", 2, "numericEqual", False),
    ("COMMON-LISP", "ENDP"): ("endp", 1, "endp", False),
    ("COMMON-LISP", "NTH"): ("nthBody", 2, "Object.mvNth", True),
    ("ACL2", "UPDATE-NTH"): ("updateNthBody", 3, "Object.updateNth", True),
    ("ACL2", "UPDATE-NTH-ARRAY"): ("updateNthArray", 4, "updateNthArray", False),
    ("ACL2", "MAKE-LIST-AC"): ("makeListAcBody", 3, "Object.makeListAc", True),
}
DEFINITIONS = {
    **SUPPORT_DEFINITIONS,
    ("ACL2", "TOY-SCALARP"): ("scalarP", 1, "scalarP", False),
    ("ACL2", "TOY-CELLSP"): ("cellsPBody", 1, "Toy.cellsP", True),
    ("ACL2", "SIL-TOYP"): ("recognizer", 1, "recognizer", False),
    ("ACL2", "CREATE-SIL-TOY"): ("initial", 0, "initial", False),
    ("ACL2", "TOY-SCALAR"): ("readScalar", 1, "readScalar", False),
    ("ACL2", "UPDATE-TOY-SCALAR"): ("writeScalar", 2, "writeScalar", False),
    ("ACL2", "TOY-CELLSI"): ("readCell", 2, "readCell", False),
    ("ACL2", "UPDATE-TOY-CELLSI"): ("writeCell", 3, "writeCell", False),
}
STOBJ_INPUT = {"SIL-TOYP", "TOY-SCALAR", "UPDATE-TOY-SCALAR", "TOY-CELLSI", "UPDATE-TOY-CELLSI"}
STOBJ_OUTPUT = {"CREATE-SIL-TOY", "UPDATE-TOY-SCALAR", "UPDATE-TOY-CELLSI"}
PRIMITIVES = {
    ("COMMON-LISP", "CAR"): (1, "Object.car"),
    ("COMMON-LISP", "CDR"): (1, "Object.cdr"),
    ("COMMON-LISP", "CONS"): (2, "Object.cons"),
    ("COMMON-LISP", "COERCE"): (2, "Object.coerce"),
    ("COMMON-LISP", "ATOM"): (1, "Pure.atomBody"),
    ("ACL2", "BINARY-+"): (2, "Object.binaryAdd"),
    ("ACL2", "ZP"): (1, "Object.zp"),
    EQUAL: (2, "Object.equal"),
}
PREDICATES = {
    ("COMMON-LISP", "CONSP"): "Object.consp",
    ("COMMON-LISP", "INTEGERP"): "Object.integerp",
    ("COMMON-LISP", "STRINGP"): "Object.stringp",
    ("ACL2", "TRUE-LISTP"): "Object.trueListp",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def term(node, scope, functions):
    if is_symbol(node):
        name = symbol(node)
        require(name in scope, f"unbound translated formal {name}")
        return scope[name]
    require(isinstance(node, list) and node, f"expected a translated term, got {node!r}")
    operator, *args = node
    name = symbol(operator)
    if name == QUOTE:
        require(len(args) == 1, "quotation arity mismatch")
        if args[0] == ["symbol", "COMMON-LISP", "LIST"]:
            return "Object.symbol Symbol.list"
        return object_term(args[0])
    if name == IF:
        require(len(args) == 3, "IF arity mismatch")
        test, yes, no = (term(arg, scope, functions) for arg in args)
        return f"if {test} = Object.nil then\n{indent(no, '  ')}\nelse\n{indent(yes, '  ')}"
    if name in PREDICATES:
        require(len(args) == 1, f"call arity mismatch for {name}")
        return f"Object.ofBool ({PREDICATES[name]} ({term(args[0], scope, functions)}))"
    require(name in functions, f"unresolved translated call {name}")
    count, binding = functions[name]
    require(len(args) == count, f"call arity mismatch for {name}")
    return " ".join([binding, *(f"({term(arg, scope, functions)})" for arg in args)])


def check_stobjs(identifier, count, inputs, outputs):
    incoming = [NIL] * count
    if identifier[1] in STOBJ_INPUT:
        incoming[-1] = TOY
    expected_out = TOY if identifier[1] in STOBJ_OUTPUT else NIL
    require(inputs == (incoming or NIL) and outputs == [expected_out],
            f"unexpected stobj signature for {identifier}")


def generate(document):
    rows = document["definitions"]
    require([symbol(row[0]) for row in rows] == list(DEFINITIONS), "unexpected logical declarations")
    functions = dict(PRIMITIVES)
    definitions = []
    for name, arity, parameters, inputs, outputs, body in rows:
        identifier = symbol(name)
        lean, count, binding, recursive = DEFINITIONS[identifier]
        parameters = formals(parameters)
        names = [p[1].lower().replace("-", "_") for p in parameters]
        require(arity == count == len(parameters), f"declaration arity mismatch for {identifier}")
        require(len(set(names)) == count and all(re.fullmatch(r"[a-z_]+", n) for n in names),
                f"unsupported translated formals for {identifier}")
        check_stobjs(identifier, count, inputs, outputs)
        calls = dict(functions)
        binders = f" ({' '.join(names)} : Object)" if names else ""
        if recursive:
            calls[identifier] = (arity, "recur")
            binders = " (recur : " + " → ".join(["Object"] * (arity + 1)) + ")" + binders
        rendered = indent(term(body, dict(zip(parameters, names)), calls), "  ")
        definitions.append(f"def {lean}{binders} : Object :=\n{rendered}")
        functions[identifier] = (arity, binding)

    # Render proved observations against the model, independently of source body lowering.
    observation_calls = {
        name: (count, f"Toy.{lean}")
        for name, (lean, count, _, _) in DEFINITIONS.items()
        if lean in {"recognizer", "initial", "readScalar", "writeScalar", "readCell", "writeCell"}
    }
    observations = []
    for name, formula in document["observations"]:
        label = symbol(name)
        require(label[0] == "ACL2" and label[1].startswith("TOY-"), f"unexpected theorem {label}")
        op, lhs, rhs = formula
        require(symbol(op) == EQUAL and isinstance(rhs, list) and len(rhs) == 2
                and symbol(rhs[0]) == QUOTE, f"expected a ground observation equality for {label}")
        observations.append(f"  ({term(lhs, {}, observation_calls)}, {term(rhs, {}, {})})")
    bodies = "\n\n".join(definitions)
    samples = ",\n".join(observations)
    return f"""-- Generated from corpus/acl2/toy-defstobj by tests/logic/acl2/check_toy_defstobj.py.
module

public import Silmaril.Logic.ACL2.Standard.FixedLayout.Defs
public import Silmaril.Logic.ACL2.Standard.Pure.Source

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.FixedLayout.Source

{bodies}

def observations : List (Object × Object) := [
{samples}]

end Silmaril.Logic.ACL2.Standard.FixedLayout.Source
"""


def checked_source(data):
    require(sha256(data).hexdigest() == PIN, "toy DEFSTOBJ export differs from its pin")
    document = json.loads(data)
    require(document["toy_source_sha256"] == sha256(TOY_SOURCE.read_bytes()).hexdigest(),
            "toy DEFSTOBJ input differs from its exported digest")
    return generate(document)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path, default=FIXTURE)
    parser.add_argument("--emit", type=Path)
    args = parser.parse_args()
    try:
        generated = checked_source(args.input.read_bytes())
        if args.emit:
            args.emit.write_text(generated, encoding="utf-8")
        else:
            require(SOURCE.read_text(encoding="utf-8") == generated,
                    "Lean toy DEFSTOBJ source differs from the pinned translation")
            print("Lean toy DEFSTOBJ source and observations match the pinned export")
            if args.input == FIXTURE:
                from check_defstobj_schema import compare

                compare()
    except (KeyError, TypeError, ValueError) as error:
        parser.exit(1, f"{error}\n")
