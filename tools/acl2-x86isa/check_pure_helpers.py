#!/usr/bin/env python3
"""Compile the pinned logical helper definitions to typed Lean body functions."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_status_accessors import ROOT, functions, object_term, same
from check_x86_run import IF, Quote, lower, symbol

FIXTURE = ROOT / "corpus/acl2/pure-helpers/acl2-8.7.json"
SOURCE = ROOT / "Silmaril/Logic/ACL2/Standard/Pure/Source.lean"
EXPORT_SHA256 = "22599f92ca4704e7f1ef4fa350d18a6e22b32f4303f0656977ad745f110e4fce"

MV_NTH = ("ACL2", "MV-NTH")
EQL = ("COMMON-LISP", "EQL")
NOT = ("COMMON-LISP", "NOT")
ATOM = ("COMMON-LISP", "ATOM")
OPERATIONS = {
    ("COMMON-LISP", "CAR"): (1, "Object.car"),
    ("COMMON-LISP", "CDR"): (1, "Object.cdr"),
    ("COMMON-LISP", "CONSP"): (1, "(fun x => Object.ofBool (Object.consp x))"),
    ("COMMON-LISP", "EQUAL"): (2, "Object.equal"),
    ("ACL2", "ZP"): (1, "Object.zp"),
    ("ACL2", "BINARY-+"): (2, "Object.binaryAdd"),
}
ARITIES = {IF: 3, MV_NTH: 2, EQL: 2, NOT: 1, ATOM: 1,
           **{name: arity for name, (arity, _) in OPERATIONS.items()}}
BODIES = (
    (EQL, "eqlBody", ("x", "y"), {}),
    (NOT, "notBody", ("x",), {}),
    (ATOM, "atomBody", ("x",), {NOT: "Object.logicalNot"}),
    (MV_NTH, "mvNthBody", ("index", "values"), {ATOM: "atomBody", MV_NTH: "recur"}),
)


def render(expr, variables, dependencies, indent="  "):
    if type(expr) is int:
        return variables[expr]
    if isinstance(expr, Quote):
        return object_term(expr.value)
    if expr.name == IF:
        test, yes, no = expr.args
        deeper = indent + "  "
        return (f"if {render(test, variables, dependencies, indent)} = Object.nil then\n"
                f"{deeper}{render(no, variables, dependencies, deeper)}\n"
                f"{indent}else\n{deeper}{render(yes, variables, dependencies, deeper)}")
    operation = dependencies.get(expr.name)
    if operation is None:
        if expr.name not in OPERATIONS:
            raise ValueError(f"unsupported helper dependency {expr.name}")
        _, operation = OPERATIONS[expr.name]
    args = " ".join(f"({render(arg, variables, dependencies, indent)})" for arg in expr.args)
    return f"{operation} {args}"


def observations(rows, arity):
    same({len(row) for row in rows}, {arity + 1}, "sample arity")
    return ",\n".join("  (" + ", ".join(map(object_term, row)) + ")" for row in rows)


def generate(document):
    same(document["schema"], 1, "schema")
    same(document["x86isa_exec"], "nil", "profile")
    native_arities = {symbol(name): arity for name, arity in document["arities"]}
    same(len(document["arities"]), len(ARITIES), "arity table length")
    same(native_arities, ARITIES, "native arities")
    definitions = functions(document)
    same(set(definitions), {name for name, *_ in BODIES}, "defined helpers")

    bodies = []
    for name, lean_name, variables, dependencies in BODIES:
        formals, term = definitions[name]
        same(len(formals), ARITIES[name], f"{name[1]} declaration arity")
        scope = {symbol(formal): slot for slot, formal in enumerate(formals)}
        expr = lower(term, scope, native_arities, set())
        recur = "(recur : Object → Object → Object) " if name == MV_NTH else ""
        args = " ".join(variables)
        compiled = render(expr, variables, dependencies)
        bodies.append(f"def {lean_name} {recur}({args} : Object) : Object :=\n  {compiled}")

    body_text = "\n\n".join(bodies)
    mv = observations(document["mv_nth_observations"], 2)
    eql = observations(document["eql_observations"], 2)
    neg = observations(document["not_observations"], 1)
    return f"""-- Generated from the certified world by tools/acl2-x86isa/check_pure_helpers.py.
module

public import Silmaril.Logic.ACL2.Standard.Pure.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.Pure

{body_text}

def mvNthObservations : List (Object × Object × Object) := [
{mv}]

def eqlObservations : List (Object × Object × Object) := [
{eql}]

def notObservations : List (Object × Object) := [
{neg}]

end Silmaril.Logic.ACL2.Standard.Pure
"""


def checked_source(data):
    if sha256(data).hexdigest() != EXPORT_SHA256:
        raise ValueError("export differs from the pinned certified pure helper artifact")
    return generate(json.loads(data))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path, default=FIXTURE)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--emit", type=Path)
    mode.add_argument("--compare", action="store_true")
    args = parser.parse_args()
    try:
        generated = checked_source(args.input.read_bytes())
        if args.emit:
            args.emit.write_text(generated, encoding="utf-8")
            return
        same(generated, SOURCE.read_text(encoding="utf-8"), "generated Lean source")
    except (KeyError, TypeError, ValueError) as error:
        parser.exit(1, f"{error}\n")
    if not args.compare:
        with tempfile.TemporaryDirectory(prefix="lean-acl2-pure-") as directory:
            path = Path(directory) / "Source.lean"
            path.write_text(generated, encoding="utf-8")
            subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                            "-DwarningAsError=true", str(path)], cwd=ROOT, check=True)
    print("Pure helper bodies match the pinned certified export")


if __name__ == "__main__":
    main()
