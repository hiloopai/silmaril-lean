#!/usr/bin/env python3
"""Bind the certified X86-RUN export to its generated, kernel-checked Lean terms."""

import argparse
from dataclasses import dataclass
import difflib
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "corpus/acl2/x86-run/acl2-8.7.json"
EXPORT_SHA256 = "ad779373d1802ecd4dcedb27d23b3ca6bdb6303acb10c2d25e572cc9268fc269"
LEAN_SOURCE = ROOT / "Silmaril/Logic/ACL2/X86Run/Source.lean"
RUN = ("X86ISA", "X86-RUN")
HALTED = ("X86ISA", "X86-RUN-HALTED")
IF = ("COMMON-LISP", "IF")
QUOTE = ("COMMON-LISP", "QUOTE")
LAMBDA = ("COMMON-LISP", "LAMBDA")
EQUAL = ("COMMON-LISP", "EQUAL")
IMPLIES = ("ACL2", "IMPLIES")
NIL = ["symbol", "COMMON-LISP", "NIL"]
TRUTH = ["symbol", "COMMON-LISP", "T"]
FUNCTIONS = {
    ("X86ISA", "FAULT"): (1, "faultSymbol"),
    ("X86ISA", "MS"): (1, "msSymbol"),
    ("X86ISA", "X86-FETCH-DECODE-EXECUTE"): (1, "stepSymbol"),
    ("ACL2", "ZP"): (1, "zpSymbol"),
    ("ACL2", "BINARY-+"): (2, "addSymbol"),
}
ARITIES = {RUN: 2, IF: 3, EQUAL: 2, IMPLIES: 2,
           **{name: arity for name, (arity, _) in FUNCTIONS.items()}}


def is_symbol(node):
    return (isinstance(node, list) and len(node) == 3 and node[0] == "symbol"
            and isinstance(node[1], str) and isinstance(node[2], str))


def symbol(node):
    if not is_symbol(node):
        raise ValueError(f"expected a package-qualified symbol, got {node!r}")
    return tuple(node[1:])


def formals(node):
    names = [] if node == NIL else list(map(symbol, node))
    if len(set(names)) != len(names):
        raise ValueError("duplicate formal parameter")
    return names


@dataclass(frozen=True)
class Call:
    name: tuple[str, str]
    args: tuple


@dataclass(frozen=True)
class Quote:
    value: object


def lower(node, scope, references, used):
    """Resolve variables, check world references and substitute translated lambdas."""
    if is_symbol(node):
        name = symbol(node)
        if name not in scope:
            raise ValueError(f"unbound variable {name}")
        return scope[name]
    if not isinstance(node, list) or not node:
        raise ValueError(f"expected a translated ACL2 term, got {node!r}")
    operator, *args = node
    if not is_symbol(operator):
        if not isinstance(operator, list) or len(operator) != 3 or symbol(operator[0]) != LAMBDA:
            raise ValueError(f"unsupported translated operator {operator!r}")
        parameters = formals(operator[1])
        if len(parameters) != len(args):
            raise ValueError("lambda arity mismatch")
        actuals = [lower(arg, scope, references, used) for arg in args]
        # ACL2 translated lambdas are closed except for their explicitly listed formals.
        return lower(operator[2], dict(zip(parameters, actuals)), references, used)

    name = symbol(operator)
    if name == QUOTE:
        if len(args) != 1 or not (is_symbol(args[0]) or type(args[0]) is int and args[0] == -1):
            raise ValueError(f"unsupported quotation {args!r}")
        return Quote(args[0])
    if name not in references:
        raise ValueError(f"undeclared function {name}")
    if references[name] != len(args):
        raise ValueError(f"call arity mismatch for {name}")
    used.add(name)
    return Call(name, tuple(lower(arg, scope, references, used) for arg in args))


def vector(args):
    return "![" + ", ".join(args) + "]"


def term(expr, *, extended=False, indent="  "):
    if isinstance(expr, int):
        return f".var {expr}"
    if isinstance(expr, Quote):
        if expr.value == NIL:
            return ".nil"
        if expr.value == TRUTH:
            return ".truth"
        if expr.value != -1:
            raise ValueError(f"unsupported quoted value in a Lean term: {expr.value!r}")
        ref = "(declaration.inclusion.symbol minusOneSymbol)" if extended else "minusOneSymbol"
        return f".app {ref} Fin.elim0"

    if expr.name in (IF, IMPLIES):
        constructor = ".ite" if expr.name == IF else "Term.implies"
        inner = indent + "  "
        args = [term(arg, extended=extended, indent=inner) for arg in expr.args]
        return "".join([constructor, *(f"\n{inner}({arg})" for arg in args)])
    args = [term(arg, extended=extended, indent=indent) for arg in expr.args]
    if expr.name == EQUAL:
        return f".equal ({args[0]}) ({args[1]})"
    if expr.name == RUN:
        if not extended:
            raise ValueError("recursive call inside an old-world term")
        ref = "(declaration.symbol runSymbol)"
    else:
        _, binding = FUNCTIONS[expr.name]
        ref = f"(declaration.inclusion.symbol {binding})" if extended else binding
    if expr.args == (0, 1):
        return f".app {ref} Term.var"
    actuals = f"(fun _ => {args[0]})" if len(args) == 1 else vector(args)
    return f".app {ref} {actuals}"


def body(expr, indent="  "):
    if isinstance(expr, Call):
        if expr.name == IF:
            test, yes, no = expr.args
            return (f".ite ({term(test)})\n"
                    f"{indent}  ({body(yes, indent + '  ')})\n"
                    f"{indent}  ({body(no, indent + '  ')})")
        if expr.name == RUN:
            args = f",\n{indent}    ".join(term(arg) for arg in expr.args)
            return f".call runSymbol\n{indent}  ![{args}]"
    return f".base ({term(expr)})"


def generate(document):
    if document["schema"] != 1 or document["x86isa_exec"] != "nil":
        raise ValueError("expected the logical X86-RUN export schema")
    if symbol(document["name"]) != RUN or symbol(document["halted_name"]) != HALTED:
        raise ValueError("unexpected declaration name")
    parameters = formals(document["formals"])
    if document["arity"] != len(parameters) or len(parameters) != 2:
        raise ValueError("expected two X86-RUN formals")
    references = {}
    for raw_name, arity in document["references"]:
        name = symbol(raw_name)
        if name in references or name not in ARITIES or type(arity) is not int or ARITIES[name] != arity:
            raise ValueError(f"unexpected reference or arity for {name}")
        references[name] = arity
    used = set()
    scope = dict(zip(parameters, range(len(parameters))))
    run = lower(document["body"], scope, references, used)
    halted = lower(document["halted"], scope, references, used)
    if set(references) != used:
        raise ValueError("the reference table must match the translated terms")
    bindings = []
    for name, arity in references.items():
        if name == RUN:
            signature, binding = "members", "runSymbol"
        elif name in FUNCTIONS:
            signature, (_, binding) = "old", FUNCTIONS[name]
        else:
            continue
        package, spelling = map(json.dumps, name)
        bindings.append(
            f"example : ({binding} : {signature}.Symbol {arity}).val = "
            f"⟨{package}, {spelling}⟩ := rfl"
        )
    binding_checks = "\n".join(bindings)

    return f"""-- Generated from corpus/acl2/x86-run/acl2-8.7.json by tools/acl2-x86isa/check_x86_run.py.
module

public import Silmaril.Logic.ACL2.X86Run.Signature
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run

open Recursive

{binding_checks}

def sourceBody : Body old members 2 :=
  {body(run)}

def declaration : Block old := block sourceBody

def halted : Sentence declaration.signature :=
  ⟨2, {term(halted, extended=True)}⟩

end Silmaril.Logic.ACL2.X86Run
"""


def checked_source(data):
    if sha256(data).hexdigest() != EXPORT_SHA256:
        raise ValueError("export differs from the pinned certified world artifact")
    return generate(json.loads(data))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path, default=FIXTURE, help="certified export JSON")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--emit", type=Path, help="write the generated Lean source")
    mode.add_argument("--compare", action="store_true", help="compare source already built by Lake")
    args = parser.parse_args()
    try:
        generated = checked_source(args.input.read_bytes())
        if args.emit:
            args.emit.write_text(generated, encoding="utf-8")
            return
        existing = LEAN_SOURCE.read_text(encoding="utf-8")
        if generated != existing:
            print("".join(difflib.unified_diff(
                existing.splitlines(keepends=True), generated.splitlines(keepends=True),
                fromfile=str(LEAN_SOURCE), tofile="generated from the export",
            )), end="")
            raise ValueError("Lean source differs from the translation of the export")
    except (KeyError, TypeError, ValueError) as error:
        parser.exit(1, f"{error}\n")
    if not args.compare:
        lake = os.environ.get("LAKE", "lake")
        with tempfile.TemporaryDirectory(prefix="lean-x86-run-") as directory:
            path = Path(directory) / "Source.lean"
            path.write_text(generated, encoding="utf-8")
            subprocess.run(
                [lake, "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", str(path)],
                cwd=ROOT, check=True,
            )
    print("X86-RUN body and X86-RUN-HALTED match the pinned certified export's Lean translation")


if __name__ == "__main__":
    main()
