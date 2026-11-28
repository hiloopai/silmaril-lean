#!/usr/bin/env python3
"""Check the bounded x86isa dependency manifest against translated body evidence."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import tempfile

from check_x86_run import FIXTURE as RUN_SOURCE
from check_x86_run import EXPORT_SHA256, LAMBDA, QUOTE, RUN, formals, is_symbol, symbol
from export_x86_run import TREE
from inventory import COMMIT, PROJECT


ROOT = Path(__file__).resolve().parents[2]
CORPUS = ROOT / "corpus/acl2/x86-dependencies"
STEP = ("X86ISA", "X86-FETCH-DECODE-EXECUTE")
BOOK = f"{PROJECT}/machine/x86.lisp"
HEADER = {"schema": 1, "acl2_commit": COMMIT, "acl2_tree": TREE, "x86isa_exec": "nil",
          "book": BOOK, "coverage": "direct-root-bodies"}
WORLD_CLASSES = {
    "definition": "native-only",
    "primitive": "primitive",
    "program": "unsupported",
    "constrained": "unsupported",
    "no-body": "unsupported",
    "absent": "unresolved-external",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encode_symbol(name):
    return ["symbol", *name]


def direct_calls(body, parameters):
    """Map each literal call head to its observed arity before any beta substitution."""
    calls = {}

    def visit(term, scope):
        if is_symbol(term):
            require(symbol(term) in scope, f"unbound variable {term}")
            return
        require(isinstance(term, list) and term, f"ill-formed translated term {term!r}")
        operator, *args = term
        if is_symbol(operator):
            name = symbol(operator)
            if name == QUOTE:
                require(len(args) == 1, "quotation arity mismatch")
                return
            require(calls.setdefault(name, len(args)) == len(args),
                    f"inconsistent call-site arity for {name}")
        else:
            require(isinstance(operator, list) and len(operator) == 3
                    and symbol(operator[0]) == LAMBDA, "ill-formed translated lambda")
            bound = formals(operator[1])
            require(len(args) == len(bound), "lambda arity mismatch")
            visit(operator[2], set(bound))
        for arg in args:
            visit(arg, scope)

    visit(body, set(parameters))
    return calls


def read_run():
    data = RUN_SOURCE.read_bytes()
    require(sha256(data).hexdigest() == EXPORT_SHA256, "X86-RUN evidence changed")
    return json.loads(data)


def check(manifest, step_bytes):
    """Check the graph and return the Lean-selected declaration's direct calls."""
    require(all(manifest[key] == value for key, value in HEADER.items()),
            "unexpected ACL2 manifest header")
    run = read_run()
    require(manifest["book_sha256"] == run["source_sha256"], "wrong source book hash")
    require(manifest["run_export_sha256"] == EXPORT_SHA256, "wrong X86-RUN evidence hash")
    require(manifest["step_body_sha256"] == sha256(step_bytes).hexdigest(),
            "wrong step body evidence hash")
    step = json.loads(step_bytes)
    bodies = {RUN: run, STEP: step}
    owners = {}
    roots = manifest["roots"]
    require([symbol(row["requested"]) for row in roots] == sorted(bodies), "wrong root selection")
    for row in roots:
        requested, resolved = symbol(row["requested"]), symbol(row["resolved"])
        source = bodies[requested]
        require(resolved == symbol(source["name"]) and resolved not in owners,
                f"wrong root resolution for {requested}")
        require(row["via"] == ("direct" if requested == resolved else "macro-alias"),
                f"wrong root resolution kind for {requested}")
        owners[resolved] = source

    rows = manifest["declarations"]
    names = [symbol(row["id"]) for row in rows]
    require(names == sorted(set(names)), "declarations must be sorted and unique")
    declarations = dict(zip(names, rows))
    reached = set(owners)
    for name, row in declarations.items():
        world, arity = row["world"], row["arity"]
        require(world in WORLD_CLASSES, f"unknown world class for {name}")
        kind = "checked" if name == RUN else WORLD_CLASSES[world]
        require(row["kind"] == kind, f"wrong manifest classification for {name}")
        require(arity is None if world == "absent" else type(arity) is int and arity >= 0,
                f"invalid world arity for {name}")
        if name not in owners:
            require(row["calls"] is None, f"body expansion beyond the frontier for {name}")
            continue
        require(world == "definition", f"root {name} needs a logical defining body")
        source = owners[name]
        parameters = formals(source["formals"])
        require(arity == len(parameters), f"wrong formal arity for {name}")
        calls = direct_calls(source["body"], parameters)
        expected = [[encode_symbol(callee), count] for callee, count in sorted(calls.items())]
        require(row["calls"] == expected and all(type(edge[1]) is int for edge in row["calls"]),
                f"dependency list disagrees with the translated body of {name}")
        for callee, count in calls.items():
            require(callee in declarations, f"missing declaration for {callee}")
            target = declarations[callee]
            require(target["arity"] in (None, count), f"world arity mismatch for {callee}")
            require(target["world"] != "program", f"program-mode call from {name} to {callee}")
        reached.update(calls)
    require(set(names) == reached, "declaration table does not match the bounded graph")
    require(manifest["frontier"] == [encode_symbol(name) for name in names
                                    if name not in owners and declarations[name]["kind"] != "primitive"],
            "frontier does not match the unexpanded non-primitive declarations")
    return declarations[RUN]["calls"]


def check_lean(calls):
    references = ",\n    ".join(
        f"(⟨{json.dumps(package)}, {json.dumps(name)}⟩, {arity})"
        for (_, package, name), arity in calls
    )
    source = f"""module

public import Silmaril.Logic.ACL2.Dependencies.Defs
public import Silmaril.Logic.ACL2.X86Run.Source

namespace Silmaril.Logic.ACL2.X86Run

public theorem manifestCallsAgree :
    let observed := sourceBody.toTerm declaration |>.directCalls |>.filter
      (fun call => decide (call.1 ≠ minusOneName))
    let claimed : List (Name × Nat) := [
    {references}]
    observed.all (fun call => claimed.any (fun entry => decide (entry = call))) &&
      claimed.all (fun call => observed.any (fun entry => decide (entry = call))) := by
  decide

#print axioms manifestCallsAgree

end Silmaril.Logic.ACL2.X86Run
"""
    with tempfile.TemporaryDirectory(prefix="lean-x86-dependencies-") as directory:
        path = Path(directory) / "Check.lean"
        path.write_text(source, encoding="utf-8")
        result = subprocess.run(
            [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
             "-DwarningAsError=true", str(path)], cwd=ROOT, text=True, stdout=subprocess.PIPE,
        )
    print(result.stdout, end="")
    result.check_returncode()
    audit = "'Silmaril.Logic.ACL2.X86Run.manifestCallsAgree' "
    require(result.stdout.strip() in {audit + "does not depend on any axioms",
                                      audit + "depends on axioms: [propext]"},
            "unexpected Lean axiom audit result")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", type=Path, default=CORPUS)
    parser.add_argument("--lean", action="store_true", help="check the manifest against the compiled Lean slice")
    args = parser.parse_args()
    try:
        manifest = json.loads((args.directory / "manifest.json").read_bytes())
        calls = check(manifest, (args.directory / "step-body.json").read_bytes())
        if args.lean:
            check_lean(calls)
    except (KeyError, TypeError, ValueError) as error:
        parser.exit(1, f"{error}\n")
    print("Direct dependencies match the two translated x86isa root bodies")


if __name__ == "__main__":
    main()
