#!/usr/bin/env python3
"""Check or reproduce an immediate source dependency audit of the open step frontier."""

import argparse
from collections import Counter
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_dependencies import CORPUS, HEADER, ROOT, STEP, WORLD_CLASSES, direct_calls, encode_symbol, require
from check_step import BODY_SHA256, MANIFEST_SHA256, SOURCE, declarations, generate, name as lean_name
from check_x86_run import NIL, formals, is_symbol, symbol
from export_dependencies import read_world
from inventory import lisp_string

AUDIT = CORPUS / "frontier-audit.json"
AUDIT_SHA256 = "c5c67c055f050450b9c74318db44cb63cca248cf0a104eb04da2fdf7f87f4553"
SELECTOR = ("BITOPS", "PART-SELECT-LOW-HIGH$INLINE", 3)
COVERED = {
    ("ACL2", "MV-NTH", 2), ("COMMON-LISP", "EQL", 2), ("COMMON-LISP", "NOT", 1),
    ("X86ISA", "FAULT", 1), ("X86ISA", "MS", 1), SELECTOR,
}
X86 = ("X86ISA", "X86")
CATEGORIES = ("pure-object", "logical-stobj-wrapper", "opaque-machine")
AUDIT_HEADER = {**HEADER, "coverage": "immediate-open-step-frontier-bodies",
                "manifest_sha256": MANIFEST_SHA256, "step_body_sha256": BODY_SHA256}


def root_selection():
    manifest_data = (CORPUS / "manifest.json").read_bytes()
    body_data = (CORPUS / "step-body.json").read_bytes()
    require(generate(manifest_data, body_data) == SOURCE.read_text(encoding="utf-8"),
            "canonical step source differs from the pinned translation")
    manifest = json.loads(manifest_data)
    rows = {symbol(row["id"]): row for row in manifest["declarations"]}
    entries = [(*symbol(callee), arity) for callee, arity in rows[STEP]["calls"]
               if rows[symbol(callee)]["kind"] == "native-only"]
    require(COVERED <= set(entries), "covered bindings disagree with the canonical frontier")
    return [row for row in entries if row not in COVERED], manifest["book_sha256"]


def encoded(entries):
    return [[encode_symbol((package, name)), arity] for package, name, arity in entries]


def category(row):
    fields = row["stobjs_in"] + row["stobjs_out"]
    if row["stobj_function"] == encode_symbol(X86):
        require(encode_symbol(X86) in row["stobjs_in"], "abstract wrapper lacks X86 input")
        require(len(row["calls"]) == 1 and symbol(row["calls"][0][0]) ==
                (row["id"][1], row["id"][2] + "$A"), "abstract wrapper lacks its direct logical call")
        return "logical-stobj-wrapper"
    require(row["stobj_function"] == NIL, "unexpected stobj function property")
    return "pure-object" if all(field == NIL for field in fields) else "opaque-machine"


def encode(document):
    # Keep each declaration and its edges together. Opaque bodies are retained only by hash.
    lines = []
    for key, value in document.items():
        if key in ("roots", "targets"):
            rows = ",\n".join("    " + json.dumps(row, separators=(",", ":")) for row in value)
            lines.append(f'  "{key}": [\n{rows}\n  ]')
        else:
            lines.append(f"  {json.dumps(key)}: {json.dumps(value)}")
    return ("{\n" + ",\n".join(lines) + "\n}\n").encode()


def build_audit(native, book_sha256):
    bodies, world_rows = native
    targets = [{"id": native_id, "arity": None if arity == NIL else arity, "world": world}
               for native_id, arity, world in sorted(world_rows, key=lambda row: symbol(row[0]))]
    roots = []
    for native_id, parameters, body, fnnames, inputs, outputs, stobj_fun, recursive in bodies:
        quote_barriers = Counter()

        def observe(value):
            # The existing step lowerer handles only literal integers and symbols.
            if type(value) is not int and not is_symbol(value):
                quote_barriers["string" if isinstance(value, str) else "other-object"] += 1

        calls = direct_calls(body, formals(parameters), on_quote=observe)
        set_from_acl2 = set() if fnnames == NIL else set(map(symbol, fnnames))
        require(set(calls) == set_from_acl2, f"call-head scan disagrees with ACL2 for {native_id}")
        body_bytes = json.dumps([parameters, body], separators=(",", ":")).encode()
        row = {"id": native_id, "arity": len(parameters), "body_sha256": sha256(body_bytes).hexdigest(),
               "stobjs_in": inputs, "stobjs_out": outputs, "stobj_function": stobj_fun,
               "recursive_clique": [] if recursive == NIL else sorted(recursive),
               "unsupported_quotes": dict(sorted(quote_barriers.items())),
               "calls": [[encode_symbol(name), arity] for name, arity in sorted(calls.items())]}
        row["category"] = category(row)
        roots.append(row)
    return {**AUDIT_HEADER, "book_sha256": book_sha256, "excluded": encoded(sorted(COVERED)),
            "roots": roots, "targets": targets}


def check(document, selection, book_sha256):
    require(all(document[key] == value for key, value in AUDIT_HEADER.items()), "wrong audit header")
    require(document["book_sha256"] == book_sha256, "wrong audited book SHA-256")
    require(document["excluded"] == encoded(sorted(COVERED)), "wrong covered frontier")
    roots = document["roots"]
    require([[row["id"], row["arity"]] for row in roots] == encoded(selection), "wrong audited frontier")
    targets = document["targets"]
    target_ids = [symbol(row["id"]) for row in targets]
    require(target_ids == sorted(set(target_ids)), "unsorted or duplicate target identities")
    table = dict(zip(target_ids, targets))
    for row in targets:
        world, arity = row["world"], row["arity"]
        require(world in WORLD_CLASSES, "unknown target world class")
        require(arity is None if world == "absent" else type(arity) is int and arity >= 0,
                "invalid target arity")

    reached = {symbol(row["id"]) for row in roots}
    for row in roots:
        owner = symbol(row["id"])
        require(owner in table, f"missing root declaration for {owner}")
        require(table[owner]["world"] == "definition" and table[owner]["arity"] == row["arity"],
                f"wrong root world identity for {owner}")
        require(len(row["stobjs_in"]) == row["arity"] and row["stobjs_out"], f"invalid stobj signature for {owner}")
        for slot in row["stobjs_in"] + row["stobjs_out"] + row["recursive_clique"]:
            symbol(slot)
        require(row["category"] == category(row), f"wrong frontier category for {owner}")
        digest = row["body_sha256"]
        require(len(digest) == 64 and all(c in "0123456789abcdef" for c in digest),
                f"invalid body SHA-256 for {owner}")
        require(set(row["unsupported_quotes"]) <= {"string", "other-object"} and
                all(type(count) is int and count > 0 for count in row["unsupported_quotes"].values()),
                f"invalid quote barrier for {owner}")
        names = [symbol(callee) for callee, _ in row["calls"]]
        require(names == sorted(set(names)), f"unsorted or duplicate call edges for {owner}")
        for callee, count in row["calls"]:
            name = symbol(callee)
            require(name in table, f"missing target declaration for {name}")
            target = table[name]
            require(type(count) is int and target["arity"] in (None, count), f"world arity mismatch for {name}")
            require(target["world"] != "program", f"program-mode call from {owner} to {name}")
        require(owner not in names or owner in map(symbol, row["recursive_clique"]),
                f"self-call without recursive metadata for {owner}")
        reached.update(names)
    require(reached == set(target_ids), "target table does not match the immediate graph")


def read_audit(data, selection, book_sha256):
    require(sha256(data).hexdigest() == AUDIT_SHA256, "frontier audit differs from the pinned export")
    document = json.loads(data)
    check(document, selection, book_sha256)
    return document


def check_lean(selection):
    package, spelling, arity = SELECTOR
    selector = f"({lean_name((package, spelling))}, {arity})"
    source = f"""module

public import Silmaril.Logic.ACL2.X86Run.WithStep.Frontier.Defs
import Lean

namespace Silmaril.Logic.ACL2.X86Run.WithStep.Frontier

public theorem auditedRootsAgree :
    remainingEntries.filter (fun entry => decide (entry ≠ {selector})) =
      {declarations(encoded(selection))} := by decide

#print axioms auditedRootsAgree

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms ``auditedRootsAgree do
    unless allowed.contains axiomName do
      throwError "unapproved frontier comparison axiom {{axiomName}}"

end Silmaril.Logic.ACL2.X86Run.WithStep.Frontier
"""
    with tempfile.TemporaryDirectory(prefix="lean-x86-frontier-") as directory:
        path = Path(directory) / "Check.lean"
        path.write_text(source, encoding="utf-8")
        result = subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                                 "-DwarningAsError=true", str(path)], cwd=ROOT, text=True,
                                stdout=subprocess.PIPE)
    print(result.stdout, end="")
    require(result.returncode == 0, "Lean rejected the exact frontier comparison")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("audit", nargs="?", type=Path, default=AUDIT)
    parser.add_argument("--checkout", type=Path, help="replay the metadata query in certified ACL2")
    parser.add_argument("--emit", type=Path, help="write a fresh audit outside the repository")
    parser.add_argument("--lean", action="store_true", help="check exact roots against the compiled Lean frontier")
    args = parser.parse_args()
    if bool(args.emit) != bool(args.checkout):
        parser.error("--emit and --checkout must be used together")
    try:
        selection, book_sha256 = root_selection()
        if args.checkout:
            roots = "'(" + " ".join(f"({lisp_string(pkg)} {lisp_string(name)} {arity})"
                                    for pkg, name, arity in selection) + ")"
            log = args.emit.with_suffix(".export.log")
            native, native_sha = read_world(args.checkout, log,
                                            driver="c3-export-frontier-dependencies",
                                            library="frontier-dependencies.lisp", operands=(roots,))
            document = build_audit(native, native_sha)
            check(document, selection, book_sha256)
            args.emit.write_bytes(encode(document))
        else:
            document = read_audit(args.audit.read_bytes(), selection, book_sha256)
        if args.lean:
            check_lean(selection)
    except (IndexError, KeyError, TypeError, ValueError) as error:
        parser.exit(1, f"{error}\n")
    counts = Counter(row["category"] for row in document["roots"])
    edge_count = sum(len(row["calls"]) for row in document["roots"])
    print(f"{len(selection)} frontier roots, {edge_count} direct edges, {len(document['targets'])} declarations "
          f"({', '.join(f'{counts[key]} {key}' for key in CATEGORIES)})")


if __name__ == "__main__":
    main()
