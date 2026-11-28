#!/usr/bin/env python3
"""Reproduce or check the literal logical call closure of the 24-root snapshot."""

import argparse
from collections import Counter, defaultdict
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_dependencies import CORPUS, HEADER, ROOT, WORLD_CLASSES, encode_symbol, require
from check_frontier_dependencies import AUDIT, AUDIT_SHA256, encoded, read_audit, root_selection
from check_step import declarations
from check_x86_run import NIL, symbol
from export_dependencies import read_world
from inventory import lisp_string

FIXTURE = CORPUS / "step-closure.json"
PIN = "34c24c3ac654cabe834fa2bdcf629936ae355475025c3559a16ab65bf0a38f4a"
GRAPH_HEADER = {**HEADER, "coverage": "literal-logical-call-closure",
                "immediate_audit_sha256": AUDIT_SHA256}
NEWLY_CHECKED = {("X86ISA", f"PREFIXES->{field}$INLINE", 1) for field in ("ADR", "NUM", "NXT")}
X86_ROLES = {"abstract-export", "logical-implementation", "foundation-implementation"}
RESOLVED = {"definition", "primitive"}
NODE_KEYS = {"id", "arity", "world", "symbol_class", "stobj_function", "x86_roles", "recursive_clique"}
BODY_KEYS = {"stobjs_in", "stobjs_out", "body_sha256", "calls", "unsupported_quotes"}


def context():
    snapshot, book_sha = root_selection()
    audit = read_audit(AUDIT.read_bytes(), snapshot, book_sha)
    require(NEWLY_CHECKED <= set(snapshot), "installed projections are missing from the immediate audit")
    roots = [row for row in snapshot if row not in NEWLY_CHECKED]
    require(len(roots) == 24, "expected the 24-root frontier after the projections")
    return roots, book_sha, {symbol(row["id"]): row for row in audit["roots"]}


def nil_list(value):
    return [] if value == NIL else value


def node_category(row):
    if row["world"] != "definition":
        return row["world"]
    if row["stobj_function"] != NIL or row["x86_roles"]:
        return "stobj-interface"
    if any(slot != NIL for slot in row["stobjs_in"] + row["stobjs_out"]):
        return "stobj-bearing"
    return "ordinary-object"


def from_world(native):
    nodes = []
    for name, arity, world, symbol_class, inputs, outputs, stobj, roles, clique, *body in native:
        row = {"id": name, "arity": None if arity == NIL else arity, "world": world,
               "symbol_class": symbol_class, "stobj_function": stobj,
               "x86_roles": sorted(nil_list(roles)), "recursive_clique": sorted(nil_list(clique))}
        if body:
            digest, calls, strings, others = body
            row.update(stobjs_in=nil_list(inputs), stobjs_out=nil_list(outputs), body_sha256=digest,
                       calls=sorted(nil_list(calls)),
                       unsupported_quotes={key: count for key, count in (("string", strings), ("other-object", others))
                                           if count})
        nodes.append(row)
    return sorted(nodes, key=lambda row: symbol(row["id"]))


def reachable(outgoing, roots):
    pending = list(roots)
    seen = set()
    while pending:
        name = pending.pop()
        if name not in seen:
            seen.add(name)
            pending.extend(outgoing[name])
    return seen


def components(outgoing):
    """Kosaraju with an explicit traversal stack, including singleton components."""
    incoming = {name: [] for name in outgoing}
    for name, targets in outgoing.items():
        for target in targets:
            incoming[target].append(name)
    seen = set()
    finished = []
    for start in outgoing:
        if start in seen:
            continue
        seen.add(start)
        pending = [(start, iter(outgoing[start]))]
        while pending:
            name, targets = pending[-1]
            target = next(targets, None)
            if target is None:
                finished.append(name)
                pending.pop()
            elif target not in seen:
                seen.add(target)
                pending.append((target, iter(outgoing[target])))
    assigned = set()
    for name in reversed(finished):
        if name in assigned:
            continue
        assigned.add(name)
        component = [name]
        for vertex in component:
            for predecessor in incoming[vertex]:
                if predecessor not in assigned:
                    assigned.add(predecessor)
                    component.append(predecessor)
        yield sorted(component)


def analyse(nodes, roots):
    table = {symbol(row["id"]): row for row in nodes}
    categories = {name: node_category(row) for name, row in table.items()}
    outgoing = {name: [] for name in table}
    unresolved = []
    for owner, row in table.items():
        for callee, arity in row.get("calls", []):
            name = symbol(callee)
            require(name in table, f"missing declaration for {name}")
            target = table[name]
            outgoing[owner].append(name)
            reasons = []
            if target["world"] not in RESOLVED:
                reasons.append(target["world"])
            if target["arity"] is not None and target["arity"] != arity:
                reasons.append("arity-mismatch")
            if reasons:
                unresolved.append({"from": row["id"], "to": callee, "call_arity": arity,
                                   "world_arity": target["arity"], "reasons": reasons})
    require(reachable(outgoing, (symbol(name) for name, _ in roots)) == set(table),
            "unreachable declaration in closure")
    scc_counts = Counter()
    cycles = []
    native_clique_differences = []
    for group in components(outgoing):
        cyclic = len(group) > 1 or group[0] in outgoing[group[0]]
        kind = "mutual" if len(group) > 1 else "self" if cyclic else "acyclic"
        scc_counts[kind] += 1
        if cyclic:
            cycles.append({"kind": kind, "members": [encode_symbol(name) for name in group],
                           "categories": dict(sorted(Counter(categories[name] for name in group).items()))})
        for name in group:
            native = list(map(symbol, table[name]["recursive_clique"]))
            if native != (group if cyclic else []):
                native_clique_differences.append(table[name]["id"])
    terminals = Counter(categories[name] for name in table if not outgoing[name])
    barriers = defaultdict(Counter)
    for name, row in table.items():
        for kind, count in row.get("unsupported_quotes", {}).items():
            barriers[categories[name]][kind] += count
            barriers[categories[name]][f"{kind}_bodies"] += 1
    return {
        "roots": len(roots), "declarations": len(table), "edges": sum(map(len, outgoing.values())),
        "categories": dict(sorted(Counter(categories.values()).items())),
        "terminal_categories": dict(sorted(terminals.items())),
        "scc_counts": dict(sorted(scc_counts.items())),
        "cyclic_sccs": sorted(cycles, key=lambda c: c["members"]),
        "native_clique_differences": sorted(native_clique_differences),
        "quote_barriers": {key: dict(sorted(value.items())) for key, value in sorted(barriers.items())},
        "unresolved_edges": unresolved,
    }


def check(graph, expected_roots, book_sha, immediate):
    require(all(graph[key] == value for key, value in GRAPH_HEADER.items()), "wrong closure header")
    require(graph["book_sha256"] == book_sha, "wrong source book hash")
    roots = graph["roots"]
    require(roots == encoded(expected_roots), "wrong closure roots")
    nodes = graph["declarations"]
    names = [symbol(row["id"]) for row in nodes]
    require(names == sorted(set(names)), "unsorted or duplicate declarations")
    table = dict(zip(names, nodes))
    for name, row in table.items():
        arity, world = row["arity"], row["world"]
        require(world in WORLD_CLASSES, f"unknown world class for {name}")
        require(arity is None if world == "absent" else type(arity) is int and arity >= 0,
                f"invalid world arity for {name}")
        require(set(row) == (NODE_KEYS | BODY_KEYS if world == "definition" else NODE_KEYS),
                f"wrong body metadata for {name}")
        symbol(row["symbol_class"])
        symbol(row["stobj_function"])
        roles = row["x86_roles"]
        require(roles == sorted(set(roles)) and set(roles) <= X86_ROLES, f"bad X86 stobj roles for {name}")
        clique = list(map(symbol, row["recursive_clique"]))
        require(clique == sorted(set(clique)), f"bad native recursion clique for {name}")
        if world != "definition":
            continue
        require(len(row["stobjs_in"]) == arity and row["stobjs_out"], f"bad stobj signature for {name}")
        for slot in row["stobjs_in"] + row["stobjs_out"]:
            symbol(slot)
        digest = row["body_sha256"]
        require(len(digest) == 64 and all(c in "0123456789abcdef" for c in digest), f"bad body hash for {name}")
        callees = [symbol(callee) for callee, _ in row["calls"]]
        require(callees == sorted(set(callees)), f"unsorted or duplicate callees for {name}")
        require(all(type(count) is int and count >= 0 for _, count in row["calls"]), f"bad call arity for {name}")
        quotes = row["unsupported_quotes"]
        require(set(quotes) <= {"string", "other-object"} and
                all(type(count) is int and count > 0 for count in quotes.values()), f"bad quote counts for {name}")
    shared = BODY_KEYS | {"id", "arity", "stobj_function", "recursive_clique"}
    for name, arity in roots:
        key = symbol(name)
        require(key in table and table[key]["world"] == "definition" and table[key]["arity"] == arity,
                f"missing logical root {key}")
        require(all(table[key][field] == immediate[key][field] for field in shared),
                f"root metadata disagrees with the immediate audit for {key}")
    require(graph["summary"] == analyse(nodes, roots), "incorrect closure summary")


def encode(graph):
    rows = graph["declarations"]
    fields = [f"  {json.dumps(key)}: {json.dumps(value, separators=(',', ':'))}"
              for key, value in graph.items() if key != "declarations"]
    fields.append('  "declarations": [\n    ' +
                  ",\n    ".join(json.dumps(row, separators=(",", ":")) for row in rows) + "\n  ]")
    return ("{\n" + ",\n".join(fields) + "\n}\n").encode()


def read_graph(data):
    require(sha256(data).hexdigest() == PIN, "closure differs from the pinned export")
    graph = json.loads(data)
    check(graph, *context())
    return graph


def check_lean(roots):
    source = f"""module

public import Silmaril.Logic.ACL2.X86Run.WithStep.Frontier.Defs
import Lean

namespace Silmaril.Logic.ACL2.X86Run.WithStep.Frontier

public theorem closureRootsAgree : remainingEntries = {declarations(roots)} := by decide

#print axioms closureRootsAgree

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in ← Lean.collectAxioms ``closureRootsAgree do
    unless allowed.contains name do
      throwError "unapproved closure comparison axiom {{name}}"

end Silmaril.Logic.ACL2.X86Run.WithStep.Frontier
"""
    with tempfile.TemporaryDirectory(prefix="lean-x86-closure-") as directory:
        path = Path(directory) / "Check.lean"
        path.write_text(source, encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(path)], cwd=ROOT, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("graph", nargs="?", type=Path, default=FIXTURE)
    parser.add_argument("--checkout", type=Path, help="replay in the pinned certified ACL2 world")
    parser.add_argument("--emit", type=Path, help="write a fresh graph")
    parser.add_argument("--lean", action="store_true", help="check the roots against the compiled Lean frontier")
    args = parser.parse_args()
    if bool(args.checkout) != bool(args.emit):
        parser.error("--emit and --checkout must be used together")
    try:
        if args.checkout:
            roots, book_sha, immediate = context()
            query = "'(" + " ".join(f"({lisp_string(pkg)} {lisp_string(name)} {arity})"
                                   for pkg, name, arity in roots) + ")"
            native, source_sha = read_world(args.checkout, args.emit.with_suffix(".export.log"),
                                            driver="c3-export-closure-dependencies",
                                            library="closure-dependencies.lisp", operands=(query,))
            nodes = from_world(native)
            graph = {**GRAPH_HEADER, "book_sha256": source_sha, "roots": encoded(roots),
                     "summary": analyse(nodes, encoded(roots)), "declarations": nodes}
            check(graph, roots, book_sha, immediate)
            args.emit.write_bytes(encode(graph))
        else:
            graph = read_graph(args.graph.read_bytes())
        if args.lean:
            check_lean(graph["roots"])
    except (IndexError, KeyError, TypeError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"{error}\n")
    info = graph["summary"]
    print(f"{info['roots']} roots, {info['declarations']} declarations, {info['edges']} direct edges, "
          f"{len(info['cyclic_sccs'])} cyclic SCCs, {len(info['unresolved_edges'])} unresolved edges")


if __name__ == "__main__":
    main()
