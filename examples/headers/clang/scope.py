#!/usr/bin/env python3
"""The scope of a filtered artifact: what the file filter (filter.py) keeps and drops of a whole
clang `-ast-dump=json` translation unit, and how many explicit function declarations another
preprocessor configuration of the same header has.

    python3 -I scope.py NAME KEPT-FILES DEFAULT.json OTHER-LABEL OTHER.json

KEPT-FILES is the filter's file list (one argument, space-separated). Every top-level node of
DEFAULT.json is attributed to the file of its location exactly as filter.py does (it imports
filter.py's location chain from its own directory), and counted by (file, kind, implicit).
OTHER.json is the same header under another configuration (OTHER-LABEL names it); it is not
pinned, and only its explicit function declarations are compared with DEFAULT.json's. The
report is written to standard output; `recipe.sh --check` compares it byte for byte. It is a
recipe-level check of clang's output, not a theorem.
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import filter as filt  # noqa: E402  (filter.py, next to this file)


def nodes(path):
    with open(path) as f:
        doc = json.load(f)
    chain = filt.Chain()
    out = []
    for n in doc.get("inner", []):
        _, file = filt.advance(n, chain)
        out.append((file, n.get("kind"), bool(n.get("isImplicit")), n.get("name")))
    return out


def explicit_fns(ns):
    return {name for (_, kind, implicit, name) in ns if kind == "FunctionDecl" and not implicit}


def main(argv):
    name, kept, default, label, other = argv
    kept = set(kept.split())
    ns = nodes(default)
    rows = {}
    for file, kind, implicit, _ in ns:
        key = ("kept" if file in kept else "dropped", str(file), kind, implicit)
        rows[key] = rows.get(key, 0) + 1
    print(f"scope: {name}")
    print(f"top-level declarations: {len(ns)}")
    for (what, file, kind, implicit), n in sorted(rows.items()):
        print(f"{what}: {n} {kind}{' implicit' if implicit else ''} {file}")
    dropped_fns = sum(n for (what, _, kind, _), n in rows.items()
                      if what == "dropped" and kind == "FunctionDecl")
    print(f"function declarations dropped by the file filter: {dropped_fns}")
    a, b = explicit_fns(ns), explicit_fns(nodes(other))
    print(f"explicit function names, pinned configuration: {len(a)}")
    print(f"explicit function names, {label} (not pinned): {len(b)}")
    only = sorted(b - a)
    public = [x for x in only if not x.startswith("__")]
    print(f"names only under {label}: {len(only)} ({len(public)} without a leading __)")
    print(f"names only in the pinned configuration: {len(a - b)}")
    for x in public:
        print(f"  {x}")


if __name__ == "__main__":
    main(sys.argv[1:])
