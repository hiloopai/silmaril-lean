#!/usr/bin/env python3
"""Filter a clang `-ast-dump=json` translation unit to the declarations of named files, and
project each to the keys the Lean import reads.

    python3 -I filter.py FILE... < full.json > filtered.json

FILE are the file names as clang prints them in locations (`arith.h`, `../common/rt.h`,
`./zconf.h`). The filter is part of the recipe (`recipe.sh`), which records it and its SHA-256
in each artifact's `.prov`. It does exactly these things:

1. **Selection.** A top-level node of the TranslationUnitDecl is kept iff the file of its
   `loc` is one of FILE. For a location inside a macro expansion the file is that of the
   *expansion* location (where the declaration is written), not of the macro's spelling. A
   node whose `loc` is empty (clang's implicit builtin typedefs) has no file and is dropped.
   The order of the kept nodes is clang's.
2. **Locations resolved.** Clang prints a location's `file` only when it differs from the
   previously printed location, and its `line` only when the file or the line differs
   (JSONNodeDumper::writeBareSourceLocation). The filter follows that chain through the whole
   document and writes each kept node's `loc` with its `file` and `line` explicit (both parts
   of a macro location: `spellingLoc`, `expansionLoc`).
3. **Projection.** Of a kept node, only the keys in `TOP_KEYS` are written, and of its `type`
   only `qualType` and `desugaredQualType`. Of its children (`inner`), only the kinds the
   import reads are written: `ParmVarDecl` (`id`, `kind`, `name`, `type` as above), attributes
   (kinds ending in `Attr`: `id`, `kind`, `visibility`), `CompoundStmt` (`id`, `kind`: that
   the declaration has a body) and `EnumConstantDecl` (`id`, `kind`, `name`). Everything else
   (ranges, columns and offsets, other children, type nodes) is dropped. Values are clang's.
4. **Ids renumbered.** Clang's node ids are heap addresses and differ from run to run. Every
   kept `id` is replaced by `0x` followed by the hexadecimal index of its first appearance in
   the output (starting at 1).
5. **Layout.** Compact ASCII JSON (no spaces, non-ASCII escaped), with the root's `inner`
   written one kept node per line, and a final newline. Keys keep clang's order.
"""
import json
import sys

TOP_KEYS = ["id", "kind", "loc", "isImplicit", "name", "mangledName", "type", "storageClass",
            "variadic", "inline", "tagUsed", "completeDefinition", "inner"]


class Chain:
    """The delta-encoding state of clang's location printer."""

    def __init__(self):
        self.file = None
        self.line = None

    def bare(self, loc):
        """Advance over one bare location; its resolved (file, line), or None if empty."""
        if not loc:
            return None
        if "file" in loc:
            self.file = loc["file"]
        if "line" in loc:
            self.line = loc["line"]
        return {"file": self.file, "line": self.line}

    def loc(self, loc):
        """A location (bare, or macro with spelling and expansion), resolved; and its file
        (of the expansion)."""
        if "spellingLoc" in loc:
            s = self.bare(loc["spellingLoc"])
            e = self.bare(loc["expansionLoc"])
            out = {}
            if s is not None:
                out["spellingLoc"] = s
            if e is not None:
                out["expansionLoc"] = e
            return out, (e or {}).get("file")
        r = self.bare(loc)
        return (r or {}), (r or {}).get("file")


def advance(node, chain):
    """Advance the chain over a node in print order. Returns its resolved `loc` and file."""
    own, own_file = None, None
    if not isinstance(node, dict):
        return own, own_file
    for k, v in node.items():
        if k == "loc":
            own, own_file = chain.loc(v)
        elif k == "range":
            for vv in v.values():
                chain.loc(vv)
        elif k in ("inner", "array_filler"):
            for c in v:
                advance(c, chain)
    return own, own_file


def qual(t):
    return {k: v for k, v in t.items() if k in ("qualType", "desugaredQualType")}


def child(c):
    """The projection of a child, or None if the import does not read its kind."""
    if not isinstance(c, dict) or "kind" not in c:
        return None
    k = c["kind"]
    if k == "ParmVarDecl":
        keep = ["id", "kind", "name", "type"]
    elif k.endswith("Attr"):
        keep = ["id", "kind", "visibility"]
    elif k in ("CompoundStmt", "EnumConstantDecl"):
        keep = ["id", "kind", "name"]
    else:
        return None
    return {kk: (qual(c[kk]) if kk == "type" else c[kk]) for kk in c if kk in keep}


def project(node, loc):
    out = {}
    for k, v in node.items():
        if k not in TOP_KEYS:
            continue
        if k == "loc":
            v = loc
        elif k == "type":
            v = qual(v)
        elif k == "inner":
            v = [p for p in (child(c) for c in v) if p is not None]
            if not v:
                continue
        out[k] = v
    return out


def renumber(x, table):
    if isinstance(x, dict):
        return {k: (table.setdefault(v, "0x%x" % (len(table) + 1))
                    if k == "id" and isinstance(v, str) else renumber(v, table))
                for k, v in x.items()}
    if isinstance(x, list):
        return [renumber(v, table) for v in x]
    return x


def main():
    files = set(sys.argv[1:])
    tu = json.load(sys.stdin)
    if tu.get("kind") != "TranslationUnitDecl":
        raise SystemExit("filter: not a TranslationUnitDecl")
    chain = Chain()
    kept = []
    for node in tu.get("inner", []):
        loc, f = advance(node, chain)
        if f in files:
            kept.append(project(node, loc))
    table = {}
    root = renumber({"id": tu["id"], "kind": tu["kind"]}, table)
    kept = [renumber(n, table) for n in kept]
    dump = lambda v: json.dumps(v, separators=(",", ":"), ensure_ascii=True)
    head = dump(root)[:-1]
    body = ",\n".join(dump(n) for n in kept)
    sys.stdout.write(head + ',"inner":[\n' + body + "\n]}\n")


if __name__ == "__main__":
    main()
