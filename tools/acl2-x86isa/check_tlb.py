#!/usr/bin/env python3
"""Check the pinned TLB closure and emit its Lean constants and observations."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_environment import define_body
from check_object_order import bool_literal
from check_status_accessors import NIL, ROOT, call, functions, object_term, quote, same, sym

FIXTURE = ROOT / "corpus/acl2/x86-tlb/acl2-8.7.json"
SOURCE = ROOT / "Silmaril/Logic/ACL2/X86Run/Status/TlbSource.lean"
EXPORT_SHA256 = "6f78907ac56fa95d36abc83be9402c617c29bd8c7fd6ee8aa460f72b2ca88cd9"


def bind(formals, body, *values):
    return [call("LAMBDA", formals, body), *values]


def natural(term):
    _, value = term
    if type(value) is not int or value < 0:
        raise ValueError("expected a quoted natural")
    same(term, quote(value), "quoted natural")
    return value


def check_arithmetic(check):
    def quotient(i, j):
        zero = quote(0)
        is_zero = call("=", call("ACL2:NFIX", j), zero)
        stop = call("IF", is_zero, is_zero, call("<", call("ACL2:IFIX", i), j))
        smaller = call("ACL2:BINARY-+", i, call("ACL2:UNARY--", j))
        step = call("ACL2:NONNEGATIVE-INTEGER-QUOTIENT", smaller, j)
        return call("IF", stop, zero, call("ACL2:BINARY-+", quote(1), step))

    def floor(i, j):
        q, n, d = [sym("ACL2", name) for name in ("Q", "N", "D")]
        pos = call("ACL2:NONNEGATIVE-INTEGER-QUOTIENT", n, d)
        neg = call("ACL2:NONNEGATIVE-INTEGER-QUOTIENT", call("ACL2:UNARY--", n), d)
        branch = call("IF", call("NOT", call("<", n, quote(0))), pos,
                      call("ACL2:BINARY-+", call("ACL2:UNARY--", neg), quote(-1)))
        body = call("IF", call("=", d, quote(1)), n, branch)
        body = bind([d, n], body, call("DENOMINATOR", q), n)
        body = bind([n, q], body, call("NUMERATOR", q), q)
        return bind([q], body, call("ACL2:BINARY-*", i, call("ACL2:UNARY-/", j)))

    nil, zero = quote(NIL), quote(0)
    check("ACL2", "NONNEGATIVE-INTEGER-QUOTIENT", 2, quotient)
    check("COMMON-LISP", "FLOOR", 2, floor)
    check("COMMON-LISP", "MOD", 2, lambda x, y:
          call("ACL2:BINARY-+", x, call("ACL2:UNARY--", call("ACL2:BINARY-*", call("FLOOR", x, y), y))))
    check("ACL2", "IFIX", 1, lambda x: call("IF", call("INTEGERP", x), x, zero))
    check("ACL2", "NFIX", 1, lambda x:
          call("IF", call("IF", call("INTEGERP", x), call("NOT", call("<", x, zero)), nil), x, zero))
    check("ACL2", "UNSIGNED-BYTE-P", 2, lambda width, x:
          call("IF", call("INTEGERP", width),
               call("IF", call("NOT", call("<", width, zero)),
                    call("ACL2:INTEGER-RANGE-P", zero, call("EXPT", quote(2), width), x), nil), nil))
    check("ACL2", "INTEGER-RANGE-P", 3, lambda lo, hi, x:
          call("IF", call("INTEGERP", x),
               call("IF", call("NOT", call("<", x, lo)), call("<", x, hi), nil), nil))


def check_access_path(check, key_width, mode_width, offset):
    check("X86ISA", "TLB-KEY-P", 1, lambda x: call("ACL2:UNSIGNED-BYTE-P", quote(key_width), x))
    check("X86ISA", "TLB-KEY-FIX", 1, lambda x: call("ACL2:LOGHEAD$INLINE", quote(key_width), x))
    check("X86ISA", "TLB-KEY->R-W-X$INLINE", 1, lambda x:
          bind([x], call("BITOPS:PART-SELECT-WIDTH-LOW$INLINE", x, quote(mode_width), quote(offset)),
               call("X86ISA:TLB-KEY-FIX", x)))
    check("BITOPS", "PART-SELECT-WIDTH-LOW$INLINE", 3, lambda x, width, low:
          call("ACL2:LOGHEAD$INLINE", width, call("ACL2:LOGTAIL$INLINE", low, x)))
    check("ACL2", "LOGHEAD$INLINE", 2, lambda size, i:
          call("ACL2:IMOD$INLINE", i, call("ACL2:EXPT2$INLINE", size)))
    check("ACL2", "LOGTAIL$INLINE", 2, lambda pos, i:
          call("ACL2:IFLOOR$INLINE", i, call("ACL2:EXPT2$INLINE", pos)))
    check("ACL2", "IFLOOR$INLINE", 2, lambda i, j: call("FLOOR", call("ACL2:IFIX", i), call("ACL2:IFIX", j)))
    check("ACL2", "IMOD$INLINE", 2, lambda i, j: call("MOD", call("ACL2:IFIX", i), call("ACL2:IFIX", j)))
    check("ACL2", "EXPT2$INLINE", 1, lambda n: call("EXPT", quote(2), call("ACL2:NFIX", n)))


def check_predicates(check, marker, page_width, max_mode):
    nil = quote(NIL)

    def tlb(x):
        el, tail = sym("X86ISA", "EL"), sym("X86ISA", "TAIL")
        body = call("IF", call("X86ISA:TLB-ENTRYP", el), call("X86ISA:TLBP", tail), nil)
        branch = bind([el, x], bind([tail, el], body, call("CDR", x), el), call("CAR", x), x)
        return define_body("TLBP", x, call("IF", call("CONSP", x), branch, call("EQUAL", x, quote(marker))))

    def entry(x):
        key, val = sym("X86ISA", "KEY"), sym("X86ISA", "VAL")
        body = call("IF", call("X86ISA:GOOD-TLB-KEY-P", key),
                    call("ACL2:UNSIGNED-BYTE-P", quote(page_width), val), nil)
        branch = bind([key, x], bind([val, key], body, call("CDR", x), key), call("CAR", x), x)
        return define_body("TLB-ENTRYP", x, call("IF", call("CONSP", x), branch, nil))

    def good(x):
        body = call("NOT", call("<", quote(max_mode), call("X86ISA:TLB-KEY->R-W-X$INLINE", x)))
        return define_body("GOOD-TLB-KEY-P", x, call("IF", call("X86ISA:TLB-KEY-P", x), body, nil))

    check("X86ISA", "TLBP", 1, tlb)
    check("X86ISA", "TLB-ENTRYP", 1, entry)
    check("X86ISA", "GOOD-TLB-KEY-P", 1, good)


def check_theorems(rows, key_width, mode_width, offset):
    theorems = {tuple(name[1:]): term for name, term in rows}
    x = sym("ACL2", "X")
    same(theorems["X86ISA", "TLB-KEY-FIX-WHEN-TLB-KEY-P"],
         call("ACL2:IMPLIES", call("X86ISA:TLB-KEY-P", x),
              call("EQUAL", call("X86ISA:TLB-KEY-FIX", x), x)), "TLB key fix formula")
    k = sym("X86ISA", "KEY")
    same(theorems["X86ISA", "C3-RWX-FLOOR-MOD"],
         call("ACL2:IMPLIES", call("ACL2:UNSIGNED-BYTE-P", quote(key_width), k),
              call("EQUAL", call("X86ISA:TLB-KEY->R-W-X$INLINE", k),
                   call("MOD", call("FLOOR", k, quote(2 ** offset)), quote(2 ** mode_width)))),
         "bit selection formula")


def generate(document):
    same(document["schema"], 1, "schema")
    same(document["x86isa_exec"], "nil", "profile")
    declarations = functions(document)

    def check(package, name, arity, body):
        args, logical = declarations[package, name]
        same(len(args), arity, f"{name} arity")
        same(logical, body(*args), f"{name} logical body")

    key_width = natural(declarations["X86ISA", "TLB-KEY-P"][1][1])
    _, _, mode_width, offset = declarations["X86ISA", "TLB-KEY->R-W-X$INLINE"][1][0][2]
    mode_width, offset = natural(mode_width), natural(offset)
    tlb_body = declarations["X86ISA", "TLBP"][1][0][2]
    marker = tlb_body[3][2][1]
    if marker[:2] != ["symbol", "KEYWORD"]:
        raise ValueError("expected a keyword TLB terminator")
    entry_body = declarations["X86ISA", "TLB-ENTRYP"][1][0][2]
    page_width = natural(entry_body[2][0][2][0][2][2][1])
    good_body = declarations["X86ISA", "GOOD-TLB-KEY-P"][1][0][2]
    max_mode = natural(good_body[2][1][1])

    check_arithmetic(check)
    check_access_path(check, key_width, mode_width, offset)
    check_predicates(check, marker, page_width, max_mode)
    check_theorems(document["theorems"], key_width, mode_width, offset)

    arithmetic = ",\n".join(f"  ({n}, {d}, {q}, {floor}, {mod})"
                           for n, d, q, floor, mod in document["arithmetic_observations"])
    keys = ",\n".join(f"  ({object_term(k)}, {bool_literal(valid)}, {bool_literal(good)}, {object_term(mode)})"
                     for k, valid, good, mode in document["key_observations"])
    observations = ",\n".join(
        f"  ({object_term(tlb)}, {bool_literal(tlb_ok)},\n"
        f"    {object_term(entries)}, {bool_literal(entries_ok)}, {bool_literal(state_ok)}, "
        f"{object_term(ms)}, {object_term(fault)})"
        for tlb, tlb_ok, entries, entries_ok, state_ok, ms, fault in document["observations"])
    return f"""-- Generated from the certified world by tools/acl2-x86isa/check_tlb.py.
module

public import Silmaril.Logic.ACL2.X86Run.Status.TlbDefs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.Status.Tlb

open Standard

def layout : Layout where
  marker := {object_term(marker)}
  keyWidth := {key_width}
  pageWidth := {page_width}
  modeWidth := {mode_width}
  modeOffset := {offset}
  maxMode := {max_mode}

def tlbP : Object → Bool := recognizes layout

def arithmeticObservations : List (Int × Nat × Nat × Int × Int) := [
{arithmetic}]

def keyObservations : List (Object × Bool × Bool × Object) := [
{keys}]

def tlbObservations : List (Object × Bool × Object × Bool × Bool × Object × Object) := [
{observations}]

end Silmaril.Logic.ACL2.X86Run.Status.Tlb
"""


def checked_source(data):
    if sha256(data).hexdigest() != EXPORT_SHA256:
        raise ValueError("export differs from the pinned certified TLB artifact")
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
    except (IndexError, KeyError, TypeError, ValueError) as error:
        parser.exit(1, f"{error}\n")
    if not args.compare:
        with tempfile.TemporaryDirectory(prefix="lean-x86-tlb-") as directory:
            path = Path(directory) / "TlbSource.lean"
            path.write_text(generated, encoding="utf-8")
            subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                            "-DwarningAsError=true", str(path)], cwd=ROOT, check=True)
    print("TLB recognizer matches the pinned certified export")


if __name__ == "__main__":
    main()
