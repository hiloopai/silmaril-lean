#!/usr/bin/env python3
"""Check the translated object-order and entry-recognizer slice and emit its Lean data."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_status_accessors import NIL, ROOT, TRUTH, call, functions, object_term, quote, same, sym

FIXTURE = ROOT / "corpus/acl2/x86-order/acl2-8.7.json"
SOURCE = ROOT / "Silmaril/Logic/ACL2/X86Run/Status/RecordSource.lean"
EXPORT_SHA256 = "cb77542025f89ab900def3282353ee3a102a1192cd5a3c6bb5f04f994335eac0"


def check_order(check):
    nil, truth = quote(NIL), quote(TRUTH)

    def alphorder(x, y):
        real_x, real_y = call("REALPART", x), call("REALPART", y)
        less_real = call("<", real_x, real_y)
        complex_le = call("IF", less_real, less_real,
                          call("IF", call("=", real_x, real_y),
                               call("NOT", call("<", call("IMAGPART", y), call("IMAGPART", x))), nil))
        cases = [
            ("RATIONALP", call("NOT", call("<", y, x))),
            ("ACL2:COMPLEX-RATIONALP", complex_le),
            ("CHARACTERP", call("NOT", call("<", call("CHAR-CODE", y), call("CHAR-CODE", x)))),
            ("STRINGP", call("IF", call("STRING<=", x, y), truth, nil)),
            ("SYMBOLP", call("NOT", call("ACL2:SYMBOL<", y, x))),
        ]
        body = call("ACL2:BAD-ATOM<=", x, y)
        for predicate, same_category in reversed(cases):
            body = call("IF", call(predicate, x),
                        call("IF", call(predicate, y), same_category, truth),
                        call("IF", call(predicate, y), nil, body))
        return body

    def symbol_less(x, y):
        a, b = sym("ACL2", "X1"), sym("ACL2", "Y1")
        smaller = call("STRING<", a, b)
        names = call("IF", smaller, smaller,
                     call("IF", call("EQUAL", a, b),
                          call("STRING<", call("ACL2:SYMBOL-PACKAGE-NAME", x),
                               call("ACL2:SYMBOL-PACKAGE-NAME", y)), nil))
        return [call("LAMBDA", [a, b, y, x], names), call("SYMBOL-NAME", x),
                call("SYMBOL-NAME", y), y, x]

    def string_list(x, y, offset):
        return call("IF", call("ENDP", x), call("IF", call("ENDP", y), nil, offset),
                    call("IF", call("ENDP", y), nil,
                         call("IF", call("EQL", call("CAR", x), call("CAR", y)),
                              call("ACL2:STRING<-L", call("CDR", x), call("CDR", y),
                                   call("ACL2:BINARY-+", offset, quote(1))),
                              call("IF", call("CHAR<", call("CAR", x), call("CAR", y)), offset, nil))))

    check("ACL2", "<<", 2, lambda x, y:
          call("IF", call("ACL2:LEXORDER", x, y), call("NOT", call("EQUAL", x, y)), nil))
    check("ACL2", "LEXORDER", 2, lambda x, y:
          call("IF", call("ATOM", x), call("IF", call("ATOM", y), call("ACL2:ALPHORDER", x, y), truth),
               call("IF", call("ATOM", y), nil,
                    call("IF", call("EQUAL", call("CAR", x), call("CAR", y)),
                         call("ACL2:LEXORDER", call("CDR", x), call("CDR", y)),
                         call("ACL2:LEXORDER", call("CAR", x), call("CAR", y))))))
    check("ACL2", "ALPHORDER", 2, alphorder)
    check("ACL2", "SYMBOL<", 2, symbol_less)
    check("ACL2", "STRING<-L", 3, string_list)
    check("COMMON-LISP", "CHAR<", 2,
          lambda x, y: call("<", call("CHAR-CODE", x), call("CHAR-CODE", y)))
    check("COMMON-LISP", "ENDP", 1, lambda x: call("ATOM", x))
    check("COMMON-LISP", "STRING<", 2, lambda x, y:
          call("ACL2:STRING<-L", call("COERCE", x, quote(sym("COMMON-LISP", "LIST"))),
               call("COERCE", y, quote(sym("COMMON-LISP", "LIST"))), quote(0)))
    check("COMMON-LISP", "STRING<=", 2, lambda x, y:
          call("IF", call("EQUAL", x, y), call("LENGTH", x), call("STRING<", x, y)))


def check_record(check):
    nil = quote(NIL)

    def p1(x):
        entry, tail = call("CAR", x), call("CDR", x)
        key, value = call("CAR", entry), call("CDR", entry)
        null_tail = call("NULL", tail)
        body = call("IF", null_tail, null_tail, call("ACL2:<<", key, call("CAR", call("CAR", tail))))
        tests = [call("CONSP", x), call("CONSP", entry), call("X86ISA:X86REC-P1", tail),
                 call("X86ISA:X86-ELEM-P-TOP", key, value),
                 call("NOT", call("EQUAL", value, call("X86ISA:X86-ELEM-DEFAULT-TOP", key)))]
        for test in reversed(tests):
            body = call("IF", test, body, nil)
        return call("IF", call("NULL", x), call("NULL", x), body)

    check("X86ISA", "X86REC-P1", 1, p1)
    check("X86ISA", "X86-ELEM-P-TOP", 2, lambda k, x: call("X86ISA:X86-ELEM-P", call("CAR", k), x))
    check("X86ISA", "X86-ELEM-DEFAULT-TOP", 1, lambda k: call("X86ISA:X86-ELEM-DEFAULT", call("CAR", k)))
    def tty_buffer(x):
        body = call("IF", call("NULL", x), call("NULL", x),
                    call("IF", call("CONSP", x),
                         call("IF", call("ACL2:UNSIGNED-BYTE-P", quote(8), call("CAR", x)),
                              call("X86ISA:TTY-BUFFERP", call("CDR", x)), nil), nil))
        return [call("LAMBDA", [sym("ACL2", "__FUNCTION__"), x], body),
                quote(sym("X86ISA", "TTY-BUFFERP")), x]

    check("X86ISA", "TTY-BUFFERP", 1, tty_buffer)


def field_cases(term, formal, fallback):
    result = {}
    while term[0] == sym("COMMON-LISP", "IF"):
        _, test, yes, term = term
        _, _, (_, field) = test
        same(test, call("EQL", formal, quote(field)), "field discriminator")
        if len(field) != 3 or field[:2] != ["symbol", "KEYWORD"] or field[2] in result:
            raise ValueError("expected a distinct package-qualified field")
        result[field[2]] = yes
    same(term, quote(fallback), "field dispatch fallback")
    return result


def field_type(term, value):
    if term == quote(TRUTH):
        return ".any"
    names = {"ACL2:BOOLEANP": ".boolean", "COMMON-LISP:KEYWORDP": ".keyword", "ACL2:NATP": ".natural",
             "X86ISA:ENV-ALISTP": ".environment", "X86ISA:TLBP": ".tlb", "X86ISA:TTY-BUFFERP": ".tty"}
    for name, constructor in names.items():
        if term == call(name, value):
            return constructor
    for name, constructor in [("ACL2:SIGNED-BYTE-P", ".signed"), ("ACL2:UNSIGNED-BYTE-P", ".unsigned")]:
        if term[0] != call(name)[0]:
            continue
        _, (_, width), _ = term
        if type(width) is not int or width <= 0:
            raise ValueError("expected a positive literal field width")
        same(term, call(name, quote(width), value), "field width predicate")
        return f"{constructor} {width}"
    raise ValueError("unsupported field predicate")


def bool_literal(value):
    if value not in (TRUTH, NIL):
        raise ValueError("expected a Boolean observation")
    return "true" if value == TRUTH else "false"


def generate(document):
    same(document["schema"], 1, "schema")
    same(document["x86isa_exec"], "nil", "profile")
    definitions = functions(document)

    def check(package, name, arity, body):
        args, term = definitions[package, name]
        same(len(args), arity, f"{name} arity")
        same(term, body(*args), f"{name} logical body")

    check_order(check)
    check_record(check)
    (key,), default_body = definitions["X86ISA", "X86-ELEM-DEFAULT"]
    (field, value), type_body = definitions["X86ISA", "X86-ELEM-P"]
    defaults = field_cases(default_body, key, NIL)
    types = field_cases(type_body, field, TRUTH)
    same(defaults.keys(), types.keys(), "field declaration sets")
    rows = []
    for field, default in defaults.items():
        _, literal = default
        same(default, quote(literal), "field default quotation")
        rows.append(f"  ⟨{object_term(sym('KEYWORD', field))}, {object_term(literal)}, "
                    f"{field_type(types[field], value)}⟩")
    order = []
    for a, b, *results in document["order_observations"]:
        result = ", ".join(map(bool_literal, results))
        order.append(f"  ({object_term(a)}, {object_term(b)}, {result})")
    entries = [f"  ({object_term(value)}, {bool_literal(result)})"
               for value, result in document["entry_observations"]]
    rules = ",\n".join(rows)
    order_rows = ",\n".join(order)
    entry_rows = ",\n".join(entries)
    return f"""-- Generated from the certified export by tools/acl2-x86isa/check_object_order.py.
module

public import Silmaril.Logic.ACL2.X86Run.Status.RecordDefs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.Status

open Standard

def fieldRules : List FieldRule := [
{rules}]

def orderObservations : List (Object × Object × Bool × Bool × Bool × Bool) := [
{order_rows}]

def entryObservations : List (Object × Bool) := [
{entry_rows}]

end Silmaril.Logic.ACL2.X86Run.Status
"""


def checked_source(data):
    if sha256(data).hexdigest() != EXPORT_SHA256:
        raise ValueError("export differs from the pinned certified order artifact")
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
        with tempfile.TemporaryDirectory(prefix="lean-x86-order-") as directory:
            path = Path(directory) / "RecordSource.lean"
            path.write_text(generated, encoding="utf-8")
            subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                            "-DwarningAsError=true", str(path)], cwd=ROOT, check=True)
    print("Object order and record rules match the pinned certified export")


if __name__ == "__main__":
    main()
