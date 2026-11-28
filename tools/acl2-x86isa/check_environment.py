#!/usr/bin/env python3
"""Check the pinned ENV-ALISTP closure and emit its Lean recognizer and observations."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_object_order import bool_literal
from check_status_accessors import NIL, ROOT, TRUTH, call, functions, object_term, quote, same, sym

FIXTURE = ROOT / "corpus/acl2/x86-environment/acl2-8.7.json"
SOURCE = ROOT / "Silmaril/Logic/ACL2/X86Run/Status/EnvironmentSource.lean"
EXPORT_SHA256 = "6fedc848bea2d78ae15de964b4848414e91fe88fc4cf938c4eafa1f6adaec48d"


def define_body(name, formal, body):
    return [call("LAMBDA", [sym("ACL2", "__FUNCTION__"), formal], body),
            quote(sym("X86ISA", name)), formal]


def check_helpers(check):
    nil = quote(NIL)
    check("COMMON-LISP", "NOT", 1, lambda x: call("IF", x, nil, quote(TRUTH)))
    check("COMMON-LISP", "ATOM", 1, lambda x: call("NOT", call("CONSP", x)))
    check("COMMON-LISP", "ENDP", 1, lambda x: call("ATOM", x))
    check("COMMON-LISP", "EQ", 2, lambda x, y: call("EQUAL", x, y))
    check("ACL2", "ALISTP", 1, lambda x:
          call("IF", call("ATOM", x), call("EQ", x, nil),
               call("IF", call("CONSP", call("CAR", x)), call("ACL2:ALISTP", call("CDR", x)), nil)))
    check("ACL2", "TRUE-LISTP", 1, lambda x:
          call("IF", call("CONSP", x), call("ACL2:TRUE-LISTP", call("CDR", x)), call("EQ", x, nil)))
    check("ACL2", "LEN", 1, lambda x:
          call("IF", call("CONSP", x), call("ACL2:BINARY-+", quote(1), call("ACL2:LEN", call("CDR", x))),
               quote(0)))
    check("ACL2", "ASSOC-EQUAL", 2, lambda k, x:
          call("IF", call("ENDP", x), nil,
               call("IF", call("EQUAL", k, call("CAR", call("CAR", x))), call("CAR", x),
                    call("ACL2:ASSOC-EQUAL", k, call("CDR", x)))))

    def rip_ret(x):
        entry = call("CAR", x)
        recur = call("X86ISA:RIP-RET-ALISTP", call("CDR", x))
        body = call("IF", call("ATOM", x), call("EQUAL", x, nil),
                    call("IF", call("CONSP", entry),
                         call("IF", call("X86ISA:I48P$INLINE", call("CAR", entry)),
                              call("IF", call("ACL2:TRUE-LISTP", call("CDR", entry)), recur, nil), nil), nil))
        return define_body("RIP-RET-ALISTP", x, body)

    check("X86ISA", "RIP-RET-ALISTP", 1, rip_ret)


def check_arithmetic(check):
    nil = quote(NIL)

    def signed_byte(bits, x):
        limit = sym("ACL2", "Y")
        body = call("ACL2:INTEGER-RANGE-P", call("ACL2:UNARY--", limit), limit, x)
        bound = call("EXPT", quote(2), call("ACL2:BINARY-+", quote(-1), bits))
        branch = [call("LAMBDA", [limit, x], body), bound, x]
        return call("IF", call("INTEGERP", bits), call("IF", call("<", quote(0), bits), branch, nil), nil)

    def power(base, i):
        up = call("EXPT", base, call("ACL2:BINARY-+", i, quote(-1)))
        down = call("EXPT", base, call("ACL2:BINARY-+", i, quote(1)))
        return call("IF", call("ACL2:ZIP", i), quote(1),
                    call("IF", call("=", call("ACL2:FIX", base), quote(0)), quote(0),
                         call("IF", call("<", quote(0), i), call("ACL2:BINARY-*", base, up),
                              call("ACL2:BINARY-*", call("ACL2:UNARY-/", base), down))))

    check("ACL2", "SIGNED-BYTE-P", 2, signed_byte)
    check("ACL2", "INTEGER-RANGE-P", 3, lambda lo, hi, x:
          call("IF", call("INTEGERP", x),
               call("IF", call("NOT", call("<", x, lo)), call("<", x, hi), nil), nil))
    check("COMMON-LISP", "EXPT", 2, power)


def environment_fields(formal, term):
    """Read the native finite conjunction and retain the actual quoted keys and count."""
    nil = quote(NIL)
    ((_, _, body), _, _) = term
    nil_env = call("EQUAL", formal, nil)
    tests = []
    rest = body[3]
    while isinstance(rest, list) and rest and rest[0] == call("IF")[0]:
        _, test, yes, no = rest
        same(no, nil, "ENV-ALISTP conjunct fallback")
        tests.append(test)
        rest = yes

    same(len(tests), 7, "ENV-ALISTP conjunct count")
    _, length, *fields = tests
    count = length[2][1]
    if type(count) is not int or count < 0:
        raise ValueError("expected a natural environment length")
    same(tests[:2], [call("ACL2:ALISTP", formal), call("EQUAL", call("ACL2:LEN", formal), quote(count))],
         "ENV-ALISTP list/length tests")
    keys = []
    predicates = ["ACL2:ALISTP", "ACL2:ALISTP", "X86ISA:RIP-RET-ALISTP"]
    for shape, check_value, predicate in zip(fields[::2], fields[1::2] + [rest], predicates):
        _, lookup = shape
        key = lookup[1][1]
        if key[:2] != ["symbol", "KEYWORD"] or key in keys:
            raise ValueError("expected a distinct package-qualified environment key")
        same(shape, call("CONSP", call("ACL2:ASSOC-EQUAL", quote(key), formal)),
             "ENV-ALISTP required association")
        same(check_value, call(predicate, call("CDR", lookup)), "ENV-ALISTP subfield predicate")
        keys.append(key)
    same(term, define_body("ENV-ALISTP", formal, call("IF", nil_env, nil_env, body[3])),
         "ENV-ALISTP logical wrapper")
    return count, keys


def generate(document):
    same(document["schema"], 1, "schema")
    same(document["x86isa_exec"], "nil", "profile")
    declarations = functions(document)

    def check(package, name, arity, body):
        args, logical = declarations[package, name]
        same(len(args), arity, f"{name} arity")
        same(logical, body(*args), f"{name} logical body")

    check_helpers(check)
    check_arithmetic(check)
    (_,), i48 = declarations["X86ISA", "I48P$INLINE"]
    width = i48[1][1]
    if type(width) is not int or width <= 0:
        raise ValueError("expected a positive oracle address width")
    check("X86ISA", "I48P$INLINE", 1, lambda x: call("ACL2:SIGNED-BYTE-P", quote(width), x))
    (formal,), environment = declarations["X86ISA", "ENV-ALISTP"]
    count, keys = environment_fields(formal, environment)
    descriptors, contents, oracle = map(object_term, keys)
    helpers = []
    for key, obj, match, length, alist, true_list, rip_ret in document["helper_observations"]:
        helpers.append(f"  ({object_term(key)}, {object_term(obj)}, {object_term(match)}, {length}, "
                       f"{bool_literal(alist)}, {bool_literal(true_list)}, {bool_literal(rip_ret)})")
    observations = []
    for label, env, valid_env, entries, valid_entries, valid_state, ms, fault in document["observations"]:
        observations.append(f'  ("{label[2]}", {object_term(env)}, {bool_literal(valid_env)},\n'
                            f"    {object_term(entries)}, {bool_literal(valid_entries)}, "
                            f"{bool_literal(valid_state)}, {object_term(ms)}, {object_term(fault)})")
    helpers_text = ",\n".join(helpers)
    observations_text = ",\n".join(observations)
    return f"""-- Generated from the certified world by tools/acl2-x86isa/check_environment.py.
module

public import Silmaril.Logic.ACL2.X86Run.Status.EnvironmentDefs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.Status.Environment

open Standard

def descriptorsKey : Object := {descriptors}
def contentsKey : Object := {contents}
def oracleKey : Object := {oracle}
def addressWidth : Nat := {width}
def fieldCount : Nat := {count}

/-- Non-NIL projection of the translated ENV-ALISTP body. -/
def envAlistP (env : Object) : Bool :=
  let descriptors := assocEqual descriptorsKey env
  let contents := assocEqual contentsKey env
  let oracle := assocEqual oracleKey env
  decide (env = .nil) ||
    (alistP env && decide (len env = fieldCount) &&
      descriptors.consp && alistP descriptors.cdr &&
      contents.consp && alistP contents.cdr &&
      oracle.consp && ripRetAlistP addressWidth oracle.cdr)

def helperObservations : List (Object × Object × Object × Nat × Bool × Bool × Bool) := [
{helpers_text}]

def environmentObservations :
    List (String × Object × Bool × Object × Bool × Bool × Object × Object) := [
{observations_text}]

end Silmaril.Logic.ACL2.X86Run.Status.Environment
"""


def checked_source(data):
    if sha256(data).hexdigest() != EXPORT_SHA256:
        raise ValueError("export differs from the pinned certified environment artifact")
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
        with tempfile.TemporaryDirectory(prefix="lean-x86-environment-") as directory:
            path = Path(directory) / "EnvironmentSource.lean"
            path.write_text(generated, encoding="utf-8")
            subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                            "-DwarningAsError=true", str(path)], cwd=ROOT, check=True)
    print("Environment recognizer matches the pinned certified export")


if __name__ == "__main__":
    main()
