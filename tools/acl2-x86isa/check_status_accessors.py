#!/usr/bin/env python3
"""Translate the pinned FAULT/MS world slice to checked Lean accessor declarations."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_x86_run import NIL, ROOT, TRUTH, is_symbol, symbol

FIXTURE = ROOT / "corpus/acl2/x86-status/acl2-8.7.json"
SOURCE = ROOT / "Silmaril/Logic/ACL2/X86Run/Status/Source.lean"
EXPORT_SHA256 = "481d502d3980285e97fae81c58c9841a19750490c14549219b819ad8c414ae7c"


def sym(package, spelling):
    return ["symbol", package, spelling]


def call(name, *args):
    """Unqualified names here are Common Lisp primitives."""
    package, separator, spelling = name.partition(":")
    return [sym(package, spelling) if separator else sym("COMMON-LISP", name), *args]


def quote(value):
    return call("QUOTE", value)


def same(actual, expected, label):
    if actual != expected:
        raise ValueError(f"unexpected {label}")


def functions(document):
    """Check arities and index definitions by their package-qualified names."""
    result = {}
    for name, arity, formals, _raw, logical, *_metadata in document["functions"]:
        key = symbol(name)
        if key in result or type(arity) is not int or arity != len(formals):
            raise ValueError(f"invalid declaration for {key}")
        for formal in formals:
            symbol(formal)
        if any(formals.count(formal) != 1 for formal in formals):
            raise ValueError(f"duplicate formal in {key}")
        result[key] = (formals, logical)
    return result


def check_record_path(definitions):
    """Match the complete translated bodies used by Status.Defs."""
    def check(name, arity, make_body):
        args, term = definitions["X86ISA", name]
        same(len(args), arity, f"{name} arity")
        same(term, make_body(*args), f"{name} logical body")

    check("XR", 3, lambda field, index, state:
          call("X86ISA:X86REC-GET", call("CONS", field, index), state))
    check("X86REC-GET", 2, lambda key, state:
          call("X86ISA:X86REC-GET1", key, call("CAR", call("X86ISA:X86REC-TO-MTR", state))))
    check("X86REC-TO-MTR", 1, lambda x:
          call("IF", call("X86ISA:X86REC-P", x), x, call("CONS", quote(NIL), x)))
    check("X86REC-P", 1, lambda x:
          call("IF", call("CONSP", x),
               call("IF", call("X86ISA:X86REC-P1", call("CAR", x)),
                    call("IF", call("CAR", x), call("NOT", call("X86ISA:X86REC-P", call("CDR", x))),
                         quote(NIL)), quote(NIL)), quote(NIL)))
    check("X86REC-BAD-PART", 1, lambda x:
          call("IF", call("X86ISA:X86REC-P", x), call("CDR", x), x))
    check("X86$AP", 1, lambda x: call("NOT", call("X86ISA:X86REC-BAD-PART", x)))

    def lookup(key, rest):
        entry = call("CAR", rest)
        field = call("CAR", entry)
        end = call("ENDP", rest)
        return call("IF", call("IF", end, end, call("ACL2:<<", key, field)),
                    call("X86ISA:X86-ELEM-DEFAULT-TOP", key),
                    call("IF", call("EQUAL", key, field), call("CDR", entry),
                         call("X86ISA:X86REC-GET1", key, call("CDR", rest))))

    check("X86REC-GET1", 2, lookup)
    check("X86-ELEM-DEFAULT-TOP", 1, lambda key:
          call("X86ISA:X86-ELEM-DEFAULT", call("CAR", key)))


def field_default(definitions, field):
    """Specialize the exported EQL dispatch on a fixed keyword."""
    (formal,), term = definitions["X86ISA", "X86-ELEM-DEFAULT"]
    while term[0] == sym("COMMON-LISP", "IF"):
        _, test, yes, no = term
        operator, variable, candidate = test
        same(operator, sym("COMMON-LISP", "EQL"), "field discriminator")
        same(variable, formal, "field discriminator variable")
        same(candidate[0], sym("COMMON-LISP", "QUOTE"), "field discriminator quotation")
        if candidate == quote(field):
            operator, value = yes
            same(operator, sym("COMMON-LISP", "QUOTE"), "field default quotation")
            return value
        term = no
    raise ValueError(f"missing field default for {field!r}")


def accessor_declarations(document, definitions):
    result = []
    obligations = []
    same(document["abstract_stobj"], sym("X86ISA", "X86"), "abstract stobj")
    same(document["foundation"], sym("X86ISA", "X86$C"), "foundation")
    same(document["correspondence_relation"], sym("X86ISA", "X86-CORR"), "correspondence relation")
    tuples = document["accessor_tuples"]
    same(tuples, [[sym("X86ISA", spelling + suffix) for suffix in ("", "$A", "$C")]
                  for spelling in ("FAULT", "MS")], "accessor tuples")
    for exported, abstract, concrete in tuples:
        name = exported[2]
        (x,), wrapper = definitions[symbol(exported)]
        (a,), abstract_body = definitions[symbol(abstract)]
        (c,), concrete_body = definitions[symbol(concrete)]
        same(wrapper, [abstract, x], f"{name} wrapper")
        field = sym("KEYWORD", name)
        same(abstract_body, call("X86ISA:XR", quote(field), quote(NIL), a), f"{name} abstract body")
        _, (_, slot), _ = concrete_body
        if type(slot) is not int or slot < 0:
            raise ValueError(f"invalid concrete slot for {name}")
        same(concrete_body, call("NTH", quote(slot), c), f"{name} concrete body")
        obligations.append([sym("X86ISA", name + "{CORRESPONDENCE}"),
                            call("ACL2:IMPLIES", [document["correspondence_relation"], c, x],
                                 call("EQUAL", [concrete, c], [abstract, x]))])
        result.append(f"def {name.lower()} : Accessor := "
                      f"⟨{object_term(field)}, {object_term(field_default(definitions, field))}, {slot}⟩")
    same(document["correspondence_obligations"], obligations, "correspondence obligations")
    return "\n\n".join(result)


def object_term(value):
    if value == NIL:
        return "Object.nil"
    if value == TRUTH:
        return "Object.truth"
    if type(value) is int:
        return f"Object.integer ({value})"
    if is_symbol(value):
        package, spelling = map(json.dumps, symbol(value))
        return f"Object.symbol ((Symbol.ofName? ⟨{package}, {spelling}⟩).get (by decide))"
    if isinstance(value, list) and len(value) == 3 and value[0] == "pair":
        return f"Object.cons ({object_term(value[1])}) ({object_term(value[2])})"
    if isinstance(value, list) and value:
        return "Object.ofList [" + ", ".join(map(object_term, value)) + "]"
    raise ValueError(f"unsupported observation object {value!r}")


def generate(document):
    same(document["schema"], 1, "schema")
    same(document["x86isa_exec"], "nil", "profile")
    definitions = functions(document)
    check_record_path(definitions)
    declarations = accessor_declarations(document, definitions)
    observations = []
    for label, state, valid, ms, fault in document["samples"]:
        if valid not in (TRUTH, NIL):
            raise ValueError("invalid sample recognizer result")
        observations.append(
            f"  ⟨{json.dumps(symbol(label)[1])},\n    {object_term(state)},\n"
            f"    {'true' if valid == TRUTH else 'false'}, {object_term(ms)}, {object_term(fault)}⟩")
    entries = ",\n".join(observations)
    return f"""-- Generated by tools/acl2-x86isa/check_status_accessors.py from the certified export.
module

public import Silmaril.Logic.ACL2.X86Run.Status.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.Status

open Standard

{declarations}

def observations : List Observation := [
{entries}]

end Silmaril.Logic.ACL2.X86Run.Status
"""


def checked_source(data):
    if sha256(data).hexdigest() != EXPORT_SHA256:
        raise ValueError("export differs from the pinned certified accessor artifact")
    return generate(json.loads(data))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path, default=FIXTURE)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--emit", type=Path, help="write the generated Lean source")
    mode.add_argument("--compare", action="store_true", help="compare source already built by Lake")
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
        with tempfile.TemporaryDirectory(prefix="lean-x86-status-") as directory:
            path = Path(directory) / "Source.lean"
            path.write_text(generated, encoding="utf-8")
            subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean",
                            "-DautoImplicit=false", "-DwarningAsError=true", str(path)],
                           cwd=ROOT, check=True)
    print("FAULT and MS match the pinned certified accessor translation")


if __name__ == "__main__":
    main()
