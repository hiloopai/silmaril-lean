#!/usr/bin/env python3
"""Check logical DEFSTOBJ expansions against integer scalar and fixed-array schemas."""

import argparse
from dataclasses import dataclass
from hashlib import sha256
import json
from pathlib import Path
import re
import sys
from textwrap import indent

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_toy_defstobj import (
    EQUAL, FIXTURE as TOY, NIL, PRIMITIVES, QUOTE, ROOT, SUPPORT_DEFINITIONS,
    checked_source as checked_toy, require, symbol, term,
)


FIXTURE = ROOT / "corpus/acl2/defstobj-schema/acl2-8.7.json"
LEAN = ROOT / "Silmaril/Logic/ACL2/Standard/FixedLayout/Schema/Fixtures.lean"
PIN = "4c4b3a5d5481e5ee71c79da725d3707da89e5c0a3a38b245c4c3840214a399ec"
INPUT = Path(__file__).with_name("schema-defstobj.lsp")


def sym(name, package="ACL2"):
    return ["symbol", package, name]


def cl(name, *args):
    return [sym(name, "COMMON-LISP"), *args]


def call(name, *args):
    return [sym(name), *args]


def quote(value):
    return [sym("QUOTE", "COMMON-LISP"), value]


def acl2_name(value):
    package, name = symbol(value)
    require(package == "ACL2" and re.fullmatch(r"[A-Z][A-Z0-9-]*", name),
            f"unsupported DEFSTOBJ name {package}::{name}")
    return name


@dataclass(frozen=True)
class Slot:
    name: str
    initial: int
    size: int | None


def parse_layout(event):
    require(isinstance(event, list) and len(event) >= 3 and event[0] == sym("DEFSTOBJ"),
            "expected a nonempty DEFSTOBJ layout")
    record = acl2_name(event[1])
    slots = []
    for field in event[2:]:
        require(isinstance(field, list) and len(field) in (5, 7), "malformed field descriptor")
        name = acl2_name(field[0])
        pairs = [(symbol(key), value) for key, value in zip(field[1::2], field[2::2])]
        props = dict(pairs)
        require(len(props) == len(pairs), f"duplicate attribute for {name}")
        kind = props.pop(("KEYWORD", "TYPE"), None)
        initial = props.pop(("KEYWORD", "INITIALLY"), None)
        require(type(initial) is int, f"expected an explicit integer initializer for {name}")
        integer = sym("INTEGER", "COMMON-LISP")
        array = sym("ARRAY", "COMMON-LISP")
        if kind == integer:
            require(not props, f"unsupported scalar attributes for {name}")
            slots.append(Slot(name, initial, None))
        else:
            require(isinstance(kind, list) and len(kind) == 3 and kind[:2] == [array, integer],
                    f"unsupported field type for {name}")
            dimensions = kind[2]
            require(isinstance(dimensions, list) and len(dimensions) == 1
                    and type(dimensions[0]) is int and dimensions[0] >= 0,
                    f"expected one natural array dimension for {name}")
            require(props.pop(("KEYWORD", "RESIZABLE"), NIL) == NIL and not props,
                    f"unsupported or resizable array attributes for {name}")
            slots.append(Slot(name, initial, dimensions[0]))
    require(len({slot.name for slot in slots}) == len(slots), "duplicate slot name")
    return record, slots


@dataclass(frozen=True)
class Declaration:
    name: str
    lean: str
    params: tuple[str, ...]
    body: list
    takes_record: bool = False
    returns_record: bool = False
    recursive: bool = False
    call_binding: str | None = None
    model: str | None = None

    def row(self, record):
        inputs = [NIL] * len(self.params)
        if self.takes_record:
            inputs[-1] = sym(record)
        return [sym(self.name), len(self.params), [sym(p) for p in self.params] or NIL,
                inputs or NIL, [sym(record) if self.returns_record else NIL], self.body]


def declarations(record, slots):
    x, i, v, st = map(sym, ("X", "I", "V", record))
    predicates, operations, tests, values = [], [], [], []
    for position, slot in enumerate(slots):
        name, size = slot.name, slot.size
        predicate = name + "P"
        prefix = f"slot{position}"
        index = quote(position)
        field = cl("NTH", index, st)
        tests.append(call(predicate, field))
        if size is None:
            predicates.append(Declaration(predicate, prefix + "Recognizer", ("X",), cl("INTEGERP", x)))
            values.append(quote(slot.initial))
            operations += [
                Declaration(name, prefix + "Read", (record,), field, True,
                            model=f"Object.readAt {position}"),
                Declaration("UPDATE-" + name, prefix + "Write", ("V", record),
                            call("UPDATE-NTH", index, v, st), True, True,
                            model=f"Object.writeAt {position}"),
            ]
        else:
            pred_body = cl("IF", cl("ATOM", x), cl("EQUAL", x, quote(NIL)),
                           cl("IF", cl("INTEGERP", cl("CAR", x)),
                              call(predicate, cl("CDR", x)), quote(NIL)))
            predicates.append(Declaration(predicate, prefix + "Recognizer", ("X",), pred_body,
                                          recursive=True, call_binding="Schema.integerListP"))
            tests.append(cl("EQUAL", call("LEN", field), quote(size)))
            values.append(call("MAKE-LIST-AC", quote(size), quote(slot.initial), quote(NIL)))
            operations += [
                Declaration(name + "-LENGTH", prefix + "Length", (record,), quote(size), True),
                Declaration("RESIZE-" + name, prefix + "Resize", ("I", record), st, True, True),
                Declaration(name + "I", prefix + "Read", ("I", record), cl("NTH", i, field), True,
                            model=f"Schema.readCell {position}"),
                Declaration("UPDATE-" + name + "I", prefix + "Write", ("I", "V", record),
                            call("UPDATE-NTH-ARRAY", index, i, v, st), True, True,
                            model=f"Schema.writeCell {position}"),
            ]
    recognize = quote(sym("T", "COMMON-LISP"))
    leading_tests = [call("TRUE-LISTP", st), cl("=", cl("LENGTH", st), quote(len(slots)))]
    for test in reversed(leading_tests + tests):
        recognize = cl("IF", test, recognize, quote(NIL))
    create = quote(NIL)
    for value in reversed(values):
        create = cl("CONS", value, create)
    return predicates + [
        Declaration(record + "P", "recognizer", (record,), recognize, True,
                    model="Schema.recognizer layout"),
        Declaration("CREATE-" + record, "initial", (), create, returns_record=True,
                    model="Schema.initial layout"),
    ] + operations


def check_expansion(event, rows):
    """Validate the whole named expansion and its lexical and stobj signatures."""
    record, slots = parse_layout(event)
    expansion = declarations(record, slots)
    expected = [("ACL2", d.name) for d in expansion]
    reserved = set(PRIMITIVES) | set(SUPPORT_DEFINITIONS) | {("ACL2", record)}
    require(len(set(expected)) == len(expected) and not (set(expected) & reserved),
            "colliding generated declaration identities")
    actual = {symbol(row[0]): row for row in rows}
    require(len(actual) == len(rows) and set(actual) == set(expected),
            "missing, duplicate, or unsupported generated declarations")
    checked = []
    for decl, identifier in zip(expansion, expected):
        wanted, found = decl.row(record), actual[identifier]
        require(len(found) == len(wanted) and type(found[1]) is int
                and len(set(decl.params)) == len(decl.params)
                and wanted[:5] == found[:5], f"unexpected signature or formals for {decl.name}")
        require(wanted[5] == found[5], f"unexpected logical body for {decl.name}")
        checked.append((decl, identifier, found))
    return record, slots, checked


def render_fixture(namespace, event, rows, examples):
    record, slots, checked = check_expansion(event, rows)
    helpers = {
        name: (count, f"Source.{binding}" if binding in {"length", "numericEqual", "endp", "updateNthArray"}
               else binding)
        for name, (_, count, binding, _) in SUPPORT_DEFINITIONS.items()
    }
    available = {**PRIMITIVES, **helpers}

    specs = [f".scalar ({s.initial})" if s.size is None else f".array {s.size} ({s.initial})"
             for s in slots]
    text = [f"namespace {namespace}", f"def layout : List Slot := [{', '.join(specs)}]"]
    model = {}
    for decl, identifier, found in checked:
        count = len(decl.params)
        names = ["state" if p == record else p.lower() for p in decl.params]
        calls = dict(available)
        binders = f" ({' '.join(names)} : Object)" if count else ""
        if decl.recursive:
            calls[identifier] = (count, "recur")
            binders = " (recur : Object → Object)" + binders
        rendered = term(found[5], dict(zip(map(symbol, found[2] if count else []), names)), calls)
        if decl.lean.endswith("Length"):
            binders = " (_state : Object)"
        if decl.lean.endswith("Resize"):
            binders = " (_i state : Object)"
        text.append(f"-- ACL2::{decl.name}\ndef {decl.lean}{binders} : Object :=\n{indent(rendered, '  ')}")
        available[identifier] = (count, decl.call_binding or decl.lean)
        if decl.model:
            model[identifier] = (count, decl.model)

    samples = []
    for theorem, formula in examples:
        label = acl2_name(theorem)
        op, lhs, rhs = formula
        require(symbol(op) == EQUAL and isinstance(rhs, list) and len(rhs) == 2
                and symbol(rhs[0]) == QUOTE, f"expected a ground observation equality for {label}")
        samples.append(f"  ({term(lhs, {}, model)}, {term(rhs, {}, {})})")
    text.append("def observations : List (Object × Object) := [\n" + ",\n".join(samples) + "]")
    text.append(f"end {namespace}")
    return "\n\n".join(text)


def generate(document, toy):
    toy_rows = [row for row in toy["definitions"] if symbol(row[0]) not in SUPPORT_DEFINITIONS]
    fixtures = [
        render_fixture("SilToy", document["toy_event"], toy_rows + document["toy_auxiliary"],
                       toy["observations"]),
        render_fixture("SilShelves", document["event"], document["definitions"], document["observations"]),
    ]
    return """-- Generated by tests/logic/acl2/check_defstobj_schema.py.
module

public import Silmaril.Logic.ACL2.Standard.FixedLayout.Schema.Defs
public import Silmaril.Logic.ACL2.Standard.FixedLayout.Source

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.FixedLayout.Schema.Fixtures

""" + "\n\n".join(fixtures) + "\n\nend Silmaril.Logic.ACL2.Standard.FixedLayout.Schema.Fixtures\n"


def checked_source(data):
    require(sha256(data).hexdigest() == PIN, "schema export differs from its pin")
    document = json.loads(data)
    toy_data = TOY.read_bytes()
    checked_toy(toy_data)
    require(document["toy_fixture_sha256"] == sha256(toy_data).hexdigest(),
            "SIL-TOY fixture differs from the reference in the schema export")
    require(document["source_sha256"] == sha256(INPUT.read_bytes()).hexdigest(),
            "SIL-SHELVES input differs from its exported digest")
    return generate(document, json.loads(toy_data))


def compare(path=FIXTURE):
    require(LEAN.read_text(encoding="utf-8") == checked_source(path.read_bytes()),
            "Lean DEFSTOBJ schema fixtures differ from the pinned translation")
    print("Lean DEFSTOBJ schema fixtures match both pinned ACL2 events")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path, default=FIXTURE)
    parser.add_argument("--emit", type=Path)
    args = parser.parse_args()
    try:
        if args.emit:
            args.emit.write_text(checked_source(args.input.read_bytes()), encoding="utf-8")
        else:
            compare(args.input)
    except (IndexError, KeyError, TypeError, ValueError) as error:
        parser.exit(1, f"{error}\n")
