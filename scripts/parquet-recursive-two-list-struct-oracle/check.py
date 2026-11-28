"""Inspect original V1 leaves and reconstruct two shared Parquet LIST wrappers."""

from importlib.metadata import version
from itertools import product
import json
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
NATIVE = runpy.run_path(str(HERE.parent / "parquet-recursive-list-path-v1-oracle/check.py"))
PREVIOUS = runpy.run_path(str(HERE.parent / "parquet-recursive-list-struct-oracle/check.py"))
TWO, V2, FRAMES, LEVEL = (NATIVE[key] for key in ("TWO", "V2", "FRAMES", "LEVEL"))
THRIFT, path_term, lst, fingerprints = (
    PREVIOUS[key] for key in ("THRIFT", "path_term", "lst", "fingerprints")
)
expected_observation = PREVIOUS["ROWS"]["expected_observation"]
write, frame, raw_chunks, repack = (TWO[key] for key in ("write", "frame", "raw_chunks", "repack"))
triple, page_term, metadata = (NATIVE[key] for key in ("triple", "page_term", "metadata"))
PATH = ("items", "list", "element", "list", "element")
NAMES = ("lo", "hi")
WIDTHS = (32, 64)


LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open RecursiveSchema.TwoListStruct
open Arrow.RecursiveSchema.Batch.Rows (Observation)

set_option maxRecDepth 8192

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"unexpected refusal: {repr cause}")

private def refuse {ε α : Type} [DecidableEq ε] [Repr ε] (wanted : ε) (result : Except ε α) :
    IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"expected a refusal with {repr wanted}")
  | .error actual =>
    unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")

private structure ExpectedPage where
  frame : Page.Frame
  sections : RecursiveSchema.ListPath.Chunk.Sections
  start : RecursiveSchema.ListPath.Chunk.State
  stop : RecursiveSchema.ListPath.Chunk.State
  atoms : List RecursiveSchema.ListPath.Rows.Atom

private def checkColumn (file : Bytes) (group : Nat) (side : Side) (path : List String)
    (ceiling : Nat) (span : Footer.Span) (pages : List ExpectedPage) : IO Unit := do
  let source ← take (openFile {} file)
  let bound ← take (Reader.bindGroup source.snapshot group)
  let binding ← take (Reader.bindColumn source.schema bound side)
  let seen ← take (Reader.readColumn {} binding)
  let carrier := Reader.carrierOf binding
  unless carrier.address.path = path ∧ binding.span = span ∧
      source.schema.plan.sharedDefinition = ceiling ∧ carrier.plan.shape.repetitions = 2 ∧
      seen.pages.length = pages.length do
    throw (IO.userError "original schema, span or page count differs")
  for (actual, expected) in seen.pages.zip pages do
    unless actual.frame = expected.frame ∧ actual.start = expected.start ∧
        actual.decoded.sections = expected.sections ∧ actual.decoded.after = expected.stop ∧
        actual.decoded.atoms = expected.atoms do
      throw (IO.userError "original frame, level span, cursor or child trace differs")

private def checkRows (file : Bytes) (expected : List Observation) : IO Unit := do
  let source ← take (openFile {} file)
  let rows ← take (Reader.readAll {} source.schema)
  unless rows == expected do throw (IO.userError s!"original ordered row groups differ: {repr rows}")

private def inconsistent (file : Bytes) (group : Nat) (wanted : Reader.Error) : IO Unit := do
  let source ← take (openFile {} file)
  let bound ← take (Reader.bindGroup source.snapshot group)
  for side in [Side.left, .right] do
    let binding ← take (Reader.bindColumn source.schema bound side)
    let observed ← take (Reader.readColumn {} binding)
    let _ ← take (RecursiveSchema.ListPath.Rows.reconstruct {} (source.schema.plan.path side)
      bound.original.numRows.toNat observed.atoms)
  refuse wanted (Reader.readGroup {} source.schema group)
  refuse wanted (Reader.readAll {} source.schema)

private def groupRefusal (file : Bytes) (group : Nat) (limits : Reader.Limits) (wanted : Reader.Error) : IO Unit := do
  let source ← take (openFile {} file)
  refuse wanted (Reader.readGroup limits source.schema group)
"""


def native(nullable, struct_nullable=False, **options):
    outer, inner, lhs, rhs = nullable
    element = pa.struct([pa.field("lo", pa.int32(), lhs), pa.field("hi", pa.int64(), rhs)])
    node = pa.list_(pa.field("element", element, nullable=struct_nullable))
    schema = pa.schema([pa.field("items", pa.list_(pa.field("element", node, inner)), outer)])

    def pair(lo, hi):
        return {"lo": lo, "hi": hi}

    leaves = [pair(None if lhs else -7, None if rhs else 2**40),
              pair(-2**31, None if rhs else -2**63),
              pair(None if lhs else 9, -2**63), pair(2**31-1, 2**63-1)]
    if struct_nullable:
        leaves = [None, *leaves]
    first_inner = leaves + [pair(i, -2**40-i) for i in range(9)]
    markers = [[], None] if inner else [[]]
    groups = [
        ([None] if outer else []) + [[], [leaves, *markers]],
        [[first_inner, *markers], [[], first_inner[:2]], [leaves]],
    ]
    wire = write(schema, groups, **({"max_rows_per_page": 1, "write_batch_size": 1} | options))
    return schema, groups, wire


def steps(nullable):
    outer, inner = nullable[:2]
    outer_empty = int(outer)
    inner_empty = outer_empty + 1 + int(inner)
    return outer_empty, inner_empty, inner_empty + 1


def trace(rows, nullable, side):
    outer, inner = nullable[:2]
    outer_empty, inner_empty, shared = steps(nullable)
    def entries(row):
        if row is None:
            assert outer
            yield 0, 0, None
        elif not row:
            yield 0, outer_empty, None
        else:
            for index, inner_list in enumerate(row):
                rep = int(index > 0)
                if inner_list is None:
                    assert inner
                    yield rep, outer_empty + 1, None
                elif not inner_list:
                    yield rep, inner_empty, None
                else:
                    for element, record in enumerate(inner_list):
                        word = record[NAMES[side]]
                        level = shared + (int(nullable[2 + side]) if word is not None else 0)
                        yield (2 if element else rep), level, word
    return [slot for row in rows for slot in entries(row)]


def inspect(wire, schema, groups):
    expected_rows = [[{"items": row} for row in group] for group in groups]
    table = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert table.schema_arrow.equals(schema, check_metadata=True)
    assert [table.read_row_group(group).to_pylist() for group in range(table.num_row_groups)] == expected_rows
    outer = schema.field(0)
    inner = outer.type.value_field
    element = inner.type.value_field
    nullable = outer.nullable, inner.nullable, *(child.nullable for child in element.type)
    first_empty, second_empty, shared = steps(nullable)
    entries = THRIFT["list_field"](metadata(wire), 2)
    assert len(entries) == 8 and entries[0][5][1] == 1
    for index, optional in ((1, nullable[0]), (3, nullable[1])):
        node, wrapper = entries[index:index+2]
        assert node[3][1] == optional and node[5][1] == 1 and node[6][1] == 3
        assert node[10][1] == {3: (TType.STRUCT, {})}
        assert wrapper[3][1] == 2 and wrapper[4][1] == b"list" and wrapper[5][1] == 1
        assert not (set(wrapper) & {1, 2, 6, 10})
    assert entries[5][3][1] == 0 and entries[5][5][1] == 2 and not (set(entries[5]) & {1, 2, 6, 10})
    for side, entry in enumerate(entries[6:]):
        assert entry[1][1] == side + 1 and entry[3][1] == nullable[2 + side]
        assert entry[4][1] == NAMES[side].encode() and not (set(entry) & {2, 6, 10})
        column = table.schema.column(side)
        assert column.path == ".".join(PATH + (NAMES[side],))
        assert column.max_repetition_level == 2 and column.max_definition_level == shared + nullable[2 + side]

    output = {}
    for (group, side), footer, lo, hi in V2["columns"](wire):
        assert set(THRIFT["list_field"](footer, 2)) == {0, 3}
        assert footer[4][1] == 0 and 11 not in footer and footer[9][1] == lo
        assert footer[6][1] == footer[7][1] == hi - lo
        assert [piece.decode() for piece in THRIFT["list_field"](footer, 3)] == list(PATH + (NAMES[side],))
        maximum = shared + nullable[2 + side]
        expected = trace(groups[group], nullable, side)
        slots, rows, live = 0, 0, 0
        pages = []
        for at, header, body_at, body in FRAMES(wire, lo, hi):
            assert header[1][1] == 0 and header[2][1] == header[3][1] == len(body)
            crc = header[4][1] & 0xffffffff
            assert crc == zlib.crc32(body)
            count, *encodings = [header[5][1][key][1] for key in range(1, 5)]
            assert encodings == [0, 3, 3]
            reps, rest = LEVEL(body, 2, count)
            defs, suffix = LEVEL(rest, maximum, count)
            physical = "<i" if WIDTHS[side] == 32 else "<q"
            assert len(suffix) == defs.count(maximum) * (WIDTHS[side] // 8)
            words = iter(word for word, in struct.iter_unpack(physical, suffix))
            page_trace = [(rep, definition, next(words) if definition == maximum else None)
                          for rep, definition in zip(reps, defs, strict=True)]
            assert page_trace == expected[slots:slots + count]
            before = slots, rows, live
            for rep, definition, _ in page_trace:
                reached = int(first_empty < definition) + int(second_empty < definition)
                assert rep <= min(live, reached)
                live = reached
                rows += rep == 0
            slots += count
            sections = body_at, body_at + len(body) - len(rest), body_at + len(body) - len(suffix), body_at + len(body)
            pages.append((at, body_at, crc, len(body), sections, before, (slots, rows, live), page_trace))
        assert slots == footer[5][1] == len(expected) and rows == len(groups[group])
        assert pages[-1][1] + pages[-1][3] == hi
        output[group, side] = (lo, hi), pages
    assert len(output) == 2 * len(groups)
    for group, rows in enumerate(groups):
        def topology(side):
            return [(rep, min(definition, shared)) for rep, definition, _ in trace(rows, nullable, side)]
        assert topology(0) == topology(1)
    return shared, output


def frames_in(wire, group, side):
    return next(list(FRAMES(wire, lo, hi)) for key, _, lo, hi in V2["columns"](wire) if key == (group, side))


def address(group, side):
    return f"⟨{group}, {side}, {path_term(PATH + (NAMES[side],))}⟩"


def point(wire, group, side, slot):
    remaining = slot
    for page, (at, header, _, _) in enumerate(frames_in(wire, group, side)):
        count = header[5][1][1][1]
        if remaining < count:
            return f"⟨{address(group, side)}, {page}, {at}, {slot}⟩"
        remaining -= count
    raise AssertionError("missing expected counterpart")


def fixtures():
    genuine = {"native_" + "".join(str(int(flag)) for flag in flags): native(flags)
               for flags in product((False, True), repeat=4)}
    schema, groups, wire = genuine["native_1111"]
    inspect(wire, schema, groups)
    carrier = raw_chunks(wire)
    all_flags = (True,) * 4
    pure_rows = {key: trace(groups[key[0]], all_flags, key[1]) for key in carrier}
    authored, controls = {}, []

    def replace(chunks, key, atoms, cuts):
        template = carrier[key][0]
        frames = [frame(template, atoms[lo:hi], WIDTHS[key[1]])
                  for lo, hi in zip([0, *cuts], [*cuts, len(atoms)], strict=True)]
        return chunks | {key: frames}

    next_inner = len(groups[1][0][0])
    for side, cuts in ((0, [2, next_inner]), (1, [4, next_inner + 1])):
        atoms = pure_rows[1, side]
        assert [atoms[cut][0] for cut in cuts] == [2, 1]
        carrier = replace(carrier, (1, side), atoms, cuts)
    authored["independent_cuts"] = repack(wire, carrier)
    _, checked = inspect(authored["independent_cuts"], schema, groups)
    assert [[page[-1][0][0] for page in checked[1, side][1]] for side in (0, 1)] == [[0, 2, 1], [0, 2, 1]]

    def patch(label, group, atoms, cuts=()):
        footer = metadata(wire)
        THRIFT["column_metadata"](footer, group, 1)[5] = TType.I64, len(atoms)
        authored[label] = repack(wire, replace(carrier, (group, 1), atoms, cuts), footer)

    def mismatched(label, group, atoms, slot):
        patch(label, group, atoms)
        before = pure_rows[group, 0][slot]
        after = atoms[slot]
        def common(atom):
            return f"({atom[0]}, {min(atom[1], steps(all_flags)[2])})"
        edited = authored[label]
        cause = (f".topology (.conflict {slot} {point(edited, group, 0, slot)} {point(edited, group, 1, slot)} "
                 f"{common(before)} {common(after)})")
        controls.append((label, group, cause, True))

    first = pure_rows[0, 1]
    assert first[0] == (0, 0, None)
    mismatched("outer_null_empty", 0, [(0, 1, None), *first[1:]], 0)
    second = pure_rows[1, 1]
    null = next_inner + 1
    assert second[null] == (1, 2, None)
    changed = [*second[:null], (1, 3, None), *second[null+1:]]
    mismatched("inner_null_empty", 1, changed, null)
    earliest = 4
    assert second[earliest][0] == 2
    changed[earliest] = (1, *second[earliest][1:])
    mismatched("earlier_repetition_conflict", 1, changed, earliest)
    final = len(second) - 1
    assert second[final][0] == 2
    patch("short_sibling", 1, second[:-1])
    controls.append(("short_sibling", 1,
                     f".topology (.missing {final} {address(1, 1)} {point(authored['short_sibling'], 1, 0, final)})", True))

    before = second[:null]
    assert before[-1] == (1, 3, None)
    patch("closed_inner_continuation", 1, [*before, (2, *second[null][1:]), *second[null+1:]], [null])
    edited = authored["closed_inner_continuation"]
    page_at = frames_in(edited, 1, 1)[1][0]
    controls.append(("closed_inner_continuation", 1,
                     f".chunk (.page {address(1, 1)} 1 {page_at} ⟨{null}, 1, 1⟩ "
                     f"(.level (.closedAncestor {null} 2 1)))", False))

    original = {label: case[2] for label, case in genuine.items()}
    for label, settings in (
        ("optional_struct", {"struct_nullable": True}),
        ("snappy", {"compression": "SNAPPY"}),
        ("v2", {"data_page_version": "2.0"}),
    ):
        original[label] = native(all_flags, **settings)[2]
    positive = genuine | {"independent_cuts": (schema, groups, authored["independent_cuts"])}
    return original, authored, positive, controls


def verify(folder):
    genuine, authored, positives, controls = fixtures()
    files = genuine | authored
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)
    code = [LEAN, "public def main (args : List String) : IO Unit := do",
            '  let [folder] := args | throw (IO.userError "expected fixture directory")']
    total = 0
    for label, (schema, groups, wire) in positives.items():
        ceiling, chunks = inspect(wire, schema, groups)
        for (group, side), ((lo, hi), pages) in chunks.items():
            terms = lst(page_term(page, WIDTHS[side]) for page in pages)
            tag = ".left" if side == 0 else ".right"
            code.append(f'  checkColumn (← load folder "{label}") {group} {tag} {path_term(PATH + (NAMES[side],))} '
                        f'{ceiling} ⟨{lo}, {hi}⟩ {terms}')
            total += len(pages)
        rows = lst(expected_observation(schema, [{"items": row} for row in group]) for group in groups)
        code.append(f'  checkRows (← load folder "{label}") {rows}')
    for label, group, wanted, topology in controls:
        if topology:
            code.append(f'  inconsistent (← load folder "{label}") {group} ({wanted})')
        else:
            code.append(f'  groupRefusal (← load folder "{label}") {group} {{}} ({wanted})')

    v2 = genuine["v2"]
    (key, _, lo, hi), = [item for item in V2["columns"](v2) if item[0] == (0, 0)]
    at, header, _, _ = frames_in(v2, *key)[0]
    info = header[8][1]
    fields = ", ".join(str(info[k][1]) for k in range(1, 7))
    flag = str(info.get(7, (TType.BOOL, True))[1]).lower()
    span, _ = inspect(genuine["native_1111"], *positives["native_1111"][:2])[1][0, 0]
    limit_span = triple(span)
    code.extend([
        '  refuse .structShape (openFile {} (← load folder "optional_struct"))',
        '  let source ← take (openFile {} (← load folder "native_1111"))',
        '  refuse (.depth 6) (compile { maxSchemaDepth := 6 } source.snapshot)',
        f'  groupRefusal (← load folder "snappy") 0 {{}} (.binding (.column {address(0, 0)} (.codec 1)))',
        f'  groupRefusal (← load folder "v2") 0 {{}} (.chunk (.chunk {address(0, 0)} ⟨{lo}, {hi}⟩ '
        f'(.pageVersion 0 {at} (.dataV2 ⟨{fields}, {flag}⟩))))',
        f'  groupRefusal (← load folder "native_1111") 0 {{ maxSlots := 0 }} '
        f'(.chunk (.chunk {address(0, 0)} {limit_span} .slotLimit))',
        f'  groupRefusal (← load folder "native_1111") 0 {{ maxRows := 0 }} '
        f'(.chunk (.chunk {address(0, 0)} {limit_span} .rowLimit))',
    ])
    driver = folder / "TwoListStruct.lean"
    driver.write_text("\n".join(code) + "\n", encoding="utf-8")
    subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                    "--run", str(driver), str(folder)], cwd=ROOT, check=True)
    print(f"Checked {len(positives)} native inputs, {total} original V1 pages and {len(controls) + 6} typed refusals")
    return {"genuine_parquet": fingerprints(genuine), "authored_parquet": fingerprints(authored)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for category, fixtures in captured.items():
        assert fixtures == pins[category], f"{category} fixture pins changed"


if __name__ == "__main__":
    main()
