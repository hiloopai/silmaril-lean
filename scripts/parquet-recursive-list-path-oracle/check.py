"""Check native PyArrow schemas and independently extracted traces against the LIST-path core."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import struct
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROWS = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-rows-oracle/check.py"))
TWO = ROWS["TWO"]
V1, V2, FRAMES, lst, write, fingerprints = (TWO[k] for k in ("V1", "V2", "FRAMES", "lst", "write", "fingerprints"))
LEVEL = TWO["CHUNK"]["level_section"]

LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Defs

open Silmaril.Formats (Bytes)
open Silmaril.Formats.Arrow.RecursiveSchema (Schema)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation)
open Silmaril.Formats.Parquet
open RecursiveSchema.ListPath
open RecursiveSchema.ListPath.Rows

private def take {ε α : Type} [Repr ε] (input : Except ε α) : IO α :=
  match input with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def deny {ε α : Type} [DecidableEq ε] [Repr ε] (wanted : ε) (input : Except ε α) : IO Unit :=
  match input with
  | .ok _ => throw (IO.userError s!"unexpected acceptance, expected {reprStr wanted}")
  | .error error =>
    unless error = wanted do throw (IO.userError s!"expected {reprStr wanted}, got {reprStr error}")

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def checkFile (input : Bytes) (depth : Nat) (schema : Schema)
    (steps : List RecursiveSchema.Repeated.Step)
    (groups : List (Observation × List Atom)) : IO Unit := do
  let source ← take (openFile { maxSchemaDepth := 2 * depth + 2 } input)
  let plan := source.schema.plan
  let leaf := plan.shape.leaf.1
  unless leaf.location.ordinal = 2 * depth + 1 ∧
      leaf.location.path = "chain" :: (List.replicate depth ["list", "element"]).flatten do
    throw (IO.userError "original leaf ordinal or path differs")
  unless plan.arrow == schema ∧ plan.shape.repetitions = depth ∧
      plan.shape.definitions = steps.length ∧ plan.shape.steps {} = steps ∧
      source.snapshot.groupCount = groups.length do
    throw (IO.userError "original schema, definition steps or group count differs")
  for (batches, atoms) in groups do
    let accepted ← take (reconstruct {} plan batches.rowCount atoms)
    unless accepted == batches do throw (IO.userError "reconstructed Arrow rows differ")
    let projected ← take (project {} plan batches.rows)
    unless projected = atoms do throw (IO.userError "projected trace differs from original wire")
  let expected := groups.map Prod.fst
  if depth = 1 then
    let original ← take (RecursiveSchema.Repeated.openFile {} input)
    let actual ← take (RecursiveSchema.Repeated.Rows.readAll {} original.schema)
    unless actual == expected ∧ original.schema.arrow == schema do
      throw (IO.userError "one-LIST predecessor differs")
  if depth = 2 then
    let original ← take (RecursiveSchema.TwoList.openFile {} input)
    let actual ← take (RecursiveSchema.TwoList.Rows.readAll {} original.schema)
    unless actual == expected ∧ RecursiveSchema.TwoList.Rows.arrowSchema original.schema.plan == schema do
      throw (IO.userError "two-LIST predecessor differs")
    for ((_, atoms), ordinal) in groups.zipIdx do
      let binding ← take (RecursiveSchema.TwoList.Chunk.bind original.schema ordinal)
      let observed ← take (RecursiveSchema.TwoList.Chunk.read {} binding)
      let previous := (RecursiveSchema.TwoList.Rows.atoms observed.pages).map fun atom =>
        ({ repetition := atom.repetition, definition := atom.definition, word := atom.word } : Atom)
      unless previous = atoms do throw (IO.userError "two-LIST predecessor trace differs")

private def refuseRows (input : Bytes) : IO Unit := do
  let original ← take (openFile {} input)
  let plan := original.schema.plan
  let maximum := plan.shape.definitions
  let depth := plan.shape.repetitions
  let word : Atom := ⟨0, maximum, some (.int32 42)⟩
  let empty : Observation := ⟨0, []⟩
  let noRows ← take (reconstruct {} plan 0 [])
  unless noRows == empty do throw (IO.userError "empty observation differs")
  deny (.traceMismatch) (reconstruct {} plan 1 [{ word with repetition := 1 }])
  deny (.shape 0) (reconstruct {} plan 1 [word, { word with repetition := depth + 1 }])
  deny (.shape 0) (reconstruct {} plan 1
    [⟨0, maximum - 2, none⟩, { word with repetition := depth }])
  deny (.shape 0) (reconstruct {} plan 1 [{ word with word := none }])
  deny (.shape 0) (reconstruct {} plan 1 [{ word with word := some (.int64 42) }])
  deny (.shape 0) (reconstruct {} plan 1 [{ word with definition := maximum + 1 }])
  deny (.rowCount 2 1) (reconstruct {} plan 2 [word])
  deny (.slotLimit 1) (reconstruct { maxSlots := 0 } plan 1 [word])
  deny (.rowLimit 1) (reconstruct { maxRows := 0 } plan 1 [word])
  deny (.slotLimit 1) (project { maxSlots := 0 } plan [[none]])
  deny (.rowLimit 1) (project { maxRows := 0 } plan [[none]])
  deny .projection (project {} plan [[some (.int32 4)]])
  deny .projection (project {} plan [[]])

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
"""


def schema_for(nullable, width):
    leaf = pa.field("element", pa.int32() if width == 32 else pa.int64(), nullable[-1])
    for i in reversed(range(len(nullable) - 1)):
        leaf = pa.field("element" if i else "chain", pa.list_(leaf), nullable[i])
    return pa.schema([leaf])


def samples(nullable, width):
    edge = 1 << (width - 1)
    row = [-edge] + ([None] if nullable[-1] else []) + [0, edge - 1]
    for optional in reversed(nullable[:-1]):
        row = ([None] if optional else []) + [[], row]
    again = row[-1]
    return [row, [again, [], [again[0], again[-1]]]]


def levels(rows, nullable):
    def walk(value, at, rep, defined):
        if value is None:
            assert nullable[at]
            yield rep, defined, None
        elif at == len(nullable) - 1:
            yield rep, defined + nullable[at], value
        elif not value:
            yield rep, defined + nullable[at], None
        else:
            for index, child in enumerate(value):
                yield from walk(child, at + 1, at + 1 if index else rep, defined + nullable[at] + 1)

    return [slot for row in rows for slot in walk(row, 0, 0, 0)]


def inspect(wire, schema, nullable, width, groups):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.equals(schema, check_metadata=True)
    assert parquet.num_row_groups == len(groups)
    depth = len(nullable) - 1
    maximum = depth + sum(nullable)
    path = ["chain"] + ["list", "element"] * depth
    physical = 1 if width == 32 else 2
    metadata = TWO["MIXED"]["metadata"](wire)
    entries = TWO["THRIFT"]["list_field"](metadata, 2)
    assert len(entries) == 2 * depth + 2 and entries[0][5][1] == 1
    steps = []
    for index in range(depth):
        at = 2 * index + 1
        outer, wrapper = entries[at:at + 2]
        assert outer[4][1].decode() == path[at - 1] and outer[3][1] == nullable[index]
        assert outer[5][1] == 1 and outer[6][1] == 3 and list(outer[10][1]) == [3]
        assert wrapper[4][1] == b"list" and wrapper[3][1] == 2 and wrapper[5][1] == 1
        outer_at = f"⟨{at}, {json.dumps(path[:at])}⟩"
        wrapper_at = f"⟨{at + 1}, {json.dumps(path[:at + 1])}⟩"
        if nullable[index]:
            steps.append(f".optional {outer_at} .list")
        steps.append(f".emptyList {outer_at} {wrapper_at}")
    leaf = entries[-1]
    assert set(leaf) == {1, 3, 4} and leaf[1][1] == physical
    assert leaf[3][1] == nullable[-1] and leaf[4][1] == b"element"
    if nullable[-1]:
        steps.append(f".optional ⟨{2 * depth + 1}, {json.dumps(path)}⟩ .element")

    traces, pages = [], 0
    for (group, column), original, lo, hi in V2["columns"](wire):
        assert column == 0 and original[1][1] == physical and original[4][1] == 0
        assert original[9][1] == lo and original[6][1] == original[7][1] == hi - lo
        assert [item.decode() for item in original[3][1][1]] == path
        assert parquet.read_row_group(group).column(0).to_pylist() == groups[group]
        trace = []
        for start, header, payload, body in FRAMES(wire, lo, hi):
            assert start < payload and header[1][1] == 0
            assert header[2][1] == header[3][1] == len(body) and header[4][1] & 0xffffffff == zlib.crc32(body)
            count, encoding, def_encoding, rep_encoding = [header[5][1][field][1] for field in (1, 2, 3, 4)]
            assert (encoding, def_encoding, rep_encoding) == (0, 3, 3)
            reps, rest = LEVEL(body, depth, count)
            defs, suffix = LEVEL(rest, maximum, count)
            assert len(suffix) == (width // 8) * defs.count(maximum)
            words = iter(word for word, in struct.iter_unpack("<i" if width == 32 else "<q", suffix))
            trace.extend((rep, definition, next(words) if definition == maximum else None)
                         for rep, definition in zip(reps, defs, strict=True))
            pages += 1
        assert len(trace) == original[5][1] and trace == levels(groups[group], nullable)
        traces.append(trace)
    assert len(traces) == len(groups)
    assert set(rep for trace in traces for rep, _, _ in trace) == set(range(depth + 1))
    assert set(definition for trace in traces for _, definition, _ in trace) == set(range(maximum + 1))
    return steps, traces, pages


def atom_term(slot, width):
    rep, definition, word = slot
    value = "none" if word is None else f"some (.int{width} ({word}))"
    return f"⟨{rep}, {definition}, {value}⟩"


def cases():
    for width in (32, 64):
        for depth in (1, 2, 3):
            choices = range(1 << (depth + 1)) if depth == 3 else (0, (1 << (depth + 1)) - 1)
            for bits in choices:
                yield width, tuple(bool(bits & (1 << i)) for i in range(depth + 1))
    yield 32, (False, True, False, True, False)
    yield 64, (True, False, True, False, True, False, True)
    yield 64, tuple(i % 2 == 0 for i in range(16))
    yield 32, (True,) * 17


def verify(folder):
    code = [LEAN, *V1["ENTRY"]]
    genuine, controls, page_count = {}, {}, 0
    for width, nullable in cases():
        depth = len(nullable) - 1
        bits = sum(1 << i for i, optional in enumerate(nullable) if optional)
        label = f"signed_{width}_depth_{depth}_{bits}"
        schema, groups = schema_for(nullable, width), samples(nullable, width)
        genuine[label] = write(schema, groups, max_rows_per_page=1)
        steps, traces, pages = inspect(genuine[label], schema, nullable, width, groups)
        page_count += pages
        declaration = ROWS["field_term"](schema.field(0))
        batches = lst(f"({ROWS['batch_term'](group, width)}, {lst(atom_term(slot, width) for slot in trace)})"
                      for group, trace in zip(groups, traces, strict=True))
        code.append(f'  checkFile (← load folder "{label}") {depth} ⟨[{declaration}]⟩ {lst(steps)} {batches}')
    controls["scalar"] = write(pa.schema([pa.field("chain", pa.int32(), False)]), [[1]])
    # A genuine schema-only file with multiple leaves.
    controls["multi_leaf"] = write(pa.schema([pa.field("a", pa.int32()), pa.field("b", pa.int64())]), [])
    controls["struct_wrapped"] = write(pa.schema([pa.field("root", pa.struct([schema_for((True,) * 4, 32).field(0)]))]), [])
    for label, wire in (genuine | controls).items():
        (folder / f"{label}.parquet").write_bytes(wire)
    code.extend([
        '  deny (.original (.shape 1)) (openFile {} (← load folder "scalar"))',
        '  deny (.original (.shape 0)) (openFile {} (← load folder "multi_leaf"))',
        '  deny (.original (.shape 1)) (openFile {} (← load folder "struct_wrapped"))',
        '  deny (.original (.snapshot (.invalidMetadata .schemaDepth))) '
        '(openFile {} (← load folder "signed_32_depth_16_131071"))',
        '  deny (.original (.snapshot (.invalidMetadata .schemaDepth))) '
        '(openFile { maxSchemaDepth := 7 } (← load folder "signed_32_depth_3_15"))',
        '  refuseRows (← load folder "signed_32_depth_3_15")',
    ])
    V2["run_lean"](folder, "ListPath.lean", code)
    print(f"Checked {len(genuine)} genuine schemas, {page_count} independently decoded pages, "
          f"{2 * len(genuine)} logical round trips and 18 typed refusals")
    return {"genuine_parquet": fingerprints(genuine), "genuine_controls": fingerprints(controls)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for kind, expected in captured.items():
        assert expected == pins[kind], f"{kind} fixture pins changed"


if __name__ == "__main__":
    main()
