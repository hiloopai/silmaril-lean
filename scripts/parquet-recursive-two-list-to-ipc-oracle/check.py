"""Read complete Lean-emitted two-LIST IPC streams with pinned PyArrow."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
EVENTS = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-events-oracle/check.py"))
STREAM = runpy.run_path(str(HERE.parent / "arrow-recursive-stream-oracle/check.py"))
V1, V2, FRAMES, PATH, fingerprints, observation = (
    EVENTS[key] for key in ("V1", "V2", "FRAMES", "PATH", "fingerprints", "observation")
)

LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Defs

open Silmaril.Formats
open Silmaril.Formats.Arrow.RecursiveSchema (Field)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events (Value declarations eraseBatch)
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events (Selection)

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError (reprStr cause))

private def deny {ε α : Type} [DecidableEq ε] [Repr ε] (expected : ε) (result : Except ε α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"accepted input expected to fail with {repr expected}")
  | .error actual =>
    unless actual = expected do throw (IO.userError s!"expected {repr expected}, got {repr actual}")

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def checkTrace {ε : Type} [Repr ε] [DecidableEq ε]
    (result : Arrow.Events.EventStream (Option String) Value ε)
    (fields : List (Option String × Field)) (batches : List Observation)
    (terminal : Arrow.Events.Termination ε) : IO Unit := do
  let ⟨source, trace⟩ ← take result
  unless declarations source == fields ∧ trace.batches.map eraseBatch == batches do
    throw (IO.userError "schema, batch count or logical rows differ")
  unless trace.termination = terminal do throw (IO.userError "terminal outcome differs")

private def selectedFields (selection : Selection) (fields : List (Option String × Field)) :
    List (Option String × Field) :=
  match selection with
  | .field => fields
  | .empty => []

private def checkFile (folder : System.FilePath) (label : String) (input : Bytes)
    (fields : List (Option String × Field)) (batches : List Observation) : IO Unit := do
  for (selection, suffix) in [(Selection.field, "field"), (.empty, "empty")] do
    let expected := batches.map (selectBatch selection)
    let projected := selectedFields selection fields
    let wire ← take (convert {} {} {} input selection)
    checkTrace (Parquet.RecursiveSchema.TwoList.Rows.Events.readProjected {} {} input selection)
      projected expected .eos
    checkTrace (Arrow.RecursiveSchema.Stream.Events.read {} wire) projected expected .eos
    let strict ← take (Arrow.RecursiveSchema.Stream.read {} wire)
    let .eos ordinal offset := strict.terminal | throw (IO.userError "expected exact IPC EOS")
    unless ordinal = batches.length ∧ offset + 8 = wire.len do
      throw (IO.userError "EOS or batch extent differs")
    deny (.failed ordinal offset .trailingBytes)
      (Arrow.RecursiveSchema.Stream.read {} (wire ++ Arrow.StreamWriter.eos))
    let truncated := wire.slice 0 (wire.len - 1)
    let .error (.failed index pos (.envelope _)) := Arrow.RecursiveSchema.Stream.read {} truncated |
      throw (IO.userError "strict read accepted incomplete EOS")
    unless index = ordinal ∧ pos = offset do throw (IO.userError "incomplete EOS lost its address")
    IO.FS.writeBinFile (folder / (label ++ "_" ++ suffix ++ ".arrow")) wire.toByteArray

private def noOutputBudget : Arrow.RecursiveSchema.Batch.Limits :=
  { schema.ipc := { fields := 0, batches := 0 }, slots := 0 }

private def sourceFailure (input : Bytes) (fields : List (Option String × Field))
    (batches : List Observation) (original : Parquet.RecursiveSchema.TwoList.Rows.Events.Error) : IO Unit := do
  for selection in [Selection.field, .empty] do
    checkTrace (Parquet.RecursiveSchema.TwoList.Rows.Events.readProjected {} {} input selection)
      (selectedFields selection fields) (batches.map (selectBatch selection)) (.readError original)
    deny (.source original) (convert {} {} {} input selection)
    deny (.source original) (convert {} {} noOutputBudget input selection)

private def openFailure (input : Bytes) : IO Unit := do
  let .error original := Parquet.RecursiveSchema.TwoList.openFile {} input |
    throw (IO.userError "expected original open failure")
  for selection in [Selection.field, .empty] do
    deny (.source (.openError original)) (convert {} {} noOutputBudget input selection)

private def writerFailure (input : Bytes) : IO Unit := do
  for selection in [Selection.field, .empty] do
    deny (.writer (.batchLimit 3 0)) (convert {} {} noOutputBudget input selection)

set_option maxRecDepth 8192
"""


def verify(scratch):
    genuine, labeled, positives = EVENTS["fixtures"]()
    predecessor = json.loads((Path(EVENTS["HERE"]) / "fixtures.json").read_text(encoding="utf-8"))
    source_pins = {"genuine": fingerprints(genuine), "labeled": fingerprints(labeled)}
    assert all(pins == predecessor[kind] for kind, pins in source_pins.items())
    files = genuine | labeled
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)
    code = [LEAN, *V1["ENTRY"]]
    for label, width in positives.items():
        fields, batches = observation(files[label], width)
        code.append(f'  checkFile folder "{label}" (← load folder "{label}") {fields} {batches}')

    def original_frame(label, position, ordinal):
        lo, hi = next((start, stop) for key, _, start, stop in V2["columns"](files[label]) if key == position)
        return list(FRAMES(files[label], lo, hi))[ordinal]

    at, *_ = original_frame("first_of_two_errors", (1, 0), 3)
    path = json.dumps(PATH)
    stale = (f".group 1 (.chunk (.page ⟨1, 0, {path}⟩ 3 {at} ⟨3, 2, .outer⟩ "
             "(.level (.closedAncestor 3 2 .outer))))")
    at, header, _, body = original_frame("late_crc", (2, 0), 0)
    stored, computed = header[4][1] & 0xffffffff, zlib.crc32(body)
    checksum = f".group 2 (.chunk (.page ⟨2, 0, {path}⟩ 0 {at} {{}} (.checksum (.mismatch {stored} {computed}))))"
    for label, kept, error in (("first_of_two_errors", 1, stale), ("late_crc", 2, checksum)):
        fields, batches = observation(genuine["native_32"], 32, prefix=kept)
        code.append(f'  sourceFailure (← load folder "{label}") {fields} {batches} ({error})')
    code.extend(['  openFailure (← load folder "empty_input")',
                 '  writerFailure (← load folder "native_32")'])
    V2["run_lean"](scratch, "ToIpc.lean", code)

    emitted = {}
    for label in positives:
        parquet = pq.ParquetFile(pa.BufferReader(files[label]), page_checksum_verification=True)
        expected = [parquet.read_row_group(i).to_pylist() for i in range(parquet.num_row_groups)]
        for selection in ("field", "empty"):
            name = f"{label}_{selection}"
            wire = (scratch / f"{name}.arrow").read_bytes()
            reader = pa.ipc.open_stream(wire)
            assert reader.schema == (parquet.schema_arrow if selection == "field" else pa.schema([]))
            batches = list(reader)
            assert [batch.num_rows for batch in batches] == list(map(len, expected))
            rows = expected if selection == "field" else [[{}] * len(group) for group in expected]
            assert [batch.to_pylist() for batch in batches] == rows
            _, offset = STREAM["metadata"](wire)
            for count in map(len, expected):
                frame = STREAM["read_record"](wire, offset)
                assert frame.rows == count
                offset = frame.end
            assert wire[offset:] == STREAM["EOS"]
            emitted[name] = wire
    print("Checked ten native IPC streams through exact EOS, projection counts and source-error precedence")
    return source_pins | {"lean_ipc": fingerprints(emitted)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for kind, fixtures in captured.items():
        assert fixtures == pins[kind], f"{kind} fixture pins changed"


if __name__ == "__main__":
    main()
