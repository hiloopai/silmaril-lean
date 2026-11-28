"""Compare direct two-LIST event traces with pinned PyArrow rows."""

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
ROWS = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-rows-oracle/check.py"))
V1, V2, FRAMES, PATH, fingerprints, lst, samples, schema_for, write, inspect, raw_chunks, repack, frame = (
    ROWS[k] for k in ("V1", "V2", "FRAMES", "PATH", "fingerprints", "lst", "samples", "schema_for", "write",
                      "inspect", "raw_chunks", "repack", "frame")
)
field_term, batch_term = ROWS["field_term"], ROWS["batch_term"]

LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.Defs

open Silmaril.Formats
open Silmaril.Formats.Arrow.RecursiveSchema (Field)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events (declarations eraseBatch eraseRow)
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"unexpected refusal: {repr cause}")

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def direct (input : Bytes) : EventStream :=
  Parquet.RecursiveSchema.TwoList.Rows.Events.read {} {} input

private def check (result : EventStream) (fields : List (Option String × Field))
    (batches : List Observation) (ending : Arrow.Events.Termination Error) : IO Unit := do
  let ⟨source, trace⟩ ← take result
  unless declarations source == fields do throw (IO.userError "positional schema differs")
  unless trace.batches.map eraseBatch == batches do throw (IO.userError "ordered batch or count differs")
  unless trace.collect.table.rows.map eraseRow == batches.flatMap (·.rows) do
    throw (IO.userError "collected rows differ")
  unless trace.termination = ending do throw (IO.userError "terminal outcome differs")

private def checkFile (input : Bytes) (fields : List (Option String × Field))
    (batches : List Observation) (ending : Arrow.Events.Termination Error := .eos) : IO Unit := do
  check (direct input) fields batches ending
  check (readProjected {} {} input .field) fields batches ending
  let empty := batches.map fun batch => { batch with rows := List.replicate batch.rowCount [] }
  check (readProjected {} {} input .empty) [] empty ending

private def checkReframe (original reframed : Bytes) : IO Unit := do
  for selection in [Selection.field, .empty] do
    let ⟨schema, before⟩ ← take (readProjected {} {} original selection)
    let ⟨other, after⟩ ← take (readProjected {} {} reframed selection)
    unless declarations schema == declarations other ∧
        before.collect.table.rows.map eraseRow == after.collect.table.rows.map eraseRow ∧
        before.batches.map (·.rowCount) = after.batches.map (·.rowCount) ∧
        before.termination = after.termination do throw (IO.userError "reframing changed the observed trace")

private def refuseOpen (input : Bytes) : IO Unit := do
  let .error cause := Parquet.RecursiveSchema.TwoList.openFile {} input |
    throw (IO.userError "expected original open failure")
  for result in [direct input, readProjected {} {} input .field, readProjected {} {} input .empty] do
    let .error error := result | throw (IO.userError "open failure produced a schema")
    unless error = .openError cause do throw (IO.userError "original open error changed")

set_option maxRecDepth 8192
"""


def observation(wire, width, prefix=None):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    fields = lst(f"(some {json.dumps(field.name)}, {field_term(field)})" for field in parquet.schema_arrow)
    count = parquet.num_row_groups if prefix is None else prefix
    groups = [parquet.read_row_group(i).column(0).to_pylist() for i in range(count)]
    assert [len(group) for group in groups] == [parquet.metadata.row_group(i).num_rows for i in range(count)]
    return fields, lst(batch_term(group, width) for group in groups)


def fixtures():
    nullable = (True, True, True)
    genuine, labeled, positives = {}, {}, {}
    for width in (32, 64):
        first, second = samples(nullable, width)
        groups = [first[:3], second, first[-2:]]
        schema = schema_for(nullable, width)
        native = f"native_{width}"
        genuine[native] = write(schema, groups)
        wire = genuine[native]
        manifest = list(inspect(wire, nullable, width, groups))
        carrier = raw_chunks(wire)
        target = (1, 0)
        slots = [slot for page in manifest[1][-1] for slot in page[-1]]
        assert [(rep, definition) for rep, definition, _ in slots[:6]] == [
            (0, 1), (0, 5), (1, 2), (1, 3), (1, 4), (2, 5),
        ]
        cuts = [[slots[i]] for i in range(5)] + [slots[5:]]
        template = carrier[target][0]
        pages = [frame(template, section, width) for section in cuts]
        label = f"reframed_{width}"
        labeled[label] = repack(wire, carrier | {target: pages})
        reframed = list(inspect(labeled[label], nullable, width, groups))
        assert [page[-1][0][0] for page in reframed[1][-1]] == [0, 0, 1, 1, 1, 2]
        positives[native] = positives[label] = width
        if width == 32:
            bad_later = frame(template, manifest[2][-1][0][-1], width, crc=False)
            later = [bad_later, *carrier[2, 0][1:]]
            labeled["late_crc"] = repack(wire, carrier | {(2, 0): later})
            pages[3] = frame(template, [(2, 5, 7)], width)
            labeled["first_of_two_errors"] = repack(wire, carrier | {target: pages, (2, 0): later})
    genuine["schema_only"] = write(schema_for(nullable, 32), [])
    positives["schema_only"] = 32
    labeled["empty_input"] = b""
    return genuine, labeled, positives


def verify(scratch):
    genuine, labeled, positives = fixtures()
    files = genuine | labeled
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)
    code = [LEAN, *V1["ENTRY"]]
    for label, width in positives.items():
        fields, batches = observation(files[label], width)
        code.append(f'  checkFile (← load folder "{label}") {fields} {batches}')
    for width in (32, 64):
        code.append(f'  checkReframe (← load folder "native_{width}") (← load folder "reframed_{width}")')

    def original_frame(label, position, ordinal):
        lo, hi = next((start, stop) for key, _, start, stop in V2["columns"](files[label]) if key == position)
        return list(FRAMES(files[label], lo, hi))[ordinal]

    at, *_ = original_frame("first_of_two_errors", (1, 0), 3)
    path = json.dumps(PATH)
    first_error = (f".readError (.group 1 (.chunk (.page ⟨1, 0, {path}⟩ 3 {at} ⟨3, 2, .outer⟩ "
                   "(.level (.closedAncestor 3 2 .outer)))))")
    fields, batches = observation(files["native_32"], 32, prefix=1)
    code.append(f'  checkFile (← load folder "first_of_two_errors") {fields} {batches} ({first_error})')

    at, header, _, body = original_frame("late_crc", (2, 0), 0)
    wanted, actual = header[4][1] & 0xffffffff, zlib.crc32(body)
    assert wanted != actual
    late_error = (f".readError (.group 2 (.chunk (.page ⟨2, 0, {path}⟩ 0 {at} {{}} "
                  f"(.checksum (.mismatch {wanted} {actual})))))")
    fields, batches = observation(files["native_32"], 32, prefix=2)
    code.append(f'  checkFile (← load folder "late_crc") {fields} {batches} ({late_error})')
    code.append('  refuseOpen (← load folder "empty_input")')
    V2["run_lean"](scratch, "Events.lean", code)
    print("Checked five positive event streams, two legal reframes, original failure prefixes and an open refusal")
    return {"genuine": fingerprints(genuine), "labeled": fingerprints(labeled)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for name, fixtures in captured.items():
        assert fixtures == pins[name], f"{name} fixture pins changed"


if __name__ == "__main__":
    main()
