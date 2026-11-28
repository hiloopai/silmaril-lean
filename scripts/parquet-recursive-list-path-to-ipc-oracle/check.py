"""Read exact Lean-emitted LIST-path IPC from original native Parquet sources."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import tempfile

import pyarrow as pa


HERE = Path(__file__).resolve().parent
EVENTS = runpy.run_path(str(HERE.parent / "parquet-recursive-list-path-events-oracle/check.py"))
RAW = runpy.run_path(str(HERE.parent / "arrow-recursive-batch-writer-oracle/check.py"))
NATIVE = EVENTS["NATIVE"]
capture, fingerprints = EVENTS["capture"], EVENTS["fingerprint"]


LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Arrow.RecursiveSchema (Field)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events (Value declarations eraseBatch)
open Parquet.Reader.Recursive (Selection)
open Parquet.RecursiveSchema.ListPath.Reader.ToIpc

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError (reprStr cause))

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def selected (selection : Selection) (fields : List (Option String × Field))
    (batches : List Observation) : List (Option String × Field) × List Observation :=
  match selection with
  | .field => (fields, batches)
  | .empty => ([], batches.map fun batch => ⟨batch.rowCount, List.replicate batch.rowCount []⟩)

private def checkTrace {ε : Type} [Repr ε] [DecidableEq ε]
    (result : Arrow.Events.EventStream (Option String) Value ε)
    (fields : List (Option String × Field)) (batches : List Observation)
    (ending : Arrow.Events.Termination ε) : IO Unit := do
  let ⟨source, trace⟩ ← take result
  unless declarations source == fields && trace.batches.map eraseBatch == batches do
    throw (IO.userError "declaration, ordered batch or count differs")
  unless trace.termination = ending do throw (IO.userError "terminal outcome differs")

private def checkIpc (folder : System.FilePath) (label : String) (input : Bytes) (depth : Nat)
    (fields : List (Option String × Field)) (batches : List Observation) : IO Unit := do
  let cap : Parquet.Snapshot.Limits := { maxSchemaDepth := 2 * depth + 2 }
  for (selection, suffix) in [(Selection.field, "field"), (.empty, "empty")] do
    let (projected, expected) := selected selection fields batches
    let wire ← take (convert cap {} {} input selection)
    checkTrace (Parquet.RecursiveSchema.ListPath.Reader.Events.readProjected cap {} input selection)
      projected expected .eos
    checkTrace (Arrow.RecursiveSchema.Stream.Events.read {} wire) projected expected .eos
    let strict ← take (Arrow.RecursiveSchema.Stream.read {} wire)
    let .eos ordinal offset := strict.terminal | throw (IO.userError "expected strict EOS")
    unless ordinal = batches.length ∧ offset + 8 = wire.len do
      throw (IO.userError "exact terminal offset or batch count differs")
    let .error (.failed index cursor .trailingBytes) :=
        Arrow.RecursiveSchema.Stream.read {} (wire ++ Arrow.StreamWriter.eos) |
      throw (IO.userError "strict read accepted appended EOS")
    unless index = ordinal ∧ cursor = offset do throw (IO.userError "trailing EOS lost its address")
    let .error (.failed index cursor (.envelope (.malformed .truncated))) :=
        Arrow.RecursiveSchema.Stream.read {} (wire.slice 0 (wire.len - 1)) |
      throw (IO.userError "strict read accepted incomplete EOS")
    unless index = ordinal ∧ cursor = offset do throw (IO.userError "incomplete EOS lost its address")
    IO.FS.writeBinFile (folder / (label ++ "_" ++ suffix ++ ".arrow")) wire.toByteArray

private def exhausted : Arrow.RecursiveSchema.Batch.Limits :=
  { schema.ipc := { fields := 0, batches := 0, rows := 0, metadataBytes := 0, bodyBytes := 0 },
    slots := 0 }

private def sourceFailure (input : Bytes) (fields : List (Option String × Field)) (batches : List Observation)
    (cause : Parquet.RecursiveSchema.ListPath.Reader.Events.Error) : IO Unit := do
  for selection in [Selection.field, .empty] do
    let (projected, expected) := selected selection fields batches
    checkTrace (Parquet.RecursiveSchema.ListPath.Reader.Events.readProjected {} {} input selection)
      projected expected (.readError cause)
    for budget in [({} : Arrow.RecursiveSchema.Batch.Limits), exhausted] do
      let .error (.readError actual completed) := convert {} {} budget input selection |
        throw (IO.userError "source failure did not take precedence")
      unless actual = cause ∧ completed == expected do
        throw (IO.userError "native error or complete selected prefix differs")

private def openFailure (input : Bytes) : IO Unit := do
  let .error cause := Parquet.RecursiveSchema.ListPath.openFile {} input |
    throw (IO.userError "expected an open refusal")
  for selection in [Selection.field, .empty] do
    let .error (.openError (.openError actual)) := convert {} {} exhausted input selection |
      throw (IO.userError "open error did not take precedence")
    unless actual = cause do throw (IO.userError "original open error differs")

private def writerFailure (input : Bytes) (selection : Selection) (limits : Arrow.RecursiveSchema.Batch.Limits)
    (wanted : Arrow.RecursiveSchema.Stream.Writer.Error) : IO Unit := do
  let .error (.writer actual) := convert {} {} limits input selection |
    throw (IO.userError "expected typed writer refusal")
  unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
"""


def verify(folder):
    genuine, authored, positive = EVENTS["fixtures"]()
    pins = {"genuine_parquet": fingerprints(genuine), "authored_controls": fingerprints(authored)}
    old_pins = json.loads((EVENTS["HERE"] / "fixtures.json").read_text(encoding="utf-8"))
    assert all(values == old_pins[kind] for kind, values in pins.items())
    files = genuine | authored
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)
    code = [LEAN, *NATIVE["V1"]["ENTRY"]]
    frames = 0
    for label, (schema, nullable, width, groups) in positive.items():
        inspected = capture(files[label], schema, nullable, width, groups)
        frames += sum(len(group[-1]) for group in inspected)
        code.append(f'  checkIpc folder "{label}" (← load folder "{label}") {len(nullable) - 1} '
                    f'{EVENTS["declarations"](schema)} {EVENTS["batch_terms"](groups, width)}')

    source = EVENTS["SOURCE"]
    schema, _, width, groups = positive[source]
    for label, error in EVENTS["late_errors"](authored, positive):
        code.append(f'  sourceFailure (← load folder "{label}") {EVENTS["declarations"](schema)} '
                    f'{EVENTS["batch_terms"](groups[:1], width)} ({error})')
    code.append('  openFailure (← load folder "empty_input")')

    refusals = []
    for selection in ("field", "empty"):
        refusals.extend([
            f'  writerFailure (← load folder "empty_group") .{selection} {{ schema.ipc.batches := 0 }} '
            '(.batchLimit 3 0)',
            f'  writerFailure (← load folder "empty_group") .{selection} {{ schema.ipc.rows := 0 }} '
            '(.batch 0 (.ipc (.limit .rows)))',
            f'  writerFailure (← load folder "signed_64_depth_3_0") .{selection} {{ schema.ipc.rows := 2 }} '
            '(.batch 1 (.ipc (.limit .rows)))',
        ])
    refusals.extend([
        f'  writerFailure (← load folder "{source}") .field {{ schema.depth := 0 }} (.schema (.depth 0))',
        f'  writerFailure (← load folder "{source}") .field {{ slots := 0 }} (.batch 0 (.slots 0))',
    ])
    NATIVE["V2"]["run_lean"](folder, "ListPathToIpc.lean", code + refusals)

    emitted = {}
    for label, (schema, _, _, groups) in positive.items():
        for selection in ("field", "empty"):
            name = f"{label}_{selection}"
            wire = (folder / f"{name}.arrow").read_bytes()
            selected_schema = schema if selection == "field" else pa.schema([])
            reader = pa.ipc.open_stream(wire)
            assert reader.schema.equals(selected_schema, check_metadata=True)
            fields, cursor = RAW["raw_schema"](wire)
            assert fields == [RAW["STREAM"]["SCHEMA"]["pyarrow_field"](pa, field) for field in selected_schema]
            for group, batch in zip(groups, reader, strict=True):
                record = RAW["read_record"](wire, cursor)
                assert record.rows == batch.num_rows == len(group)
                expected = [group] if selection == "field" else []
                assert RAW["columns"](pa, batch) == expected
                RAW["check_record"](pa, selected_schema, record, expected)
                cursor = record.end
            assert wire[cursor:] == RAW["eos"] and cursor + 8 == len(wire)
            emitted[name] = wire
    for selection in ("field", "empty"):
        assert emitted[f"{source}_{selection}"] == emitted[f"deep_reframed_{selection}"]
    print(f"Checked {len(positive)} Parquet sources and {frames} original pages, {len(emitted)} native IPC streams "
          f"through exact EOS, three source failures and {len(refusals)} typed writer-budget refusals")
    return pins | {"lean_ipc": fingerprints(emitted)}


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
