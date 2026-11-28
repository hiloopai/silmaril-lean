"""Verify strict Lean-emitted TwoListStruct IPC against the original Parquet."""

import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
EVENTS = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-events-oracle/check.py"))
RAW = runpy.run_path(str(HERE.parent / "arrow-recursive-batch-writer-oracle/check.py"))
fields_term, batches_term = EVENTS["fields_term"], EVENTS["batches_term"]


LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Defs

open Silmaril.Formats
open Arrow.RecursiveSchema (Field)
open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Arrow.RecursiveSchema.Stream.Events (declarations eraseBatch)
open Parquet.Reader.Recursive (Selection)
open Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc

set_option maxRecDepth 8192

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError (reprStr cause))

private def checkIpc (folder : System.FilePath) (label : String)
    (fields : List (Option String × Field)) (batches : List Observation) : IO Unit := do
  let input ← load folder label
  for (selection, suffix) in [(Selection.field, "field"), (.empty, "empty")] do
    let wire ← take (convert {} {} {} input selection)
    let ⟨source, trace⟩ ← take (Arrow.RecursiveSchema.Stream.Events.read {} wire)
    let expectedFields := if selection = .field then fields else []
    unless declarations source == expectedFields &&
        trace.batches.map eraseBatch == batches.map selection.batch && trace.termination == .eos do
      throw (IO.userError "strict readback differs from the selected declaration or ordered batches")
    let strict ← take (Arrow.RecursiveSchema.Stream.read {} wire)
    let .eos ordinal cursor := strict.terminal | throw (IO.userError "expected strict EOS")
    unless ordinal = batches.length ∧ cursor + 8 = wire.len do
      throw (IO.userError "terminal count or extent differs")
    let .error (.failed trailingOrdinal trailingCursor .trailingBytes) :=
        Arrow.RecursiveSchema.Stream.read {} (wire ++ Arrow.StreamWriter.eos) |
      throw (IO.userError "strict read accepted appended EOS")
    let .error (.failed truncatedOrdinal truncatedCursor (.envelope (.malformed .truncated))) :=
        Arrow.RecursiveSchema.Stream.read {} (wire.slice 0 (wire.len - 1)) |
      throw (IO.userError "strict read accepted incomplete EOS")
    unless trailingOrdinal = ordinal ∧ trailingCursor = cursor ∧
        truncatedOrdinal = ordinal ∧ truncatedCursor = cursor do
      throw (IO.userError "terminal refusal lost its original position")
    IO.FS.writeBinFile (folder / (label ++ "_" ++ suffix ++ ".arrow")) wire.toByteArray

private def exhausted : Arrow.RecursiveSchema.Batch.Limits :=
  { schema.ipc := { fields := 0, batches := 0, rows := 0, metadataBytes := 0, bodyBytes := 0 },
    slots := 0 }

private def sourceFailure (input : Bytes) (batches : List Observation)
    (wanted : Parquet.RecursiveSchema.TwoListStruct.Reader.Events.Error) : IO Unit := do
  for selection in [Selection.field, .empty] do
    for budget in [({} : Arrow.RecursiveSchema.Batch.Limits), exhausted] do
      let .error (.readError actual completed) := convert {} {} budget input selection |
        throw (IO.userError "expected the original source refusal before any writer admission")
      unless actual = wanted ∧ completed == batches.map selection.batch do
        throw (IO.userError "original failure or complete selected prefix differs")

private def openFailure (input : Bytes) : IO Unit := do
  let .error wanted := Parquet.RecursiveSchema.TwoListStruct.openFile {} input |
    throw (IO.userError "expected an original opening refusal")
  for selection in [Selection.field, .empty] do
    let .error (.openError (.openError actual)) := convert {} {} exhausted input selection |
      throw (IO.userError "opening refusal did not take precedence")
    unless actual = wanted do throw (IO.userError "original opening refusal differs")

private def writerFailure (input : Bytes) (selection : Selection) (limits : Arrow.RecursiveSchema.Batch.Limits)
    (wanted : Arrow.RecursiveSchema.Stream.Writer.Error) : IO Unit := do
  let .error (.writer actual) := convert {} {} limits input selection |
    throw (IO.userError "expected a typed writer refusal")
  unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture directory")
"""


def positional(kind, value):
    if value is None:
        return None
    if pa.types.is_struct(kind):
        return tuple(positional(child.type, value[child.name]) for child in kind)
    if pa.types.is_list(kind):
        return [positional(kind.value_type, item) for item in value]
    return value


def inspect_ipc(wire, schema, groups):
    reader = pa.ipc.open_stream(wire)
    assert reader.schema.equals(schema, check_metadata=True)
    fields, cursor = RAW["raw_schema"](wire)
    field_spec = RAW["STREAM"]["SCHEMA"]["pyarrow_field"]
    assert fields == [field_spec(pa, field) for field in schema]
    for group, batch in zip(groups, reader, strict=True):
        record = RAW["read_record"](wire, cursor)
        assert record.rows == batch.num_rows == len(group)
        expected = [[positional(field.type, row[field.name]) for row in group] for field in schema]
        assert RAW["columns"](pa, batch) == expected
        RAW["check_record"](pa, schema, record, expected)
        cursor = record.end
    assert wire[cursor:] == RAW["eos"] and cursor + 8 == len(wire)


def verify(folder):
    files, positives, failures = EVENTS["fixtures"]()
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)

    code, expected, pages = [LEAN], {}, 0
    for label, (schema, rows, wire) in positives.items():
        groups, inspected = EVENTS["inspect_positive"](label, schema, rows, wire)
        expected[label] = schema, groups
        pages += inspected
        code.append(f'  checkIpc folder "{label}" {fields_term(schema)} {batches_term(schema, groups)}')

    schema, groups = expected["native_1111"]
    for label, group, wanted in failures:
        code.append(f'  sourceFailure (← load folder "{label}") {batches_term(schema, groups[:group])} '
                    f'(.group {group} ({wanted}))')
    for label in ("empty_input", "optional_struct"):
        code.append(f'  openFailure (← load folder "{label}")')

    refusals = []
    for selection in ("field", "empty"):
        refusals.extend([
            f'  writerFailure (← load folder "physical_empty") .{selection} {{ schema.ipc.batches := 2 }} '
            '(.batchLimit 3 2)',
            f'  writerFailure (← load folder "physical_empty") .{selection} {{ schema.ipc.rows := 0 }} '
            '(.batch 0 (.ipc (.limit .rows)))',
        ])
    refusals.extend([
        '  writerFailure (← load folder "renamed") .field { schema.depth := 0 } (.schema (.depth 0))',
        '  writerFailure (← load folder "renamed") .field { slots := 0 } (.batch 0 (.slots 0))',
        '  writerFailure (← load folder "renamed") .field { schema.ipc.bodyBytes := 0 } '
        '(.batch 0 (.ipc (.limit .bodyBytes)))',
    ])
    driver = folder / "TwoListStructToIpc.lean"
    driver.write_text("\n".join(code + refusals) + "\n", encoding="utf-8")
    subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                    "--run", str(driver), str(folder)], cwd=ROOT, check=True)

    emitted = {}
    for label, (schema, groups) in expected.items():
        for selection, projected in (("field", schema), ("empty", pa.schema([]))):
            name = f"{label}_{selection}"
            wire = (folder / f"{name}.arrow").read_bytes()
            inspect_ipc(wire, projected, groups)
            emitted[name] = wire
    for selection in ("field", "empty"):
        assert emitted[f"native_1111_{selection}"] == emitted[f"independent_cuts_{selection}"]
    print(f"Checked {len(positives)} sources, {pages} Parquet pages, {len(emitted)} strict IPC streams, "
          f"{len(failures) + 2} source refusals and {len(refusals)} writer refusals")
    return EVENTS["fingerprints"](emitted)


def main():
    assert platform.python_implementation() == "CPython"
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    with tempfile.TemporaryDirectory() as directory:
        assert verify(Path(directory)) == pins, "Lean IPC output pins changed"


if __name__ == "__main__":
    main()
