"""Verify strict Lean IPC for the shared Tree reader against PyArrow and independent wire decoding."""

import json
from pathlib import Path
import runpy
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
EVENTS_DIR = HERE.parent / "parquet-recursive-tree-events-oracle"
EVENTS = runpy.run_path(str(EVENTS_DIR / "check.py"))
IPC = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-to-ipc-oracle/check.py"))
NATIVE, V2, lst = (EVENTS[key] for key in ("NATIVE", "V2", "lst"))
fields_term = EVENTS["EVENTS"]["fields_term"]
fingerprints = NATIVE["fingerprints"]


LEAN = """
module

import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Relational
open RecursiveSchema.Tree
open Arrow.RecursiveSchema (Field)
open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch)

set_option maxRecDepth 8192

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private inductive View where
  | full | reverse | first | empty
  deriving Repr

private def View.columns (view : View) (source : Signature) : Scan.Projection source :=
  match view with
  | .full => .id source
  | .reverse => .ofArray (List.finRange source.width).reverse.toArray
  | .first => .ofArray ((List.finRange source.width).take 1).toArray
  | .empty => .ofArray #[]

private def convert (input : Bytes) (view : View) (limits : Arrow.RecursiveSchema.Batch.Limits := {}) :
    Except Rows.Events.ToIpc.Error KBytes :=
  Rows.Events.ToIpc.convert {} {} limits input view.columns

private def checkIpc (folder : System.FilePath) (label : String) (view : View) (suffix : String)
    (fields : List (Option String × Field)) (batches : List Observation) : IO Unit := do
  let wire ← take (convert (← load folder label) view)
  let ⟨source, trace⟩ ← take (Arrow.RecursiveSchema.Stream.Events.read {} wire)
  unless declarations source == fields && trace.batches.map eraseBatch == batches &&
      trace.batches.map (·.rowCount) == batches.map (·.rowCount) && decide (trace.termination = .eos) do
    throw (IO.userError s!"strict readback differs for {label} {repr view}")
  let strict ← take (Arrow.RecursiveSchema.Stream.read {} wire)
  let .eos ordinal cursor := strict.terminal | throw (IO.userError "expected exact EOS")
  unless ordinal = batches.length ∧ cursor + 8 = wire.len do
    throw (IO.userError "strict terminal count or extent differs")
  let .error (.failed extraOrdinal extraCursor .trailingBytes) :=
    Arrow.RecursiveSchema.Stream.read {} (wire ++ Arrow.StreamWriter.eos) |
      throw (IO.userError "strict read accepted appended EOS")
  let .error (.failed shortOrdinal shortCursor (.envelope (.malformed .truncated))) :=
    Arrow.RecursiveSchema.Stream.read {} (wire.slice 0 (wire.len - 1)) |
      throw (IO.userError "strict read accepted truncated EOS")
  unless extraOrdinal = ordinal ∧ extraCursor = cursor ∧ shortOrdinal = ordinal ∧ shortCursor = cursor do
    throw (IO.userError "terminal refusal lost its original position")
  IO.FS.writeBinFile (folder / (label ++ "_" ++ suffix ++ ".arrow")) wire.toByteArray

private def exhausted : Arrow.RecursiveSchema.Batch.Limits :=
  { schema.ipc := { fields := 0, batches := 0, rows := 0, metadataBytes := 0, bodyBytes := 0 },
    slots := 0 }

private def sourceFailure (input : Bytes) (view : View) (batches : List Observation)
    (wanted : Rows.Events.Error) : IO Unit := do
  for limits in [({} : Arrow.RecursiveSchema.Batch.Limits), exhausted] do
    let .error (.readError actual completed) := convert input view limits |
      throw (IO.userError "expected the original source refusal before writer admission")
    unless decide (actual = wanted) && completed == batches do
      throw (IO.userError (reprStr actual))

private def openFailure (input : Bytes) (wanted : RecursiveSchema.Repeated.Error) : IO Unit := do
  for view in [View.full, .reverse, .first, .empty] do
    let .error (.openError (.openError actual)) := convert input view exhausted |
      throw (IO.userError "the opening refusal must precede target budgets")
    unless actual = wanted do throw (IO.userError (reprStr actual))

private def writerFailure (input : Bytes) (view : View) (limits : Arrow.RecursiveSchema.Batch.Limits)
    (wanted : Arrow.RecursiveSchema.Stream.Writer.Error) : IO Unit := do
  let .error (.writer actual) := convert input view limits |
    throw (IO.userError "expected a typed target refusal")
  unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture directory")
"""


def views(schema):
    full = list(range(len(schema)))
    for name, positions in (("full", full), ("reverse", full[::-1]), ("first", full[:1]), ("empty", [])):
        yield name, pa.schema([schema[i] for i in positions])


def batches_term(schema, groups):
    return lst(NATIVE["expected_observation"](schema, group) for group in groups)


def verify(folder):
    good, authored, bad, rejected, branch_schema, prefix = EVENTS["create"]()
    source_pins = json.loads((EVENTS_DIR / "fixtures.json").read_text(encoding="utf-8"))
    assert source_pins["producer"] == EVENTS["COMPILER"]["BASE"]["producer"]()
    assert source_pins["genuine_parquet"] == fingerprints(
        {label: case[-1] for label, case in good.items()} | {"unsupported_double": rejected})
    assert source_pins["authored_parquet"] == fingerprints(
        {label: case[-1] for label, case in authored.items()} | {label: case[0] for label, case in bad.items()})

    lines, expected = [LEAN], {}
    group_count = 0
    for label, (schema, rows, wire) in (good | authored).items():
        (folder / f"{label}.parquet").write_bytes(wire)
        parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
        assert parquet.schema_arrow.equals(schema, check_metadata=True)
        groups = [parquet.read_row_group(i).to_pylist() for i in range(parquet.num_row_groups)]
        assert groups == rows
        group_count += len(groups)
        for view, selected in views(schema):
            lines.append(f'  checkIpc folder "{label}" .{view} "{view}" '
                         f'{fields_term(selected)} {batches_term(selected, groups)}')
            expected[f"{label}_{view}"] = selected, groups

    for label, (wire, cause) in bad.items():
        (folder / f"{label}.parquet").write_bytes(wire)
        parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
        assert parquet.read_row_group(0).to_pylist() == prefix[0]
        for view, selection in views(branch_schema):
            lines.append(f'  sourceFailure (← load folder "{label}") .{view} {batches_term(selection, prefix)} ({cause})')

    (folder / "unsupported_double.parquet").write_bytes(rejected)
    lines.extend([
        '  openFailure (← load folder "unsupported_double")',
        '    (.original (.physical ⟨4, ["items", "list", "element", "a"]⟩ .double))',
    ])
    controls = [
        '  writerFailure (← load folder "physical_zero_group") .full { schema.ipc.batches := 2 } (.batchLimit 3 2)',
        '  writerFailure (← load folder "physical_zero_group") .empty { schema.ipc.batches := 2 } (.batchLimit 3 2)',
        '  writerFailure (← load folder "physical_zero_group") .empty { schema.ipc.rows := 0 } '
        '(.batch 0 (.ipc (.limit .rows)))',
        '  writerFailure (← load folder "renamed_branch_v2") .reverse { schema.depth := 0 } (.schema (.depth 0))',
        '  writerFailure (← load folder "renamed_branch_v2") .first { slots := 0 } (.batch 0 (.slots 0))',
        '  writerFailure (← load folder "renamed_branch_v2") .reverse { schema.ipc.bodyBytes := 0 } '
        '(.batch 0 (.ipc (.limit .bodyBytes)))',
    ]
    V2["run_lean"](folder, "RecursiveTreeToIpc.lean", lines + controls)

    emitted = {}
    for name, (selected, groups) in expected.items():
        wire = (folder / f"{name}.arrow").read_bytes()
        IPC["inspect_ipc"](wire, selected, groups)
        emitted[name] = wire
    for view, _ in views(branch_schema):
        assert emitted[f"branch_v1_{view}"] == emitted[f"branch_v2_{view}"]
    print(f"Checked {len(good) + len(authored)} accepted carriers, {group_count} original groups, "
          f"{len(emitted)} strict IPC streams and {len(bad) + 1} source and {len(controls)} target controls")
    return fingerprints(emitted)


def main():
    manifest = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    with tempfile.TemporaryDirectory() as directory:
        assert verify(Path(directory)) == manifest["emitted_ipc"]


if __name__ == "__main__":
    main()
