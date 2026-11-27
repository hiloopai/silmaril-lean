"""Compare direct repeated Parquet Events and actual native Lean IPC with PyArrow."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ORACLES = HERE.parent
ROWS = runpy.run_path(str(ORACLES / "parquet-recursive-repeated-rows-oracle/check.py"))
EVENTS = runpy.run_path(str(ORACLES / "arrow-recursive-events-oracle/check.py"))
IPC = runpy.run_path(str(ORACLES / "arrow-recursive-batch-writer-oracle/check.py"))
SCHEMA, fingerprints, lst = (ROWS[key] for key in ("SCHEMA", "fingerprints", "lst"))

LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Relational
open Arrow.RecursiveSchema (Field)
open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Arrow.RecursiveSchema.Stream.Events (Value Signature declarations eraseBatch)
open Parquet.RecursiveSchema.Repeated (openFile)
open Parquet.RecursiveSchema.Repeated.Rows.Events (Error EventStream readProjected)
open Parquet.RecursiveSchema.Repeated.Rows.ToIpc (convert)

set_option maxRecDepth 4096

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"unexpected refusal: {repr cause}")

private def refuse {ε α : Type} [DecidableEq ε] [Repr ε] (wanted : ε) (result : Except ε α) :
    IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"accepted input expected to fail with {repr wanted}")
  | .error actual =>
    unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")

private def selection (source : Signature) (positions : List Nat) : Scan.Projection source :=
  Scan.Projection.ofArray ((positions.filterMap fun index =>
    if valid : index < source.width then some ⟨index, valid⟩ else none).toArray)

private def direct (input : Bytes) : EventStream :=
  Parquet.RecursiveSchema.Repeated.Rows.Events.read {} {} input

private def project (input : Bytes) (positions : List Nat) : EventStream :=
  readProjected {} {} input (fun source => selection source positions)

private def composed (input : Bytes) (first second : List Nat) : EventStream :=
  readProjected {} {} input (fun source =>
    let projection := selection source first
    projection.comp (selection projection.schema second))

private def check {ε : Type} [DecidableEq ε] [Repr ε] (label : String)
    (result : Arrow.Events.EventStream (Option String) Value ε)
    (fields : List (Option String × Field)) (batches : List Observation)
    (ending : Arrow.Events.Termination ε) : IO Unit := do
  let ⟨source, trace⟩ ← take result
  unless declarations source == fields do
    throw (IO.userError s!"{label}: positional schema differs")
  unless trace.batches.map eraseBatch == batches do
    throw (IO.userError s!"{label}: ordered batches differ")
  unless trace.termination = ending do
    throw (IO.userError s!"{label}: terminal outcome differs")

private def emit (folder : System.FilePath) (label : String) (input : Bytes)
    (fields : List (Option String × Field)) (batches : List Observation) : IO Unit := do
  check label (direct input) fields batches .eos
  let source ← take (openFile {} input)
  let wire ← take (convert {} {} source.schema)
  check label (Arrow.RecursiveSchema.Stream.Events.read {} wire) fields batches .eos
  IO.FS.writeBinFile (folder / (label ++ ".arrow")) wire.toByteArray

private def sourceFailure (input : Bytes) (wanted : Parquet.RecursiveSchema.Repeated.Rows.Error) :
    IO Unit := do
  let source ← take (openFile {} input)
  refuse (.source wanted) (convert {} { schema.ipc := { fields := 0, batches := 0 }, slots := 0 }
    source.schema)
"""


def observed(wire, positions=None, limit=None):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    fields = list(parquet.schema_arrow)
    positions = list(range(len(fields))) if positions is None else positions
    selected = [fields[index] for index in positions]
    declarations = lst(EVENTS["lean_declaration"](pa, field) for field in selected)
    groups, counts = [], []
    count = parquet.num_row_groups if limit is None else limit
    for ordinal in range(count):
        group = parquet.read_row_group(ordinal)
        rows = parquet.metadata.row_group(ordinal).num_rows
        assert rows == group.num_rows
        columns = [group.column(index).to_pylist() for index in positions]
        values = lst(lst(ROWS["ARROW"]["lean_cell"](pa, field.type, column[row])
                         for field, column in zip(selected, columns, strict=True))
                     for row in range(rows))
        groups.append(f"⟨{rows}, {values}⟩")
        counts.append(rows)
    return declarations, lst(groups), counts


def check(label, call, expected, terminal=".eos"):
    return f'  check "{label}" ({call}) {expected[0]} {expected[1]} ({terminal})'


def compare():
    producer = json.loads(SCHEMA["PREDECESSOR"]["MANIFEST"].read_text(encoding="utf-8"))["producer"]
    assert platform.python_implementation() == "CPython"
    assert platform.python_version() == producer["cpython"]
    assert pa.__version__ == producer["pyarrow"] and version("thrift") == producer["thrift"]
    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        positives, edits, genuine, labeled = ROWS["fixtures"](scratch)
        row_pins = json.loads((ORACLES / "parquet-recursive-repeated-rows-oracle/fixtures.json")
                              .read_text(encoding="utf-8"))
        assert fingerprints(genuine) == row_pins["genuine_parquet"]
        assert fingerprints(labeled) == row_pins["labeled_edits"]
        _, _, schema_edits = SCHEMA["fixtures"]()
        refusal = schema_edits["raw_repeated"]
        schema_pins = json.loads((ORACLES / "parquet-recursive-list-schema-oracle/fixtures.json")
                                 .read_text(encoding="utf-8"))
        assert fingerprints({"raw_repeated": refusal}) == {
            "raw_repeated": schema_pins["labeled_edits"]["raw_repeated"]}
        sources = {label: item[2] for label, item in positives.items()}
        inputs = sources | labeled | {"raw_repeated": refusal}
        code = [LEAN, "public def main (args : List String) : IO Unit := do",
                '  let [folder] := args | throw (IO.userError "expected fixture folder")']
        for label, wire in sources.items():
            fields, batches, _ = observed(wire)
            code.append(f'  emit folder "{label}" (← load folder "{label}") {fields} {batches}')
        empty = sources["explicit_empty"]
        code.extend([
            check("repeat_reorder", 'project (← load folder "explicit_empty") [1, 0, 0]',
                  observed(empty, [1, 0, 0])),
            check("empty_projection", 'project (← load folder "explicit_empty") []', observed(empty, [])),
            check("composition", 'composed (← load folder "explicit_empty") [1, 0, 0] [2, 0, 2]',
                  observed(empty, [0, 1, 0])),
        ])
        for label in ("element_presence", "cardinality"):
            _, group, wanted = edits[label]
            assert group == 1
            load = f'(← load folder "{label}")'
            terminal = f".readError (.group {group} ({wanted}))"
            for variant, positions in (("direct", None), ("drop_list", [1, 1]), ("width_zero", [])):
                call = f"direct {load}" if positions is None else f"project {load} {positions}"
                code.append(check(f"{label}_{variant}", call, observed(sources["nested"], positions, group),
                                  terminal))
            code.append(f"  sourceFailure {load} ({wanted})")
        open_error = '.openError (.original (.repetition ⟨3, ["packet", "items", "list"]⟩ (some .repeated)))'
        code.extend([
            f'  refuse ({open_error}) (direct (← load folder "raw_repeated"))',
            f'  refuse ({open_error}) (project (← load folder "raw_repeated") [])',
        ])

        for label, wire in inputs.items():
            (scratch / f"{label}.parquet").write_bytes(wire)
        driver = scratch / "Check.lean"
        driver.write_text("\n".join(code) + "\n", encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        "--run", str(driver), directory], cwd=ROOT, check=True)
        outputs = {}
        for label, source in sources.items():
            wire = (scratch / f"{label}.arrow").read_bytes()
            parquet = pq.ParquetFile(pa.BufferReader(source), page_checksum_verification=True)
            reader = pa.ipc.open_stream(wire)
            assert reader.schema.equals(parquet.schema_arrow)
            fields, cursor = IPC["raw_schema"](wire)
            assert fields == [EVENTS["SCHEMA"]["pyarrow_field"](pa, field) for field in parquet.schema_arrow]
            counts = []
            groups = range(parquet.num_row_groups)
            for batch, ordinal in zip(reader, groups, strict=True):
                raw = IPC["read_record"](wire, cursor)
                original = parquet.read_row_group(ordinal)
                assert batch.num_rows == raw.rows == original.num_rows
                assert batch.to_pylist() == original.to_pylist()
                counts.append(raw.rows)
                cursor = raw.end
            assert wire[cursor:] == IPC["eos"]
            outputs[label] = wire
            print(f"{label}: direct Events and native IPC group counts {counts}", flush=True)
    print("Verified seven actual Lean streams, late projected errors and original source precedence")
    return fingerprints(outputs)


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert compare() == pins["lean_ipc"]


if __name__ == "__main__":
    main()
