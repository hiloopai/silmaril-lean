"""Check direct shared Events against pinned positional PyArrow Parquet reads."""

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
PARQUET = runpy.run_path(str(HERE.parent / "parquet-recursive-rows-oracle/check.py"))
SCHEMA = PARQUET["CHUNK"]["SCHEMA"]
EVENTS = runpy.run_path(str(HERE.parent / "arrow-recursive-events-oracle/check.py"))
lean_list, lean_cell = (EVENTS["ROWS"][name] for name in ("lean_list", "lean_cell"))

LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.Rows.Events.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Rows.Events.Defs

open Silmaril Silmaril.Formats Silmaril.Relational
open Arrow.RecursiveSchema (Field)
open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch)
open Parquet.RecursiveSchema.Rows.Events (Error EventStream readProjected)

private def load (folder : System.FilePath) (name : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (name ++ ".parquet"))⟩

private def selection (source : Signature) (positions : List Nat) : Scan.Projection source :=
  Scan.Projection.ofArray ((positions.filterMap fun index =>
    if valid : index < source.width then some ⟨index, valid⟩ else none).toArray)

private def direct (input : Bytes) : EventStream :=
  Parquet.RecursiveSchema.Rows.Events.read {} {} input

private def project (input : Bytes) (positions : List Nat) : EventStream :=
  readProjected {} {} input (fun source => selection source positions)

private def composed (input : Bytes) (first second : List Nat) : EventStream :=
  readProjected {} {} input (fun source =>
    let projection := selection source first
    projection.comp (selection projection.schema second))

private def check (label : String) (result : EventStream)
    (fields : List (Option String × Field)) (batches : List Observation)
    (ending : Arrow.Events.Termination Error) : IO Unit :=
  match result with
  | .error cause => throw (IO.userError s!"{label}: unexpected open error {repr cause}")
  | .ok ⟨source, trace⟩ => do
    unless declarations source == fields do
      throw (IO.userError s!"{label}: positional schema differs")
    unless trace.batches.map eraseBatch == batches do
      throw (IO.userError s!"{label}: ordered batches differ")
    unless trace.termination = ending do
      throw (IO.userError s!"{label}: terminal outcome differs")

private def checkOpen (input : Bytes) (wanted : Error) : IO Unit :=
  match direct input, project input [] with
  | .error original, .error projected =>
    unless original = wanted ∧ projected = wanted do
      throw (IO.userError s!"wrong open errors: {repr original}, {repr projected}")
  | _, _ => throw (IO.userError "expected open refusal before any Events")
"""


def expectations(wire, positions=None, limit=None):
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    fields = list(parquet.schema_arrow)
    positions = list(range(len(fields))) if positions is None else positions
    expected = lean_list(EVENTS["lean_declaration"](pa, fields[index]) for index in positions)
    count = parquet.num_row_groups if limit is None else limit
    batches = []
    counts = []
    for ordinal in range(count):
        group = parquet.read_row_group(ordinal)
        rows = parquet.metadata.row_group(ordinal).num_rows
        assert group.num_rows == rows
        columns = [group.column(index).to_pylist() for index in positions]
        values = lean_list(
            lean_list(lean_cell(pa, fields[index].type, column[row])
                      for index, column in zip(positions, columns, strict=True))
            for row in range(rows)
        )
        batches.append(f"⟨{rows}, {values}⟩")
        counts.append(rows)
    return expected, lean_list(batches), counts


def check(label, call, expected, terminal=".eos"):
    return f'  check "{label}" ({call}) {expected[0]} {expected[1]} ({terminal})'


def main():
    producer = json.loads((HERE.parent / "parquet-recursive-rows-oracle/fixtures.json")
                          .read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert platform.python_version() == producer["producer"]["cpython"]
    assert pa.__version__ == producer["producer"]["pyarrow"]
    assert version("thrift") == producer["producer"]["thrift"]
    positives, empty, edits, extra = PARQUET["fixtures"]()
    fingerprints = PARQUET["fingerprints"]
    sources = {name: fixture[2] for name, fixture in positives.items()}
    assert fingerprints(sources) == producer["genuine_parquet"]
    labeled = {name: fixture[0] for name, fixture in edits.items()}
    labeled.update(explicit_empty=empty[2], extra_original=extra)
    assert fingerprints(labeled) == producer["labeled_parquet"]
    sources["explicit_empty"] = empty[2]
    _, schema_controls, _ = SCHEMA["fixtures"]()
    list_control = {"list": schema_controls["list"]}
    schema_pins = json.loads(SCHEMA["MANIFEST"].read_text(encoding="utf-8"))
    assert fingerprints(list_control) == {"list": schema_pins["genuine_parquet"]["list"]}

    code = [LEAN, "public def main (args : List String) : IO Unit := do",
            '  let [folder] := args | throw (IO.userError "expected fixture folder")']
    for label, wire in sources.items():
        expected = expectations(wire)
        code.append(check(label, f'direct (← load folder "{label}")', expected))
        print(f"{label}: positional batches {expected[2]}", flush=True)

    for label, indices in (("repeat_reorder", [1, 0, 0]), ("empty_projection", [])):
        code.append(check(label, f'project (← load folder "explicit_empty") {indices}',
                          expectations(empty[2], indices)))
    code.append(check("projection_composition",
                      'composed (← load folder "explicit_empty") [1, 0, 0] [2, 0, 2]',
                      expectations(empty[2], [0, 1, 0])))

    for label, (_, row, info) in edits.items():
        site, first, conflict, prior_count, _ = info
        assert first.group == 1
        coords = [f"⟨{col.index}, {PARQUET['path_term'](col.path)}⟩" for col in (first, conflict)]
        cause = f".sibling {first.group} {row} {PARQUET['location_term'](site)} {' '.join(coords)}"
        terminal = f".readError (.group {first.group} ({cause}))"
        for variant, indices in (("direct", None), ("drop_ancestor", [1, 1]), ("width_zero", [])):
            expected = expectations(sources["multipage"], indices, limit=first.group)
            assert expected[2] == [prior_count]
            load = f'(← load folder "{label}")'
            call = f"direct {load}" if indices is None else f"project {load} {indices}"
            code.append(check(f"{label}_{variant}", call, expected, terminal))
        print(f"{label}: retained {prior_count} rows, original group {first.group}, row {row}",
              flush=True)
    code.extend([
        '  checkOpen (← load folder "extra_original") '
        '(.openError (.snapshot (.invalidMetadata .columns)))',
        '  checkOpen (← load folder "list") (.openError (.annotation ⟨1, ["items"]⟩))',
    ])

    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        for label, wire in (sources | labeled | list_control).items():
            (scratch / f"{label}.parquet").write_bytes(wire)
        driver = scratch / "Check.lean"
        driver.write_text("\n".join(code) + "\n", encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        "--run", str(driver), directory], cwd=ROOT, check=True)
    print("Checked 6 genuine Parquet pins, 4 labeled controls and 17 direct/projected comparisons")


if __name__ == "__main__":
    main()
