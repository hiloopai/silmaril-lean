"""Compare native TwoListStruct Events with pinned PyArrow group observations."""

from copy import deepcopy
from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREVIOUS_DIR = HERE.parent / "parquet-recursive-two-list-struct-oracle"
NATIVE = runpy.run_path(str(PREVIOUS_DIR / "check.py"))
lst, fingerprints, write, inspect = (NATIVE[key] for key in ("lst", "fingerprints", "write", "inspect"))


LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events.Defs

open Silmaril.Formats
open Arrow.RecursiveSchema (Field)
open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Arrow.RecursiveSchema.Stream.Events (declarations eraseBatch eraseRow)
open Parquet.Reader.Recursive (Selection)
open Parquet.RecursiveSchema.TwoListStruct.Reader.Events

set_option maxRecDepth 8192

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def check (result : EventStream) (fields : List (Option String × Field))
    (batches : List Observation) (ending : Arrow.Events.Termination Error) : IO Unit := do
  let .ok ⟨source, trace⟩ := result |
    throw (IO.userError "unexpected refusal before schema")
  unless declarations source == fields do
    throw (IO.userError s!"declaration differs: {repr (declarations source)}")
  unless trace.batches.map eraseBatch == batches do
    throw (IO.userError "ordered complete batches or row counts differ")
  unless trace.collect.table.rows.map eraseRow == batches.flatMap (·.rows) do
    throw (IO.userError "collected rows differ")
  unless trace.termination = ending do
    throw (IO.userError "original terminal outcome differs")

private def checkFile (input : Bytes) (fields : List (Option String × Field))
    (batches : List Observation) (ending : Arrow.Events.Termination Error := .eos) : IO Unit := do
  check (read {} {} input) fields batches ending
  check (readProjected {} {} input .field) fields batches ending
  let empty : List Observation := batches.map fun batch => ⟨batch.rowCount, List.replicate batch.rowCount []⟩
  check (readProjected {} {} input .empty) [] empty ending

private def checkOpenError (input : Bytes) : IO Unit := do
  let .error cause := Parquet.RecursiveSchema.TwoListStruct.openFile {} input |
    throw (IO.userError "expected original open error")
  for result in [read {} {} input, readProjected {} {} input .field, readProjected {} {} input .empty] do
    let .error reported := result | throw (IO.userError "open error emitted a schema")
    unless reported = .openError cause do
      throw (IO.userError "original open error differs")

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture directory")
"""


def physical_empty(wire):
    footer = NATIVE["metadata"](wire)
    thrift = NATIVE["THRIFT"]
    groups = thrift["list_field"](footer, 4)
    empty = deepcopy(groups[0])
    empty[3] = TType.I64, 0
    groups.insert(1, empty)
    source = NATIVE["raw_chunks"](wire)
    chunks = {(0, side): source[0, side] for side in range(2)}
    for side, width in enumerate(NATIVE["WIDTHS"]):
        thrift["column_metadata"](footer, 1, side)[5] = TType.I64, 0
        chunks[1, side] = [NATIVE["frame"](source[0, side][0], [], width)]
        chunks[2, side] = source[1, side]
    return NATIVE["repack"](wire, chunks, footer)


def renamed():
    element = pa.struct([pa.field("west", pa.int64()), pa.field("east", pa.int32(), False)])
    inner = pa.list_(pa.field("point", element, False))
    outer = pa.list_(pa.field("segment", inner))
    schema = pa.schema([pa.field("samples", outer)])
    groups = [[None, [], [None, [], [{"west": -2**62, "east": -2**30}, {"west": None, "east": 7}]]]]
    return schema, groups, write(schema, groups, use_compliant_nested_type=False)


def field_term(field):
    kind = field.type
    if pa.types.is_list(kind):
        tag, children = ".list", [kind.value_field]
    elif pa.types.is_struct(kind):
        tag, children = ".struct", list(kind)
    else:
        tag, children = {pa.int32(): ".int32", pa.int64(): ".int64"}[kind], []
    return f".node (some {json.dumps(field.name)}) {str(field.nullable).lower()} {tag} {lst(map(field_term, children))}"


def fields_term(schema):
    return lst(f"(some {json.dumps(field.name)}, {field_term(field)})" for field in schema)


def batches_term(schema, groups):
    observation = NATIVE["expected_observation"]
    return lst(observation(schema, group) for group in groups)


def pyarrow_groups(wire, expected_schema, expected_groups):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.equals(expected_schema, check_metadata=True)
    batches = [parquet.read_row_group(ordinal).to_pylist() for ordinal in range(parquet.num_row_groups)]
    assert batches == [[{expected_schema.field(0).name: row} for row in group] for group in expected_groups]
    return batches


def fixtures():
    genuine, authored, positives, controls = NATIVE["fixtures"]()
    pins = json.loads((PREVIOUS_DIR / "fixtures.json").read_text(encoding="utf-8"))
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    assert fingerprints(genuine) == pins["genuine_parquet"]
    assert fingerprints(authored) == pins["authored_parquet"]

    schema, groups, wire = positives["native_1111"]
    empty_group = physical_empty(wire)
    schema_only = write(schema, [])
    renamed_case = renamed()
    at, header, start, body = NATIVE["frames_in"](wire, 1, 1)[0]
    checksum = header[4][1] & 0xffffffff
    assert checksum == zlib.crc32(body) and body
    changed_body = body[:-1] + bytes([body[-1] ^ 1])
    late_crc = wire[:start] + changed_body + wire[start + len(body):]
    crc_error = (f".chunk (.page {NATIVE['address'](1, 1)} 0 {at} ⟨0, 0, 0⟩ "
                 f"(.checksum (.mismatch {checksum} {zlib.crc32(changed_body)})))")

    additional = {"physical_empty": empty_group, "schema_only": schema_only,
                  "renamed": renamed_case[2], "late_crc": late_crc, "empty_input": b""}
    positives |= {"physical_empty": (schema, [groups[0], [], groups[1]], empty_group),
                  "schema_only": (schema, [], schema_only), "renamed": renamed_case}
    files = genuine | authored | additional
    failures = [(label, group, wanted) for label, group, wanted, _ in controls]
    failures.append(("late_crc", 1, crc_error))
    new_pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert fingerprints(additional) == new_pins
    return files, positives, failures


def inspect_positive(label, schema, values, original):
    batches = pyarrow_groups(original, schema, values)
    if label != "renamed":
        _, chunks = inspect(original, schema, values)
        return batches, sum(len(frames) for _, frames in chunks.values())

    pages = 0
    for (group, side), footer, lo, hi in NATIVE["V2"]["columns"](original):
        path = [part.decode() for part in NATIVE["THRIFT"]["list_field"](footer, 3)]
        assert group == 0 and path == ["samples", "list", "segment", "list", "point", ("west", "east")[side]]
        pages += len(list(NATIVE["FRAMES"](original, lo, hi)))
    return batches, pages


def verify(folder):
    files, positives, failures = fixtures()
    for label, original in files.items():
        (folder / f"{label}.parquet").write_bytes(original)

    code = [LEAN]
    pages = 0
    for label, (decl, values, original) in positives.items():
        batches, inspected = inspect_positive(label, decl, values, original)
        pages += inspected
        code.append(f'  checkFile (← load folder "{label}") {fields_term(decl)} {batches_term(decl, batches)}')

    schema, groups, wire = positives["native_1111"]
    batches = pyarrow_groups(wire, schema, groups)
    for label, group, wanted in failures:
        code.append(f'  checkFile (← load folder "{label}") {fields_term(schema)} '
                    f'{batches_term(schema, batches[:group])} (.readError (.group {group} ({wanted})))')
    for label in ("empty_input", "optional_struct"):
        code.append(f'  checkOpenError (← load folder "{label}")')

    driver = folder / "TwoListStructEvents.lean"
    driver.write_text("\n".join(code) + "\n", encoding="utf-8")
    subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                    "--run", str(driver), str(folder)], cwd=ROOT, check=True)
    print(f"Checked {len(positives)} accepted inputs, {pages} original V1 pages "
          f"and {len(failures) + 2} typed refusals through direct, full and empty Events")


def main():
    assert platform.python_implementation() == "CPython"
    with tempfile.TemporaryDirectory() as directory:
        verify(Path(directory))


if __name__ == "__main__":
    main()
