"""Check Lean's recursive Parquet row assembly and emitted Arrow IPC with PyArrow."""

from copy import deepcopy
from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MANIFEST = HERE / "fixtures.json"
CHUNK = runpy.run_path(str(HERE.parent / "parquet-recursive-chunk-oracle/check.py"))
ARROW = runpy.run_path(str(HERE.parent / "arrow-recursive-batch-writer-oracle/check.py"))
THRIFT, MIXED, describe, pack, fingerprints, path_term, location_term = (
    CHUNK[key] for key in ("THRIFT", "MIXED", "describe", "pack", "fingerprints", "path_term", "location_term")
)

LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.Rows.ToIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Rows.ToIpc.Defs

open Silmaril Silmaril.Formats
open Parquet.RecursiveSchema (openFile bindChunk)
open Parquet.RecursiveSchema.Rows (Error readGroup readAll)
open Parquet.RecursiveSchema.Rows.ToIpc (convert)

private def takeResult {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def refuse {ε α : Type} [Repr ε] [DecidableEq ε] (wanted : ε)
    (result : Except ε α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"accepted input expected to fail with {repr wanted}")
  | .error actual =>
    unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")

private def load (folder : System.FilePath) (name : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (name ++ ".parquet"))⟩

private def emit (folder : System.FilePath) (name : String) : IO Unit := do
  let source ← takeResult (openFile {} (← load folder name))
  let bytes ← takeResult (convert {} {} source.schema)
  IO.FS.writeBinFile (folder / (name ++ ".arrow")) bytes.toByteArray

private def inconsistent (file : Bytes) (priorRows badGroup badRows : Nat) (wanted : Error) :
    IO Unit := do
  let source ← takeResult (openFile {} file)
  let previous ← takeResult (readGroup {} source.schema 0)
  unless previous.rowCount = priorRows do throw (IO.userError "earlier group changed")
  for column in List.range source.schema.leaves.size do
    let bound ← takeResult (bindChunk source.schema badGroup column)
    let decoded ← takeResult (Parquet.RecursiveSchema.Chunk.read {} bound)
    unless decoded.rows.length = badRows do throw (IO.userError "a sibling chunk was invalid")
  refuse wanted (readGroup {} source.schema badGroup)
  refuse wanted (readAll {} source.schema)
  refuse (.source wanted) (convert {} { schema.ipc := { fields := 0, batches := 0 } } source.schema)
"""


def explicit_empty(wire, schema):
    footer = MIXED["metadata"](wire)
    groups = THRIFT["list_field"](footer, 4)
    leaves = describe(schema, footer)[1]
    empty = deepcopy(groups[0])
    count, = struct.unpack_from("<I", wire, len(wire) - 8)
    prefix = wire[:-8-count]
    payload = bytearray()
    for chunk, (_, _, optional) in zip(THRIFT["list_field"](empty, 1), leaves, strict=True):
        body = b"\0" * 4 if optional else b""
        header = THRIFT["encode"]({
            1: (TType.I32, 0), 2: (TType.I32, len(body)), 3: (TType.I32, len(body)),
            5: (TType.STRUCT, {i: (TType.I32, value)
                              for i, value in enumerate((0, 0, 3, 3), 1)}),
        })
        offset = len(prefix) + len(payload)
        payload.extend(header + body)
        chunk[2] = TType.I64, offset
        column = chunk[3][1]
        column[2] = TType.LIST, (TType.I32, [0, 3])
        column[5] = TType.I64, 0
        column[6] = column[7] = TType.I64, len(header) + len(body)
        column[9] = TType.I64, offset
        column.pop(12, None)
    empty[2] = TType.I64, len(payload)
    empty[3] = TType.I64, 0
    if 5 in empty:
        empty[5] = TType.I64, len(prefix)
    if 6 in empty:
        empty[6] = TType.I64, len(payload)
    groups.insert(1, empty)
    for ordinal, row_group in enumerate(groups):
        if 7 in row_group:
            row_group[7] = row_group[7][0], ordinal
    encoded = THRIFT["encode"](footer)
    return prefix + payload + encoded + struct.pack("<I", len(encoded)) + b"PAR1"


def fixtures():
    chunks, _ = CHUNK["fixtures"]()
    positives = {name: (schema, rows, wire) for name, (schema, rows, wire, _) in chunks.items()}
    schema, rows, wire = positives["deep"]
    empty = (schema, [rows[0], [], rows[1]], explicit_empty(wire, schema))

    schema, rows, wire, crc = chunks["multipage"]
    columns = list(CHUNK["capture"](wire, schema, rows, crc))
    sibling = [column for column in columns if column.group == 1 and column.path[0] == "packet"]
    assert len({tuple(page.row for page in column.pages) for column in sibling}) > 1
    first, conflict = sibling[:2]
    assert (first.index, conflict.index) == (0, 1)

    edits = {}
    for label, level in (("late_outer_disagreement", 0), ("late_inner_disagreement", 1)):
        page, index = CHUNK["level_target"](conflict, lambda value: value == level)
        assert level + 1 < len(conflict.steps)
        edits[label] = CHUNK["replace_level"](wire, conflict, page, index, level+1), page.row + index, (
            conflict.steps[level], first, conflict, len(rows[0]), len(rows[1])
        )

    footer = MIXED["metadata"](wire)
    columns = THRIFT["list_field"](THRIFT["list_field"](footer, 4)[1], 1)
    columns.append(deepcopy(columns[0]))
    return positives, empty, edits, pack(wire, footer)


def compare(positives, empty, edits, extra):
    emitted = {**positives, "explicit_empty": empty}
    code = [LEAN, "public def main (args : List String) : IO Unit := do",
            '  let [folder] := args | throw (IO.userError "expected fixture folder")']
    code.extend(f'  emit folder "{label}"' for label in emitted)
    for label, (_, row, info) in edits.items():
        site, first, conflict, prior_count, bad_count = info
        fix = f"⟨{first.index}, {path_term(first.path)}⟩"
        wrong = f"⟨{conflict.index}, {path_term(conflict.path)}⟩"
        error = f".sibling {first.group} {row} {location_term(site)} {fix} {wrong}"
        code.append(f'  inconsistent (← load folder "{label}") {prior_count} {first.group} {bad_count} ({error})')
        print(f"{label}: original row {row}, ancestor {site[1]}, columns {first.index} and {conflict.index}")
    code.extend([
        '  refuse (.snapshot (.invalidMetadata .columns)) (openFile {} (← load folder "extra_original"))',
        '  let source ← takeResult (openFile {} (← load folder "deep"))',
        '  refuse (.groupOrdinal 2) (readGroup {} source.schema 2)',
        '  refuse (.columnLimit 0 5) (readGroup { maxColumns := 4 } source.schema 0)',
        '  refuse (.rowLimit 0 5) (readGroup { chunk.maxRows := 4 } source.schema 0)',
        '  refuse (.slotLimit 0 5 5) (readGroup { maxSlots := 24 } source.schema 0)',
        '  refuse (.writer (.batchLimit 2 0)) (convert {} { schema.ipc.batches := 0 } source.schema)',
        '  IO.println "Checked sibling agreement, exact original width, resource limits and source error precedence"',
    ])
    output = {}
    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        inputs = {name: item[2] for name, item in emitted.items()} | {name: item[0] for name, item in edits.items()}
        inputs["extra_original"] = extra
        for label, wire in inputs.items():
            (scratch / f"{label}.parquet").write_bytes(wire)
        driver = scratch / "Check.lean"
        driver.write_text("\n".join(code) + "\n", encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        "--run", str(driver), directory], cwd=ROOT, check=True)
        for label, (schema, groups, source) in emitted.items():
            parquet = pq.ParquetFile(pa.BufferReader(source))
            assert parquet.schema_arrow.equals(schema) and parquet.num_row_groups == len(groups)
            native = (scratch / f"{label}.arrow").read_bytes()
            reader = pa.ipc.open_stream(native)
            assert reader.schema.equals(schema)
            _, cursor = ARROW["raw_schema"](native)
            for ordinal, (batch, rows) in enumerate(zip(reader, groups, strict=True)):
                expected = parquet.read_row_group(ordinal).to_pylist()
                frame = ARROW["read_record"](native, cursor)
                assert frame.rows == batch.num_rows == len(rows)
                assert batch.to_pylist() == expected == rows
                cursor = frame.end
            assert native[cursor:] == ARROW["eos"]
            output[label] = native
            print(f"{label}: ordered recursive IPC batches {[len(group) for group in groups]} through EOS")
    return fingerprints(output)


def main():
    pins = json.loads(MANIFEST.read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython" and platform.python_version() == pins["producer"]["cpython"]
    assert pa.__version__ == pins["producer"]["pyarrow"] and version("thrift") == pins["producer"]["thrift"]
    positives, empty, edits, extra = fixtures()
    assert fingerprints({label: data[2] for label, data in positives.items()}) == pins["genuine_parquet"]
    edits_raw = {label: data[0] for label, data in edits.items()}
    edits_raw.update(explicit_empty=empty[2], extra_original=extra)
    assert fingerprints(edits_raw) == pins["labeled_parquet"]
    assert compare(positives, empty, edits, extra) == pins["lean_ipc"]


if __name__ == "__main__":
    main()
