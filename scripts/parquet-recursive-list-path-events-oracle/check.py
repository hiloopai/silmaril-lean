"""Compare native LIST-path Events and projections with pinned original Parquet."""

from copy import deepcopy
from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import tempfile
import zlib

import pyarrow as pa
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
NATIVE = runpy.run_path(str(HERE.parent / "parquet-recursive-list-path-v1-oracle/check.py"))
TWO = NATIVE["TWO"]
capture, fingerprint, lst = (NATIVE[k] for k in ("capture", "fingerprints", "lst"))
rows = NATIVE["CORE"]["ROWS"]

LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.Defs

open Silmaril.Formats
open Silmaril.Formats.Arrow.RecursiveSchema (Field)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events (declarations eraseBatch eraseRow)
open Parquet.Reader.Recursive (Selection)
open Parquet.RecursiveSchema.ListPath.Reader.Events

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"unexpected refusal: {repr cause}")

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def check (result : EventStream) (fields : List (Option String × Field))
    (batches : List Observation) (ending : Arrow.Events.Termination Error) : IO Unit := do
  let ⟨source, trace⟩ ← take result
  unless declarations source == fields do throw (IO.userError "original declaration differs")
  unless trace.batches.map eraseBatch == batches do throw (IO.userError "complete batch or count differs")
  unless trace.collect.table.rows.map eraseRow == batches.flatMap (·.rows) do
    throw (IO.userError "collected original rows differ")
  unless trace.termination = ending do
    throw (IO.userError "terminal outcome differs")

private def checkFile (input : Bytes) (depth : Nat) (fields : List (Option String × Field))
    (batches : List Observation) (ending : Arrow.Events.Termination Error := .eos) : IO Unit := do
  let cap : Parquet.Snapshot.Limits := { maxSchemaDepth := 2 * depth + 2 }
  check (read cap {} input) fields batches ending
  check (readProjected cap {} input .field) fields batches ending
  let empty := batches.map fun batch => { batch with rows := List.replicate batch.rowCount [] }
  check (readProjected cap {} input .empty) [] empty ending

private def checkReframe (original edited : Bytes) : IO Unit := do
  for selection in [Selection.field, .empty] do
    let ⟨before, left⟩ ← take (readProjected {} {} original selection)
    let ⟨after, right⟩ ← take (readProjected {} {} edited selection)
    unless declarations before == declarations after && left.batches.map eraseBatch == right.batches.map eraseBatch &&
        left.collect.table.rows.map eraseRow == right.collect.table.rows.map eraseRow &&
        left.termination = .eos && right.termination = .eos do
      throw (IO.userError "reframe changed the complete event observation")

private def checkOpenError (input : Bytes) : IO Unit := do
  let .error cause := Parquet.RecursiveSchema.ListPath.openFile {} input |
    throw (IO.userError "expected original open error")
  for result in [read {} {} input, readProjected {} {} input .field, readProjected {} {} input .empty] do
    let .error error := result | throw (IO.userError "open error emitted a schema")
    unless error = .openError cause do throw (IO.userError "changed original open error")

set_option maxRecDepth 8192
"""


def empty_group(wire, width):
    footer = NATIVE["metadata"](wire)
    groups = NATIVE["list_field"](footer, 4)
    zero = deepcopy(groups[0])
    zero[3] = TType.I64, 0
    groups.insert(1, zero)
    column = TWO["THRIFT"]["column_metadata"](footer, 1, 0)
    column[5] = TType.I64, 0
    original = TWO["raw_chunks"](wire)
    page = TWO["frame"](original[0, 0][0], [], width)
    return TWO["repack"](wire, {(0, 0): original[0, 0], (1, 0): [page], (2, 0): original[1, 0]}, footer=footer)


def declarations(schema):
    return lst(f"(some {json.dumps(field.name)}, {rows['field_term'](field)})" for field in schema)


def batch_terms(groups, width):
    return lst(rows["batch_term"](group, width) for group in groups)


def verify(folder):
    generated, controls, _, all_cases, _ = NATIVE["fixtures"]()
    genuine = {}
    for label in ("signed_32_depth_3_15", "signed_64_depth_3_0", "signed_32_depth_4_10",
                  "signed_64_depth_6_85", "signed_32_depth_16_131071", "schema_only", "crc_absent"):
        genuine[label] = generated[label]
    authored = {label: controls[label] for label in ("deep_reframed", "late_crc", "late_words")}
    authored["empty_input"] = b""
    source = "signed_32_depth_3_15"
    schema, nullable, width, groups = all_cases[source]
    authored["empty_group"] = empty_group(genuine[source], width)
    positive = {name: all_cases[name] for name in (*genuine, "deep_reframed")}
    positive["empty_group"] = schema, nullable, width, [groups[0], [], groups[1]]

    files = genuine | authored
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)

    code = [LEAN, *NATIVE["V1"]["ENTRY"]]
    pages = 0
    for label, (decl, optional, signed, values) in positive.items():
        manifest = capture(files[label], decl, optional, signed, values)
        pages += sum(len(original) for _, _, _, original in manifest)
        depth = len(optional) - 1
        code.append(f'  checkFile (← load folder "{label}") {depth} '
                    f'{declarations(decl)} {batch_terms(values, signed)}')

    zero = capture(authored["empty_group"], *positive["empty_group"])[1]
    assert zero[0] < zero[1] and zero[2] == (0, 0, 0)
    assert len(zero[-1]) == 1 and zero[-1][0][-1] == []
    base = capture(authored["deep_reframed"], *positive["deep_reframed"])[1][-1]
    assert [page[-1][0][0] if page[-1] else None for page in base] == [0, 1, 2, 3, None]
    code.append(f'  checkReframe (← load folder "{source}") (← load folder "deep_reframed")')

    address = "⟨1, 0, " + json.dumps(["chain"] + ["list", "element"] * 3) + "⟩"
    for label in ("late_crc", "late_words"):
        wire = authored[label]
        at, header, _, body = list(NATIVE["FRAMES"](wire, *NATIVE["chunk"](wire)))[3]
        if label == "late_crc":
            declared = header[4][1] & 0xffffffff
            computed = zlib.crc32(body)
            assert declared != computed
            cause = f".checksum (.mismatch {declared} {computed})"
        else:
            assert header[4][1] & 0xffffffff == zlib.crc32(body)
            assert len(body) == base[3][3] + 1
            cause = ".plain .trailingBytes"
        state = NATIVE["triple"](base[3][-3])
        ending = f".readError (.group 1 (.chunk (.page {address} 3 {at} {state} ({cause}))))"
        code.append(f'  checkFile (← load folder "{label}") 3 {declarations(schema)} '
                    f'{batch_terms(groups[:1], width)} ({ending})')
    code.append('  checkOpenError (← load folder "empty_input")')
    NATIVE["V2"]["run_lean"](folder, "ListPathEvents.lean", code)
    print(f"Checked {len(positive)} native sources, {pages} original pages, the empty group, "
          "both projections, one equivalent reframe and three failure cases")
    return {"genuine_parquet": fingerprint(genuine), "authored_controls": fingerprint(authored)}


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
