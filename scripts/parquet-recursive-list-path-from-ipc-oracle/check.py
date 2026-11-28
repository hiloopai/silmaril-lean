"""Check original PyArrow IPC, Lean LIST-path Parquet, and exact returned IPC."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import tempfile

import pyarrow as pa


HERE = Path(__file__).resolve().parent
WRITER = runpy.run_path(str(HERE.parent / "parquet-recursive-list-path-writer-oracle/check.py"))
BRIDGE = runpy.run_path(str(HERE.parent / "parquet-recursive-from-ipc-oracle/check.py"))
RAW = runpy.run_path(str(HERE.parent / "arrow-recursive-batch-writer-oracle/check.py"))
STREAM = BRIDGE["STREAM"]
EOS = STREAM["EOS"]


LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Defs

open Silmaril Silmaril.Formats
open Parquet.RecursiveSchema.ListPath
open Parquet.RecursiveSchema.ListPath.Writer.FromIpc
open Arrow.RecursiveSchema hiding Limits Error
open Arrow.RecursiveSchema.Stream (Trace Completed)
open Arrow.RecursiveSchema.Stream.Events (declarations eraseBatch)

set_option maxRecDepth 8192

private def load (folder : System.FilePath) (label : String) : IO KBytes := do
  let bytes ← IO.FS.readBinFile (folder / (label ++ ".arrows"))
  return KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"unexpected refusal: {repr cause}")

private def exhausted (ipc : Batch.Limits) : Limits :=
  { ipc := ipc, parquet.maxGroups := 0, parquet.schema.maxFileBytes := 0, parquet.chunk.maxBodyBytes := 0 }

private def expectOpen (folder : System.FilePath) (label : String) (wanted : Arrow.RecursiveSchema.Error) : IO Unit := do
  let wire ← load folder label
  for limits in [({} : Limits), exhausted {}] do
    let .error (.openError actual) := convert limits wire true |
      throw (IO.userError s!"expected original schema error for {label}")
    unless actual = wanted do throw (IO.userError s!"changed schema error for {label}: {repr actual}")

private def expectTerminal (folder : System.FilePath) (label : String) (ipc : Batch.Limits) (wanted : Trace) : IO Unit := do
  let wire ← load folder label
  for limits in [({ ipc := ipc } : Limits), exhausted ipc] do
    let .error (.terminal actual) := convert limits wire true |
      throw (IO.userError s!"expected the first original failure for {label}")
    unless actual == wanted do throw (IO.userError s!"changed prefix, address or cause for {label}: {repr actual}")

private def expectWriter (folder : System.FilePath) (label : String) (limits : Limits)
    (wanted : Parquet.RecursiveSchema.ListPath.Writer.Error) : IO Unit := do
  let .error (.writer actual) := convert limits (← load folder label) |
    throw (IO.userError s!"expected target refusal for {label}")
  unless actual = wanted do throw (IO.userError s!"changed target error for {label}: {repr actual}")

private def roundTrip (folder : System.FilePath) (label : String) (depth : Nat)
    (checksum : Bool) (wanted : Trace) : IO Unit := do
  let wire ← load folder label
  let limits : Limits :=
    { ipc.schema.ipc.batches := wanted.batches.length
      parquet.schema.snapshot.maxSchemaDepth := 2 * depth + 2 }
  let original ← take (Stream.read limits.ipc wire)
  unless original == wanted do throw (IO.userError s!"original trace differs for {label}")
  let output ← take (convert limits wire checksum)
  let cap := limits.parquet.schema.snapshot
  let file ← take (openFile cap output.bytes)
  let rows ← take (Reader.readAll limits.parquet.chunk file.schema)
  unless file.schema.plan.arrow == original.schema &&
      rows == original.batches.map Completed.observed && file.snapshot.groupCount == original.batches.length do
    throw (IO.userError s!"Parquet declaration or groups differ for {label}")
  let arrow ← take (Stream.Events.read limits.ipc wire)
  let parquet ← take (Reader.Events.read cap limits.parquet.chunk output.bytes)
  unless declarations arrow.1 == declarations parquet.1 &&
      arrow.2.batches.map eraseBatch == rows && parquet.2.batches.map eraseBatch == rows &&
      arrow.2.termination == .eos && parquet.2.termination == .eos do
    throw (IO.userError s!"direct Events differ for {label}")
  let returned ← take (Reader.ToIpc.convert cap limits.parquet.chunk {} output.bytes .field)
  let again ← take (Stream.read {} returned)
  unless again.schema == original.schema && again.batches.map Completed.observed == rows do
    throw (IO.userError s!"returned IPC observations differ for {label}")
  IO.FS.writeBinFile (folder / (label ++ ".parquet")) output.bytes.data
  IO.FS.writeBinFile (folder / (label ++ ".returned.arrows")) returned.toByteArray

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture folder")
  let directory := System.FilePath.mk folder
"""


def cases():
    for label, schema, nullable, width, groups, crc in WRITER["cases"]():
        if label == "empty_group_no_crc":
            # Three records including an empty one. Keep one visible null and one live row in the third.
            yield label, schema, nullable, width, [groups[0], [], [None, groups[-1][0]]], crc
        elif label == "schema_only":
            yield label, schema, nullable, width, groups, crc
        elif len(nullable) <= 4:
            if all(nullable) or not any(nullable):
                yield label, schema, nullable, width, groups, crc
        elif any(nullable) and not all(nullable):
            yield label, schema, nullable, width, groups, crc


def write_ipc(schema, groups):
    name = schema.field(0).name
    return BRIDGE["ipc"](schema, [
        pa.RecordBatch.from_pylist([{name: row} for row in group], schema=schema)
        for group in groups
    ])


def inspect_ipc(wire, schema, groups, *, canonical=False):
    reader = pa.ipc.open_stream(wire)
    assert reader.schema.equals(schema, check_metadata=True)
    fields, cursor = RAW["raw_schema"](wire)
    assert fields == [STREAM["SCHEMA"]["pyarrow_field"](pa, field) for field in schema]
    for group, batch in zip(groups, reader, strict=True):
        record = STREAM["read_record"](wire, cursor)
        assert record.rows == batch.num_rows == len(group)
        assert RAW["columns"](pa, batch) == [group]
        if canonical:
            RAW["check_record"](pa, schema, record, [group])
        cursor = record.end
    assert wire[cursor:] == EOS and cursor + 8 == len(wire)


def verify(folder):
    positives = list(cases())
    genuine, observed, commands = {}, {}, [LEAN]
    for label, schema, nullable, _, groups, crc in positives:
        wire = genuine[label] = write_ipc(schema, groups)
        inspect_ipc(wire, schema, groups)
        original = observed[label] = STREAM["observe"](pa, wire)
        trace = BRIDGE["trace_term"](original, len(groups), f".eos {len(groups)} {original[4]}")
        commands.append(f'  roundTrip directory "{label}" {len(nullable) - 1} {str(crc).lower()} {trace}')

    common = "empty_group_no_crc"
    raw, original = genuine[common], observed[common]
    edits, bad_open = BRIDGE["edits_of"](raw, original)
    end = original[4]
    edits["truncated_eos"] = (raw[:-1], 3, end, ".envelope (.malformed .truncated)")
    edits["second_eos"] = (raw + EOS, 3, end, ".trailingBytes")
    flat_schema = pa.schema([pa.field("word", pa.int32())])
    flat = write_ipc(flat_schema, [[-7]])
    wrapped_struct = pa.schema([pa.field("items", pa.list_(pa.struct([
        pa.field("x", pa.int32()), pa.field("y", pa.int64()),
    ])))])
    roots = pa.schema([pa.field("left", pa.list_(pa.int32())), pa.field("right", pa.list_(pa.int64()))])
    controls = {
        "legacy": BRIDGE["ipc"](positives[0][1], [], legacy=True),
        "flat": flat,
        "list_struct": write_ipc(wrapped_struct, [[[{"x": 7, "y": -8}]]]),
        "multiple_roots": BRIDGE["ipc"](roots, []),
        "zero_width": BRIDGE["ipc"](pa.schema([]), [
            pa.RecordBatch.from_struct_array(pa.array([{}, {}], type=pa.struct([]))),
        ]),
    }
    flat_wire = STREAM["observe"](pa, flat)
    authored = {label: data for label, (data, *_) in edits.items()} | bad_open | {"flat_trailing": flat + b"\0"}
    for label, wire in (genuine | controls | authored).items():
        (folder / f"{label}.arrows").write_bytes(wire)

    refusals = [
        '  expectOpen directory "legacy" (.envelope (.unsupported .legacyFraming))',
        '  expectOpen directory "eos_without_schema" .expectedSchema',
        f'  expectWriter directory "{common}" (exhausted {{}}) (.groupLimit 3)',
        f'  expectWriter directory "{common}" {{ parquet.chunk.framing.maxPages := 0 }} (.pageLimit 0)',
        '  expectWriter directory "schema_only" { parquet.schema.maxFileBytes := 11 } (.schema .fileLimit)',
    ]
    for shape in ("flat", "list_struct", "multiple_roots", "zero_width"):
        refusals.append(f'  expectWriter directory "{shape}" {{}} .declaration')
    for label, (data, count, cursor, cause) in edits.items():
        assert data[:cursor] == raw[:cursor]
        trace = BRIDGE["trace_term"](original, count, f".failed {count} {cursor} ({cause})")
        refusals.append(f'  expectTerminal directory "{label}" {{}} {trace}')
    late = original[2][-1].start
    batch_limit = BRIDGE["trace_term"](original, 2, f".failed 2 {late} .batchLimit")
    refusals.append(f'  expectTerminal directory "{common}" {{ schema.ipc.batches := 2 }} {batch_limit}')
    assert authored["flat_trailing"][:flat_wire[4]] == flat[:flat_wire[4]]
    flat_trace = BRIDGE["trace_term"](flat_wire, 1, f".failed 1 {flat_wire[4]} .trailingBytes")
    refusals.append(f'  expectTerminal directory "flat_trailing" {{}} {flat_trace}')
    WRITER["V2"]["run_lean"](folder, "ListPathFromIpc.lean", commands + refusals)

    parquet, returned = {}, {}
    for label, schema, nullable, width, groups, crc in positives:
        parquet[label] = (folder / f"{label}.parquet").read_bytes()
        WRITER["inspect"](parquet[label], schema, nullable, width, groups, crc)
        returned[label] = (folder / f"{label}.returned.arrows").read_bytes()
        inspect_ipc(returned[label], schema, groups, canonical=True)
    print(f"Checked {len(genuine)} genuine V5 streams, {sum(len(case[4]) for case in positives)} "
          f"native V1 pages, {len(returned)} returned strict streams, and {len(refusals)} typed controls")
    return {kind: WRITER["fingerprints"](wires) for kind, wires in {
        "genuine_ipc": genuine, "genuine_controls": controls, "authored_controls": authored,
        "lean_parquet": parquet, "returned_ipc": returned,
    }.items()}


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
