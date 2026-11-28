"""Check original PyArrow IPC, Lean two-LIST Parquet and returned IPC."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import tempfile

import pyarrow as pa


HERE = Path(__file__).resolve().parent
WRITER = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-writer-oracle/check.py"))
BRIDGE = runpy.run_path(str(HERE.parent / "parquet-recursive-from-ipc-oracle/check.py"))
STREAM = BRIDGE["STREAM"]
EOS = STREAM["EOS"]


LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.FromIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.FromIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Defs

open Silmaril Silmaril.Formats
open Parquet.RecursiveSchema.TwoList
open Parquet.RecursiveSchema.TwoList.Writer.FromIpc
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

private def expectOpen (folder : System.FilePath) (label : String)
    (wanted : Arrow.RecursiveSchema.Error) : IO Unit := do
  match convert (exhausted {}) (← load folder label) true with
  | .error (.openError actual) =>
    unless actual = wanted do throw (IO.userError s!"changed schema error for {label}: {repr actual}")
  | .error other => throw (IO.userError s!"wrong stage for {label}: {repr other}")
  | .ok _ => throw (IO.userError s!"unexpected Parquet for {label}")

private def expectTerminal (folder : System.FilePath) (label : String)
    (ipc : Batch.Limits) (wanted : Trace) : IO Unit := do
  match convert (exhausted ipc) (← load folder label) true with
  | .error (.terminal actual) =>
    unless actual == wanted do throw (IO.userError s!"changed original prefix or cause for {label}: {repr actual}")
  | .error other => throw (IO.userError s!"wrong stage for {label}: {repr other}")
  | .ok _ => throw (IO.userError s!"unexpected Parquet for {label}")

private def expectWriter (folder : System.FilePath) (label : String) (limits : Limits)
    (wanted : Parquet.RecursiveSchema.TwoList.Writer.Error) : IO Unit := do
  match convert limits (← load folder label) with
  | .error (.writer actual) =>
    unless actual = wanted do throw (IO.userError s!"changed target error for {label}: {repr actual}")
  | .error other => throw (IO.userError s!"wrong stage for {label}: {repr other}")
  | .ok _ => throw (IO.userError s!"unexpected Parquet for {label}")

private def roundTrip (folder : System.FilePath) (label : String) (checksum : Bool) (wanted : Trace) : IO Unit := do
  let wire ← load folder label
  let original ← take (Stream.read {} wire)
  unless original == wanted do throw (IO.userError s!"original trace differs for {label}")
  let output ← take (convert {} wire checksum)
  let file ← take (openFile {} output.bytes)
  let rows ← take (Rows.readAll {} file.schema)
  unless Rows.arrowSchema file.schema.plan == original.schema &&
      rows == original.batches.map Completed.observed && file.snapshot.groupCount == original.batches.length do
    throw (IO.userError s!"Parquet declarations or groups differ for {label}")
  let arrow ← take (Stream.Events.read {} wire)
  let parquet ← take (Rows.Events.read {} {} output.bytes)
  unless declarations arrow.1 == declarations parquet.1 &&
      arrow.2.batches.map eraseBatch == rows && parquet.2.batches.map eraseBatch == rows &&
      arrow.2.termination == .eos && parquet.2.termination == .eos do
    throw (IO.userError s!"direct Events differ for {label}")
  let returned ← take (Rows.ToIpc.convert {} {} {} output.bytes .field)
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
            groups = [groups[0][:3], [], [None, [[-(2**63), None], [], None]]]
        yield label, schema, nullable, width, groups, crc


def to_rows(schema, groups):
    name = schema.field(0).name
    return [[{name: row} for row in group] for group in groups]


def verify(folder):
    positives = list(cases())
    genuine, observations = {}, {}
    for label, schema, _, _, groups, _ in positives:
        rows = to_rows(schema, groups)
        wire = BRIDGE["ipc"](schema, [pa.RecordBatch.from_pylist(group, schema=schema) for group in rows])
        BRIDGE["check_returned"](wire, schema, rows)
        genuine[label] = wire
        observations[label] = STREAM["observe"](pa, wire)

    common_name = "empty_group_no_crc"
    common = observations[common_name]
    edits, bad_open = BRIDGE["edits_of"](genuine[common_name], common)
    raw, end = genuine[common_name], common[4]
    edits["truncated_eos"] = (raw[:-1], 3, end, ".envelope (.malformed .truncated)")
    edits["second_eos"] = (raw + EOS, 3, end, ".trailingBytes")
    labeled = {name: data for name, (data, *_) in edits.items()} | bad_open
    controls = {
        "legacy": BRIDGE["ipc"](positives[0][1], [], legacy=True),
        "one_list": BRIDGE["ipc"](pa.schema([pa.field("items", pa.list_(pa.int32()))]), []),
        "zero_width": BRIDGE["ipc"](pa.schema([]), [
            pa.RecordBatch.from_struct_array(pa.array([{}, {}], type=pa.struct([])))
        ]),
    }
    for label, wire in (genuine | labeled | controls).items():
        (folder / f"{label}.arrows").write_bytes(wire)

    code = [LEAN]
    for label, _, _, _, groups, crc in positives:
        native = observations[label]
        wanted = BRIDGE["trace_term"](native, len(groups), f".eos {len(groups)} {native[4]}")
        code.append(f'  roundTrip directory "{label}" {str(crc).lower()} {wanted}')

    refusals = [
        '  expectOpen directory "legacy" (.envelope (.unsupported .legacyFraming))',
        '  expectOpen directory "eos_without_schema" .expectedSchema',
        '  expectWriter directory "one_list" {} .declaration',
        '  expectWriter directory "zero_width" {} .declaration',
        f'  expectWriter directory "{common_name}" (exhausted {{}}) (.groupLimit 3)',
        f'  expectWriter directory "{common_name}" {{ parquet.chunk.framing.maxPages := 0 }} (.pageLimit 0)',
        '  expectWriter directory "schema_only" { parquet.schema.maxFileBytes := 11 } (.schema .fileLimit)',
    ]
    for label, (data, completed, offset, cause) in edits.items():
        assert data[:offset] == raw[:offset]
        wanted = BRIDGE["trace_term"](common, completed, f".failed {completed} {offset} ({cause})")
        refusals.append(f'  expectTerminal directory "{label}" {{}} {wanted}')
    late = common[2][-1].start
    batch_limit = BRIDGE["trace_term"](common, 2, f".failed 2 {late} .batchLimit")
    refusals.append(f'  expectTerminal directory "{common_name}" {{ schema.ipc.batches := 2 }} {batch_limit}')
    WRITER["V2"]["run_lean"](folder, "TwoListFromIpc.lean", code + refusals)

    parquet, returned = {}, {}
    for label, schema, nullable, width, groups, crc in positives:
        parquet[label] = (folder / f"{label}.parquet").read_bytes()
        WRITER["inspect"](parquet[label], schema, nullable, width, groups, crc)
        returned[label] = (folder / f"{label}.returned.arrows").read_bytes()
        BRIDGE["check_returned"](returned[label], schema, to_rows(schema, groups))
    print(f"Checked {len(positives)} genuine Arrow V5 streams, {sum(len(item[4]) for item in positives)} "
          f"native V1 pages, {len(returned)} returned IPC streams through exact EOS, and {len(refusals)} typed controls")
    return {kind: WRITER["fingerprints"](wires) for kind, wires in {
        "genuine_ipc": genuine, "genuine_controls": controls, "labeled_edits": labeled,
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
