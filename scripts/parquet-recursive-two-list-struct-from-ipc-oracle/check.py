"""Verify genuine V5 IPC, native Lean Parquet, and selected strict round trips."""

import json
from pathlib import Path
import runpy
import struct
import subprocess
import tempfile

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WRITER = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-writer-oracle/check.py"))
FORWARD = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-to-ipc-oracle/check.py"))
BRIDGE = runpy.run_path(str(HERE.parent / "parquet-recursive-from-ipc-oracle/check.py"))
STREAM = BRIDGE["STREAM"]
SCHEMA = STREAM["SCHEMA"]
EOS = STREAM["EOS"]


LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Defs

open Silmaril Silmaril.Formats
open Parquet.RecursiveSchema.TwoListStruct
open Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc
open Parquet.Reader.Recursive (Selection)
open Arrow.RecursiveSchema hiding Limits Error
open Arrow.RecursiveSchema.Stream (Trace Completed)

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
    unless actual = wanted do throw (IO.userError s!"changed original schema error for {label}: {repr actual}")

private def expectTerminal (folder : System.FilePath) (label : String) (ipc : Batch.Limits) (wanted : Trace) : IO Unit := do
  let wire ← load folder label
  for limits in [({ ipc := ipc } : Limits), exhausted ipc] do
    let .error (.terminal actual) := convert limits wire true |
      throw (IO.userError s!"expected first original terminal failure for {label}")
    unless actual == wanted do throw (IO.userError s!"changed prefix, position or cause for {label}: {repr actual}")

private def expectDeclaration (folder : System.FilePath) (label : String) (wanted : Trace) : IO Unit := do
  let wire ← load folder label
  for limits in [({} : Limits), exhausted {}] do
    let .error (.declaration actual) := convert limits wire true |
      throw (IO.userError s!"expected a source declaration refusal for {label}")
    unless actual == wanted do throw (IO.userError s!"changed strict source trace for {label}")

private def expectWriter (folder : System.FilePath) (label : String) (limits : Limits) (wanted : Parquet.RecursiveSchema.TwoListStruct.Writer.Error) : IO Unit := do
  let .error (.writer actual) := convert limits (← load folder label) |
    throw (IO.userError s!"expected a target refusal for {label}")
  unless actual = wanted do throw (IO.userError s!"changed target error for {label}: {repr actual}")

private def roundTrip (folder : System.FilePath) (label : String) (checksum : Bool) (wanted : Trace) : IO Unit := do
  let wire ← load folder label
  let limits : Limits := { ipc.schema.ipc.batches := wanted.batches.length }
  let original ← take (Stream.read limits.ipc wire)
  unless original == wanted do throw (IO.userError s!"changed original trace for {label}")
  let output ← take (convert limits wire checksum)
  let file ← take (openFile {} output.bytes)
  let groups ← take (Reader.readAll {} file.schema)
  unless file.schema.plan.arrow == original.schema &&
      groups == original.batches.map Completed.observed && file.snapshot.groupCount == original.batches.length do
    throw (IO.userError s!"Parquet declaration, group count or rows differ for {label}")
  for (selection, suffix) in [(Selection.field, "field"), (.empty, "empty")] do
    let returned ← take (Reader.ToIpc.convert {} {} {} output.bytes selection)
    let again ← take (Stream.read {} returned)
    let .eos count cursor := again.terminal | throw (IO.userError "expected strict returned EOS")
    unless again.schema == selection.schema original.schema &&
        again.batches.map Completed.observed == groups.map selection.batch &&
        count == groups.length && cursor + 8 == returned.len do
      throw (IO.userError s!"changed selected observation or EOS for {label}")
    IO.FS.writeBinFile (folder / (label ++ "." ++ suffix ++ ".arrows")) returned.toByteArray
  IO.FS.writeBinFile (folder / (label ++ ".parquet")) output.bytes.data

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture directory")
  let directory := System.FilePath.mk folder
"""


def rows_for(schema, groups):
    name = schema.field(0).name
    return [[{name: row} for row in group] for group in groups]


def write_ipc(schema, groups):
    return BRIDGE["ipc"](schema, [pa.RecordBatch.from_pylist(group, schema=schema) for group in groups])


def absent_root_name(raw):
    data, _ = SCHEMA["metadata"](raw)

    def tables(start, count):
        for word in SCHEMA["words"](start, count):
            table = SCHEMA["target"](data, word)
            yield table
            yield from tables(*SCHEMA["vector"](data, table, 5))

    root, *descendants = tables(*SCHEMA["root_vector"](data))

    def vtable(table):
        return table - struct.unpack_from("<i", data, table)[0]

    assert all(vtable(root) != vtable(child) for child in descendants)
    assert SCHEMA["slot"](data, root, 0) is not None
    edited = bytearray(raw)
    struct.pack_into("<H", edited, 8 + vtable(root) + 4, 0)
    changed, _ = SCHEMA["metadata"](edited)
    assert SCHEMA["slot"](changed, root, 0) is None
    return bytes(edited)


def exact_trace(observed):
    count = len(observed[2])
    return BRIDGE["trace_term"](observed, count, f".eos {count} {observed[4]}")


def prepare_cases(positives, original_wire=None):
    genuine, observed, code = {}, {}, [LEAN]
    for label, schema, groups, crc in positives:
        logical = rows_for(schema, groups)
        wire = (original_wire or {}).get(label)
        if wire is None:
            wire = write_ipc(schema, logical)
        genuine[label] = wire
        FORWARD["inspect_ipc"](wire, schema, logical, canonical=False)
        original = observed[label] = STREAM["observe"](pa, wire)
        code.append(f'  roundTrip directory "{label}" {str(crc).lower()} {exact_trace(original)}')
    return genuine, observed, code


def run_cases(folder, files, positives, code):
    for label, wire in files.items():
        (folder / f"{label}.arrows").write_bytes(wire)
    driver = folder / "TwoListStructFromIpc.lean"
    driver.write_text("\n".join(code) + "\n", encoding="utf-8")
    subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                    "--run", str(driver), str(folder)], cwd=ROOT, check=True)

    parquet, returned = {}, {}
    for label, schema, groups, crc in positives:
        parquet[label] = (folder / f"{label}.parquet").read_bytes()
        WRITER["inspect"](parquet[label], schema, groups, crc)
        for selection, projected in (("field", schema), ("empty", pa.schema([]))):
            name = f"{label}.{selection}"
            wire = returned[name] = (folder / f"{name}.arrows").read_bytes()
            FORWARD["inspect_ipc"](wire, projected, rows_for(schema, groups))
    return parquet, returned


def verify(folder):
    common = "renamed_no_crc_empty_group"
    positives = []
    for label, schema, groups, crc in WRITER["cases"]():
        if label == common:
            groups = [groups[0], [], [None, groups[2][-1]]]
        positives.append((label, schema, groups, crc))

    genuine, observed, code = prepare_cases(positives)

    raw, original = genuine[common], observed[common]
    edits, bad_open = BRIDGE["edits_of"](raw, original)
    edits["second_eos"] = (raw + EOS, 3, original[4], ".trailingBytes")
    flat_schema = pa.schema([pa.field("value", pa.int32())])
    flat = write_ipc(flat_schema, [[{"value": -7}]])
    source_schema = next(schema for label, schema, _, _ in positives if label == "32_64_1000")
    outer = source_schema.field(0)
    controls = {
        "legacy": BRIDGE["ipc"](source_schema, [], legacy=True),
        "flat": flat,
        "zero_width": BRIDGE["ipc"](pa.schema([]), [
            pa.RecordBatch.from_struct_array(pa.array([{}, {}], type=pa.struct([]))),
        ]),
    }
    unnamed_model = observed["32_64_1000"]
    unnamed_schema_term, *rest = unnamed_model
    named = f".node (some {json.dumps(outer.name)}) "
    assert unnamed_schema_term.startswith(f"[{named}")
    unnamed_model = (unnamed_schema_term.replace(named, ".node none ", 1), *rest)
    authored = {label: data for label, (data, *_) in edits.items()} | bad_open | {
        "unnamed": absent_root_name(genuine["32_64_1000"]),
        "flat_trailing": flat + b"\0",
    }
    refused = [
        '  expectOpen directory "legacy" (.envelope (.unsupported .legacyFraming))',
        '  expectOpen directory "eos_without_schema" .expectedSchema',
        f'  expectDeclaration directory "unnamed" {exact_trace(unnamed_model)}',
        f'  expectWriter directory "{common}" (exhausted {{}}) (.groupLimit 3)',
        f'  expectWriter directory "{common}" {{ parquet.chunk.framing.maxPages := 0 }} (.column 0 .left (.pageLimit 0))',
        f'  expectWriter directory "{common}" {{ parquet.schema.snapshot.maxSchemaDepth := 6 }} (.schema (.depth []))',
        '  expectWriter directory "schema_only" { parquet.schema.maxFileBytes := 11 } (.schema .fileLimit)',
    ]
    for label in ("flat", "zero_width"):
        trace = exact_trace(STREAM["observe"](pa, controls[label]))
        refused.append(f'  expectDeclaration directory "{label}" {trace}')
    for label, (data, count, offset, cause) in edits.items():
        assert data[:offset] == raw[:offset]
        trace = BRIDGE["trace_term"](original, count, f".failed {count} {offset} ({cause})")
        refused.append(f'  expectTerminal directory "{label}" {{}} {trace}')
    capped = BRIDGE["trace_term"](original, 2, f".failed 2 {original[2][-1].start} .batchLimit")
    refused.append(f'  expectTerminal directory "{common}" {{ schema.ipc.batches := 2 }} {capped}')
    flat_wire = STREAM["observe"](pa, flat)
    flat_trace = BRIDGE["trace_term"](flat_wire, 1, f".failed 1 {flat_wire[4]} .trailingBytes")
    refused.append(f'  expectTerminal directory "flat_trailing" {{}} {flat_trace}')
    parquet, returned = run_cases(folder, genuine | controls | authored, positives, code + refused)
    pages = 2 * sum(len(groups) for _, _, groups, _ in positives)
    print(f"Checked {len(genuine)} genuine V5 streams, {pages} original Parquet pages, "
          f"{len(returned)} strict selected IPC returns and {len(refused)} typed controls")
    pins = WRITER["NATIVE"]["fingerprints"]
    return {kind: pins(wires) for kind, wires in {
        "genuine_ipc": genuine, "genuine_controls": controls, "authored_controls": authored,
        "lean_parquet": parquet, "returned_ipc": returned,
    }.items()}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert WRITER["producer"]() == pins["producer"]
    with tempfile.TemporaryDirectory() as directory:
        assert verify(Path(directory)) == {kind: values for kind, values in pins.items() if kind != "producer"}


if __name__ == "__main__":
    main()
