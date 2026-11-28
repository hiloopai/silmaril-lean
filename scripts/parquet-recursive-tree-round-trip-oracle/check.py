"""Compose both Tree bridges on independently produced, already pinned inputs."""

import json
from pathlib import Path
import runpy
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
FROM_DIR = HERE.parent / "parquet-recursive-tree-from-ipc-oracle"
FROM = runpy.run_path(str(FROM_DIR / "check.py"))
WRITER, FORWARD = FROM["WRITER"], FROM["FORWARD"]
EVENTS = FORWARD["EVENTS"]
JOIN = WRITER["JOIN"]


LEAN = """
module

import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Relational
open RecursiveSchema.Tree
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch)

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError (reprStr cause))

private def checkEos (wire : KBytes) : IO Unit := do
  let trace ← take (Arrow.RecursiveSchema.Stream.read {} wire)
  let .eos ordinal offset := trace.terminal | throw (IO.userError "expected exact EOS")
  unless ordinal = trace.batches.length ∧ offset + 8 = wire.len do
    throw (IO.userError "returned terminal count or extent differs")

private def views (source : Signature) (name : String) : Scan.Projection source :=
  let indices := List.finRange source.width
  match name with
  | "reverse" => .ofArray indices.reverse.toArray
  | "first" => .ofArray (indices.take 1).toArray
  | "duplicate" => .ofArray ((indices.take 1) ++ (indices.take 1)).toArray
  | "empty" => .ofArray #[]
  | _ => .id source

private def refuse (wire : KBytes) (wanted : Writer.Error) : IO Unit := do
  let .error (.writer actual) := Writer.FromIpc.convert {} wire |
    throw (IO.userError "expected target declaration refusal after strict EOS")
  unless actual = wanted do throw (IO.userError (reprStr actual))

private def roundIpc (folder : System.FilePath) (label : String) (selections : List String) : IO Unit := do
  let data ← IO.FS.readBinFile (folder / (label ++ ".ipc"))
  let original := KBytes.ofChunks 1 data.size (data.data.toList.map UInt8.toNat)
  let limits : Writer.FromIpc.Limits := {}
  let parquet ← take (Writer.FromIpc.convert limits original true)
  for view in selections do
    let returned ← take (Rows.Events.ToIpc.convert limits.parquet.schema.snapshot limits.parquet.reader
      {} parquet.bytes (fun source => views source view))
    checkEos returned
    let expected ← take (Arrow.RecursiveSchema.Stream.Events.readProjected {} original
      (fun source => views source view))
    let actual ← take (Arrow.RecursiveSchema.Stream.Events.read {} returned)
    unless declarations expected.1 == declarations actual.1 &&
        expected.2.batches.map eraseBatch == actual.2.batches.map eraseBatch &&
        decide (expected.2.termination = .eos ∧ actual.2.termination = .eos) do
      throw (IO.userError s!"IPC projection differs for {label}, {view}")
    if view = "empty" then refuse returned (.schema .emptyRoot)
    if view = "duplicate" then refuse returned (.schema (.duplicate ["identity"]))
    IO.FS.writeBinFile (folder / (label ++ "." ++ view ++ ".ipc")) returned.toByteArray

private def roundParquet (folder : System.FilePath) (label : String) : IO Unit := do
  let original : Bytes := ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩
  let schemaLimits : Snapshot.Limits := { maxSchemaDepth := 12 }
  let limits : Writer.FromIpc.Limits := {}
  let wire ← take (Rows.Events.ToIpc.convert schemaLimits {} limits.ipc original)
  checkEos wire
  let returned ← take (Writer.FromIpc.convert limits wire true)
  let before ← take (openFile schemaLimits original)
  let after ← take (openFile limits.parquet.schema.snapshot returned.bytes)
  unless before.schema.arrow == after.schema.arrow && before.snapshot.groupCount == after.snapshot.groupCount do
    throw (IO.userError "native declaration or explicit group count differs")
  for ordinal in List.range before.snapshot.groupCount do
    let first ← take (Rows.readGroupChecked before.schema {} ordinal)
    let second ← take (Rows.readGroupChecked after.schema limits.parquet.reader ordinal)
    unless first.observation == second.observation &&
        first.inputs.map (·.original.atoms) == second.inputs.map (·.original.atoms) do
      throw (IO.userError s!"native group observations or signed levels differ for {label}, {ordinal}")
  IO.FS.writeBinFile (folder / (label ++ ".returned.parquet")) returned.bytes.data

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture directory")
  roundIpc folder "mixed" ["full", "reverse", "first", "empty", "duplicate"]
  roundIpc folder "schema_only" ["full", "empty"]
  roundParquet folder "native_scalar_v2"
  roundParquet folder "native_schema_only"
  roundParquet folder "native_zero_group"
"""


def pins(path):
    return json.loads((path / "fixtures.json").read_text(encoding="utf-8"))


def check_pin(wire, fingerprint):
    assert FROM["fingerprints"]({"wire": wire})["wire"] == fingerprint


def ipc_inputs(folder):
    cases = WRITER["cases"]()
    schema, (first, empty, late), _ = cases["mixed"]
    inputs = {"mixed": (schema, [first[:3], empty, late[:2]]), "schema_only": cases["schema_only"][:2]}
    fixture_pins = pins(FROM_DIR)["genuine_ipc"]
    returned = {}
    for label, (schema, groups) in inputs.items():
        wire = FROM["ipc_of"](schema, groups)
        check_pin(wire, fixture_pins[label])
        (folder / f"{label}.ipc").write_bytes(wire)
        views = list(FORWARD["views"](schema)) + [("duplicate", pa.schema([schema[0], schema[0]]))]
        for view, selected in views:
            if label == "mixed" or view in ("full", "empty"):
                returned[f"{label}.{view}"] = selected, groups
    return returned


def native_inputs(folder):
    scalar = WRITER["SCALAR"]
    scalar_schema, scalar_groups, genuine, *_ = scalar["create"]()
    scalar_wire = genuine["scalar_v2"]
    scalar_pins = pins(HERE.parent / "parquet-recursive-tree-scalar-oracle")
    check_pin(scalar_wire, scalar_pins["genuine_parquet"]["scalar_v2"])

    genuine, authored, *_ = EVENTS["create"]()
    event_pins = pins(HERE.parent / "parquet-recursive-tree-events-oracle")
    only = genuine["schema_only"]
    zero = authored["physical_zero_group"]
    check_pin(only[-1], event_pins["genuine_parquet"]["schema_only"])
    check_pin(zero[-1], event_pins["authored_parquet"]["physical_zero_group"])

    def branch_traces(groups):
        return JOIN["trace_map"]([[row["items"] for row in group] for group in groups])

    branch = {"LAYOUT": JOIN["BRANCH_LAYOUT"], "traces": branch_traces}
    sources = {
        "native_scalar_v2": (scalar_schema, scalar_groups, scalar_wire, scalar),
        "native_schema_only": (*only, branch),
        "native_zero_group": (*zero, branch),
    }
    for label, (schema, groups, wire, _) in sources.items():
        (folder / f"{label}.parquet").write_bytes(wire)
        original = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
        assert original.schema_arrow.equals(schema, check_metadata=True)
        assert [original.read_row_group(i).to_pylist() for i in range(original.num_row_groups)] == groups
    return sources


def verify(folder):
    ipc, native = ipc_inputs(folder), native_inputs(folder)
    WRITER["V2"]["run_lean"](folder, "TreeRoundTrip.lean", [LEAN])
    for label, (schema, groups) in ipc.items():
        wire = (folder / f"{label}.ipc").read_bytes()
        FORWARD["IPC"]["inspect_ipc"](wire, schema, groups)
    pages = 0
    for label, (schema, groups, _, profile) in native.items():
        wire = (folder / f"{label}.returned.parquet").read_bytes()
        pages += WRITER["inspect"](wire, schema, groups, profile)
    print(f"Checked {len(ipc)} returned IPC streams and {len(native)} native round trips "
          f"with {pages} returned V1 pages and two target declaration refusals")


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as scratch:
        verify(Path(scratch))
