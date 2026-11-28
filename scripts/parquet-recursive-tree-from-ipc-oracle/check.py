"""Verify original PyArrow V5 traces and the exact signed groups emitted by Lean."""

import json
from pathlib import Path
import runpy
import tempfile

import pyarrow as pa


HERE = Path(__file__).resolve().parent
WRITER = runpy.run_path(str(HERE.parent / "parquet-recursive-tree-writer-oracle/check.py"))
BRIDGE = runpy.run_path(str(HERE.parent / "parquet-recursive-from-ipc-oracle/check.py"))
FORWARD = runpy.run_path(str(HERE.parent / "parquet-recursive-tree-to-ipc-oracle/check.py"))
STREAM = BRIDGE["STREAM"]
fingerprints = WRITER["NATIVE"]["fingerprints"]
lst, signed = WRITER["lst"], WRITER["JOIN"]["signed"]


LEAN = """
module

import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.Defs

open Silmaril Silmaril.Formats
open Parquet.RecursiveSchema.Tree
open Parquet.RecursiveSchema.Tree.Writer.FromIpc
open Parquet.RecursiveSchema.ListPath.Rows (Atom)
open Arrow.RecursiveSchema.Stream (Trace Completed)

set_option maxRecDepth 8192

private def load (folder : System.FilePath) (label : String) : IO KBytes := do
  let bytes ← IO.FS.readBinFile (folder / (label ++ ".arrows"))
  return KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError (reprStr cause))

private def exhausted (ipc : Arrow.RecursiveSchema.Batch.Limits) : Limits :=
  { ipc := ipc, parquet.maxGroups := 0, parquet.schema.maxFileBytes := 0, parquet.chunk.maxBodyBytes := 0 }

private def openFailure (folder : System.FilePath) (label : String)
    (wanted : Arrow.RecursiveSchema.Error) : IO Unit := do
  let source ← load folder label
  for limits in [({} : Limits), exhausted {}] do
    let .error (.openError actual) := convert limits source |
      throw (IO.userError s!"expected an original opening refusal for {label}")
    unless actual = wanted do throw (IO.userError s!"wrong opening cause for {label}: {repr actual}")

private def terminalFailure (folder : System.FilePath) (label : String)
    (ipc : Arrow.RecursiveSchema.Batch.Limits) (wanted : Trace) : IO Unit := do
  let source ← load folder label
  for limits in [({ ipc := ipc } : Limits), exhausted ipc] do
    let .error (.terminal actual) := convert limits source |
      throw (IO.userError s!"expected an original terminal refusal for {label}")
    unless actual == wanted do throw (IO.userError s!"wrong prefix, cause or offset for {label}: {repr actual}")

private def writerFailure (folder : System.FilePath) (label : String) (limits : Limits)
    (wanted : Writer.Error) : IO Unit := do
  let .error (.writer actual) := convert limits (← load folder label) true |
    throw (IO.userError s!"expected a typed target refusal for {label}")
  unless actual = wanted do throw (IO.userError s!"wrong target cause for {label}: {repr actual}")

private def check (folder : System.FilePath) (label : String) (wanted : Trace)
    (atoms : List (List (List Atom))) : IO Unit := do
  let source ← load folder label
  let limits : Limits := { ipc.schema.ipc.batches := wanted.batches.length }
  let original ← take (Arrow.RecursiveSchema.Stream.read limits.ipc source)
  unless original == wanted do throw (IO.userError s!"original IPC trace differs for {label}")
  let output ← take (convert limits source true)
  let reopened ← take (openFile {} output.bytes)
  unless reopened.schema.arrow == wanted.schema &&
      reopened.snapshot.groupCount == wanted.batches.length && atoms.length == wanted.batches.length do
    throw (IO.userError s!"original emitted declaration or group count differs for {label}")
  for ((batch, signed), ordinal) in (wanted.batches.zip atoms).zipIdx do
    let group ← take (Rows.readGroupChecked reopened.schema {} ordinal)
    unless group.observation == batch.observed && group.inputs.map (·.original.atoms) == signed do
      throw (IO.userError s!"native observation or original signed slots differ for {label}, group {ordinal}")
  IO.FS.writeBinFile (folder / (label ++ ".parquet")) output.bytes.data

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture directory")
"""


def exact_trace(observed):
    count = len(observed[2])
    return BRIDGE["trace_term"](observed, count, f".eos {count} {observed[4]}")


def failed_trace(observed, count, offset, cause):
    return BRIDGE["trace_term"](observed, count, f".failed {count} {offset} ({cause})")


def signed_groups(groups, profile):
    layout, traces = profile["LAYOUT"], profile["traces"](groups)
    return lst(lst(lst(f"⟨{rep}, {definition}, {signed(column[3], word)}⟩"
                       for rep, definition, word in traces[group, side])
                   for side, column in enumerate(layout))
               for group in range(len(groups)))


def ipc_of(schema, groups):
    return BRIDGE["ipc"](schema, [pa.RecordBatch.from_pylist(rows, schema=schema) for rows in groups])


def verify(folder):
    cases = WRITER["cases"]()
    schema, (first, empty, late), profile = cases["mixed"]
    cases["mixed"] = schema, [first[:3], empty, late[:2]], profile
    genuine, code, observed = {}, [LEAN], {}
    for label, (declared, groups, profile) in cases.items():
        wire = genuine[label] = ipc_of(declared, groups)
        FORWARD["IPC"]["inspect_ipc"](wire, declared, groups, canonical=False)
        original = observed[label] = STREAM["observe"](pa, wire)
        code.append(f'  check folder "{label}" {exact_trace(original)} {signed_groups(groups, profile)}')

    mixed = genuine["mixed"]
    original = observed["mixed"]
    edits, authored = BRIDGE["edits_of"](mixed, original)
    for label, (wire, count, offset, cause) in edits.items():
        authored[label] = wire
        code.append(f'  terminalFailure folder "{label}" {{}} {failed_trace(original, count, offset, cause)}')
    late_offset = original[2][-1].start
    limited = failed_trace(original, 2, late_offset, ".batchLimit")
    code.append(f'  terminalFailure folder "mixed" {{ schema.ipc.batches := 2 }} {limited}')

    empty_schema = pa.schema([])
    empty_groups = [[{}, {}], []]
    empty_decl = genuine["empty_decl"] = BRIDGE["ipc"](empty_schema, [
        pa.RecordBatch.from_struct_array(pa.array(rows, type=pa.struct([]))) for rows in empty_groups
    ])
    FORWARD["IPC"]["inspect_ipc"](empty_decl, empty_schema, empty_groups, canonical=False)
    empty_observation = STREAM["observe"](pa, empty_decl)
    authored["empty_decl_trailing"] = empty_decl + BRIDGE["EOS"]
    failed_empty = failed_trace(empty_observation, 2, empty_observation[4], ".trailingBytes")
    code.append(f'  terminalFailure folder "empty_decl_trailing" {{}} {failed_empty}')

    duplicate = pa.schema([pa.field("same", pa.int32()), pa.field("same", pa.int64())])
    genuine["duplicate_decl"] = BRIDGE["ipc"](duplicate, [])
    STREAM["observe"](pa, genuine["duplicate_decl"])
    genuine["legacy"] = BRIDGE["ipc"](schema, [], legacy=True)
    controls = [
        '  openFailure folder "legacy" (.envelope (.unsupported .legacyFraming))',
        '  openFailure folder "eos_without_schema" .expectedSchema',
        '  writerFailure folder "empty_decl" {} (.schema .emptyRoot)',
        '  writerFailure folder "duplicate_decl" {} (.schema (.duplicate ["same"]))',
        '  writerFailure folder "mixed" (exhausted {}) (.groupLimit 3)',
        '  writerFailure folder "mixed" { parquet.chunk.maxSlots := 2 } (.slotLimit 0 0 3)',
        '  writerFailure folder "mixed" { parquet.chunk.maxBodyBytes := 0 } (.page 0 0 (.bodyLimit 0))',
        '  writerFailure folder "schema_only" { parquet.schema.maxFileBytes := 11 } (.schema .fileLimit)',
    ]

    for label, wire in (genuine | authored).items():
        (folder / f"{label}.arrows").write_bytes(wire)
    WRITER["V2"]["run_lean"](folder, "TreeFromIpc.lean", code + controls)
    parquet, pages = {}, 0
    for label, (declared, groups, profile) in cases.items():
        parquet[label] = (folder / f"{label}.parquet").read_bytes()
        pages += WRITER["inspect"](parquet[label], declared, groups, profile)
    print(f"Checked {len(cases)} strict PyArrow sources and Lean Parquet outputs, {pages} V1 pages "
          f"and {len(edits) + 2 + len(controls)} typed controls")
    return {
        "producer": WRITER["EVENTS"]["COMPILER"]["BASE"]["producer"](),
        "genuine_ipc": fingerprints(genuine),
        "authored_ipc": fingerprints(authored),
        "emitted_parquet": fingerprints(parquet),
    }


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    with tempfile.TemporaryDirectory() as scratch:
        assert verify(Path(scratch)) == pins


if __name__ == "__main__":
    main()
