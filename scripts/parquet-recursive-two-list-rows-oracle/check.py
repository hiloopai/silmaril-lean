"""Compare checked two-LIST logical Arrow batches with PyArrow rows."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
TWO = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-oracle/check.py"))
V1, V2, FRAMES, PATH, fingerprints, lst = (TWO[k] for k in ("V1", "V2", "FRAMES", "PATH", "fingerprints", "lst"))
samples, schema_for, write, inspect = (TWO[k] for k in ("samples", "schema_for", "write", "inspect"))
raw_chunks, repack, frame = (TWO[k] for k in ("raw_chunks", "repack", "frame"))

LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Defs

open Silmaril.Formats (Bytes)
open Silmaril.Formats.Parquet
open RecursiveSchema.TwoList
open RecursiveSchema.TwoList.Rows
open Silmaril.Formats.Arrow.RecursiveSchema (Schema)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation)

private def take {ε α : Type} [Repr ε] (input : Except ε α) : IO α :=
  match input with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def deny {ε α : Type} [DecidableEq ε] [Repr ε] (wanted : ε) (input : Except ε α) : IO Unit :=
  match input with
  | .ok _ => throw (IO.userError s!"unexpected acceptance, expected {reprStr wanted}")
  | .error error =>
    unless error = wanted do throw (IO.userError s!"expected {reprStr wanted}, got {reprStr error}")

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def checkBatches (input : Bytes) (expected : Schema) (batches : List Observation) : IO Unit := do
  let source ← take (openFile {} input)
  unless arrowSchema source.schema.plan == expected do throw (IO.userError "original Arrow declaration differs")
  let logical ← take (readAll {} source.schema)
  unless logical == batches do throw (IO.userError "original group order, row count or nested values differ")

private def checkReframe (original reframed : Bytes) : IO Unit := do
  let first ← take (openFile {} original)
  let second ← take (openFile {} reframed)
  let firstBinding ← take (Chunk.bind first.schema 1)
  let secondBinding ← take (Chunk.bind second.schema 1)
  let before ← take (Chunk.read {} firstBinding)
  let after ← take (Chunk.read {} secondBinding)
  unless atoms before.pages = atoms after.pages do
    throw (IO.userError "reframing changed the original atom trace")
  let starts := after.pages.filterMap fun page => page.decoded.levels.head?.map (·.repetition)
  unless starts.contains 1 && starts.contains 2 do
    throw (IO.userError "reframe must have both continuation forms")
  let a ← take (readAll {} first.schema)
  let b ← take (readAll {} second.schema)
  unless a == b do throw (IO.userError "reframing changed the nested batches")

private def refuseGroup (input : Bytes) (limits : Chunk.Limits) (group : Nat) (wanted : Rows.Error) : IO Unit := do
  let source ← take (openFile {} input)
  deny wanted (readGroup limits source.schema group)

private def refuseTrace (input : Bytes) : IO Unit := do
  let source ← take (openFile {} input)
  let plan := source.schema.plan
  deny (.leadingContinuation 2) (reconstruct plan 1 [⟨2, plan.maxDefinition, some (.int32 7)⟩])
  deny (.leafShape 0) (reconstruct plan 1 [⟨0, plan.maxDefinition, none⟩])
  deny .projection (reconstruct plan 1 [⟨0, plan.maxDefinition, some (.int64 7)⟩])
  deny .projection (reconstruct plan 1
    [⟨0, plan.maxDefinition, some (.int32 7)⟩, ⟨3, plan.maxDefinition, some (.int32 8)⟩])
  deny (.rowCount 2 1) (reconstruct plan 2 [⟨0, plan.outerEmpty, none⟩])

set_option maxRecDepth 8192
"""


def field_term(field):
    if pa.types.is_list(field.type):
        kind = ".list"
        children = lst([field_term(field.type.value_field)])
    else:
        assert pa.types.is_int32(field.type) or pa.types.is_int64(field.type)
        kind = ".int32" if pa.types.is_int32(field.type) else ".int64"
        children = "[]"
    return f"(.node (some {json.dumps(field.name)}) {str(field.nullable).lower()} {kind} {children})"


def cell_term(value, width):
    if value is None:
        return "none"
    if isinstance(value, list):
        return f"(some (.list {lst(cell_term(item, width) for item in value)}))"
    assert isinstance(value, int)
    return f"(some (.int{width} ({value})))"


def batch_term(rows, width):
    return f"⟨{len(rows)}, {lst(lst([cell_term(row, width)]) for row in rows)}⟩"


def verify(scratch):
    genuine, labeled, declar, manifest = {}, {}, {}, {}
    for width in (32, 64):
        for bits in range(8):
            nullable = tuple(bool(bits & (1 << bit)) for bit in range(3))
            label = f"native_{width}_{bits}"
            rows = samples(nullable, width)
            schema = schema_for(nullable, width)
            genuine[label] = write(schema, rows)
            declar[label] = nullable, width, rows
            manifest[label] = list(inspect(genuine[label], nullable, width, rows))
    target = (1, 0)
    for width in (32, 64):
        label = f"native_{width}_7"
        original = genuine[label]
        carrier = raw_chunks(original)
        template = carrier[target][0]
        slots = [slot for page in manifest[label][1][-1] for slot in page[-1]]
        assert [(rep, definition) for rep, definition, _ in slots[:6]] == [
            (0, 1), (0, 5), (1, 2), (1, 3), (1, 4), (2, 5),
        ]
        cuts = [[slots[i]] for i in range(5)] + [slots[5:]]
        pages = [frame(template, section, width) for section in cuts]
        reframed = f"reframed_{width}"
        labeled[reframed] = repack(original, carrier | {target: pages})
        declar[reframed] = declar[label]
        manifest[reframed] = list(inspect(labeled[reframed], *declar[label]))
        assert [page[-1][0][0] for page in manifest[reframed][1][-1]] == [0, 0, 1, 1, 1, 2]
        if width == 32:
            pages[3] = frame(template, [(2, 5, 7)], width)
            labeled["stale_inner"] = repack(original, carrier | {target: pages})
    files = genuine | labeled
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)

    code = [LEAN, *V1["ENTRY"]]
    for label, (_, width, _) in declar.items():
        parquet = pq.ParquetFile(pa.BufferReader(files[label]), page_checksum_verification=True)
        fields = lst(field_term(field) for field in parquet.schema_arrow)
        rows = [parquet.read_row_group(group).column(0).to_pylist() for group in range(parquet.num_row_groups)]
        code.append(f'  checkBatches (← load folder "{label}") ⟨{fields}⟩ {lst(batch_term(group, width) for group in rows)}')
    for width in (32, 64):
        code.append(f'  checkReframe (← load folder "native_{width}_7") (← load folder "reframed_{width}")')
    lo, hi = next((start, stop) for key, _, start, stop in V2["columns"](labeled["stale_inner"]) if key == target)
    at = list(FRAMES(labeled["stale_inner"], lo, hi))[3][0]
    address = f"⟨1, 0, {json.dumps(PATH)}⟩"
    code.append(f'  refuseGroup (← load folder "stale_inner") {{}} 1 '
                f'(.chunk (.page {address} 3 {at} ⟨3, 2, .outer⟩ (.level (.closedAncestor 3 2 .outer))))')
    _, lo, hi, _, _ = manifest["native_32_7"][1]
    code.extend([
        f'  refuseGroup (← load folder "native_32_7") {{ maxSlots := 0 }} 1 '
        f'(.chunk (.chunk {address} ⟨{lo}, {hi}⟩ .slotLimit))',
        '  refuseGroup (← load folder "native_32_7") {} 2 (.binding (.group 2))',
        '  refuseTrace (← load folder "native_32_7")',
    ])
    V2["run_lean"](scratch, "Rows.lean", code)
    print("Checked 36 logical Arrow batches, all 16 width/nullability pairs, two split equivalents and eight refusals")
    return {"genuine": fingerprints(genuine), "labeled": fingerprints(labeled)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for name, fixtures in captured.items():
        assert fixtures == pins[name], f"{name} fixture pins changed"


if __name__ == "__main__":
    main()
