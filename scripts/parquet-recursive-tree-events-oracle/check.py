"""Check native Arrow Events and ordered views of independently read Parquet groups."""

from copy import deepcopy
import json
from pathlib import Path
import runpy
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
JOIN = runpy.run_path(str(HERE.parent / "parquet-recursive-tree-rows-oracle/check.py"))
COMPILER, NATIVE, V2, THRIFT, lst = (JOIN[key] for key in ("COMPILER", "NATIVE", "V2", "THRIFT", "lst"))
EVENTS = COMPILER["EVENTS"]


LEAN = """
module

import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.Defs

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Relational
open RecursiveSchema.Tree
open Arrow.RecursiveSchema (Field)
open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch)

set_option maxRecDepth 8192

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private inductive View where
  | direct | full | reverse | first | empty
  deriving Repr

private def View.columns (view : View) (source : Signature) : Scan.Projection source :=
  match view with
  | .direct | .full => .id source
  | .reverse => .ofArray (List.finRange source.width).reverse.toArray
  | .first => .ofArray ((List.finRange source.width).take 1).toArray
  | .empty => .ofArray #[]

private def View.read (view : View) (input : Bytes) : Rows.Events.EventStream :=
  match view with
  | .direct => Rows.Events.read {} {} input
  | _ => Rows.Events.readProjected {} {} input view.columns

private def check (input : Bytes) (view : View) (fields : List (Option String × Field))
    (batches : List Observation) (terminal : Arrow.Events.Termination Rows.Events.Error) : IO Unit := do
  let ⟨source, trace⟩ ← take (view.read input)
  unless declarations source == fields && trace.batches.map eraseBatch == batches &&
      trace.batches.map (·.rowCount) == batches.map (·.rowCount) && decide (trace.termination = terminal) do
    throw (IO.userError s!"original fields, groups or termination differ for {repr view}")

private def refuseOpen (input : Bytes) (cause : RecursiveSchema.Repeated.Error) : IO Unit := do
  for view in [View.direct, .full, .reverse, .first, .empty] do
    match view.read input with
    | .error error => unless error = .openError cause do throw (IO.userError (reprStr error))
    | .ok _ => throw (IO.userError "expected the original open refusal")

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture directory")
"""


def renamed_branch():
    scalar = pa.field("counter", pa.int32())
    west = pa.field("west", pa.list_(pa.field("reading", pa.int64(), nullable=False)))
    east = pa.field("east", pa.list_(pa.field("entry", pa.int32())))
    clusters = pa.list_(pa.field("cluster", pa.struct([scalar, west, east])))
    ids = pa.list_(pa.field("tag", pa.int64()))
    schema = pa.schema([pa.field("clusters", clusters), pa.field("identifiers", ids, nullable=False)])
    all_null = {"counter": None, "west": None, "east": None}
    groups = [
        [{"clusters": None, "identifiers": []},
         {"clusters": [], "identifiers": [2, None, -2**63]},
         {"clusters": [None, all_null, {"counter": -2**31, "west": [], "east": [4, None, 8]}],
          "identifiers": [1]}],
        [{"clusters": [{"counter": 2**31 - 1, "west": [2**63 - 1, -2**63], "east": []}, all_null],
          "identifiers": [0, None, 12, 42]},
         {"clusters": [None], "identifiers": []}],
    ]
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, compression="NONE", use_dictionary=False, data_page_version="2.0",
                          store_schema=False, use_compliant_nested_type=False, write_page_checksum=True,
                          write_batch_size=1, max_rows_per_page=1) as writer:
        for group in groups:
            writer.write_table(pa.Table.from_pylist(group, schema=schema))
    return schema, groups, sink.getvalue().to_pybytes()


def zero_group(wire):
    footer = NATIVE["metadata"](wire)
    groups = THRIFT["list_field"](footer, 4)
    empty = deepcopy(groups[0])
    empty[3] = TType.I64, 0
    groups.insert(1, empty)
    raw = NATIVE["raw_chunks"](wire)
    chunks = {(0, side): raw[0, side] for side in range(len(JOIN["PATHS"]))}
    for side, width in enumerate(JOIN["WIDTHS"]):
        THRIFT["column_metadata"](footer, 1, side)[5] = TType.I64, 0
        chunks[1, side] = [NATIVE["frame"](raw[0, side][0], [], width)]
        chunks[2, side] = raw[1, side]
    return NATIVE["repack"](wire, chunks, footer)


def late_errors(authored, invalid, changed_slot):
    group, left, right = 1, 0, 1
    wire = authored["late_presence"]
    observed, _ = JOIN["inspect"](wire, invalid["late_presence"])
    wrapper = COMPILER["location"](2, COMPILER["WRAPPER"])
    node = COMPILER["location"](3, COMPILER["ELEMENT"])
    position = f"⟨0, [({wrapper}, 1)]⟩"
    b = next(i for i, value in enumerate(invalid["late_presence"][group, right]) if value[0] == 1)
    left_point = JOIN["point"](group, left, *observed[group, left][2][changed_slot][:3])
    right_point = JOIN["point"](group, right, *observed[group, right][2][b][:3])
    conflict = (f".group {group} (.join (.presence {position} {node} (.slot {left_point}) "
                f"(.slot {right_point}) .null .present))")

    # Add a payload error in the final leaf. Its original failure precedes
    # the existing topology disagreement, even under empty selection.
    side = 2
    (lo, hi), _, _ = observed[group, side]
    at, header, payload, body = next(JOIN["FRAMES"](wire, lo, hi))
    assert header[1][1] == 0 and body
    stored = header[4][1] & 0xffffffff
    changed = bytes([body[0] ^ 1]) + body[1:]
    actual = zlib.crc32(changed)
    assert actual != stored
    damaged = wire[:payload] + changed + wire[payload + len(body):]
    address = JOIN["address"](group, side, JOIN["BRANCH_LAYOUT"])
    crc = (f".group {group} (.input (.leaf {side} (.chunk "
           f"(.page {address} 0 {at} {{}} (.checksum (.mismatch {stored} {actual}))))))")
    return {"late_presence": (wire, conflict), "late_unselected_crc": (damaged, crc)}


def create():
    schema, genuine, authored, controls, positives, invalid, changed_slot = JOIN["create"]()
    multi_schema, multi_groups, _, _, multi_wire = JOIN["independent_roots"]()
    renamed_schema, renamed_groups, renamed_wire = renamed_branch()
    branch = {name: (schema, [[{"items": row} for row in group] for group in positives[name]], wire)
              for name, wire in genuine.items()}
    good = branch | {
        "independent_roots_v2": (multi_schema, multi_groups, multi_wire),
        "renamed_branch_v2": (renamed_schema, renamed_groups, renamed_wire),
        "schema_only": (schema, [], NATIVE["write"](schema, [])),
    }
    branch_schema, groups, wire = branch["branch_v1"]
    authored_good = {"physical_zero_group": (branch_schema, [groups[0], [], groups[1]], zero_group(wire))}
    bad = late_errors(authored, invalid, changed_slot)
    prefix = groups[:1]
    assert prefix == [[{"items": row} for row in positives["independent_mixed"][0]]]
    return good, authored_good, bad, controls["unsupported_double"], branch_schema, prefix


def append_views(lines, label, schema, groups, terminal):
    full = list(range(len(schema)))
    views = {"direct": full, "full": full, "reverse": full[::-1], "first": full[:1], "empty": []}
    for view, selected in views.items():
        selected_schema = pa.schema([schema[i] for i in selected])
        filled = EVENTS["fields_term"](selected_schema)
        observed = lst(NATIVE["expected_observation"](selected_schema, group) for group in groups)
        lines.append(f'  check (← load folder "{label}") .{view} {filled} {observed} ({terminal})')


def verify(folder, good, authored_good, bad, rejected, branch_schema, prefix):
    lines = [LEAN]
    total_groups = 0
    for label, (schema, expected, wire) in (good | authored_good).items():
        (folder / f"{label}.parquet").write_bytes(wire)
        original = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
        assert original.schema_arrow.equals(schema, check_metadata=True)
        groups = [original.read_row_group(i).to_pylist() for i in range(original.num_row_groups)]
        assert groups == expected
        total_groups += len(groups)
        append_views(lines, label, schema, groups, ".eos")

    for label, (wire, original_error) in bad.items():
        (folder / f"{label}.parquet").write_bytes(wire)
        original = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
        assert original.num_row_groups == 2 and original.read_row_group(0).to_pylist() == prefix[0]
        append_views(lines, label, branch_schema, prefix, f".readError ({original_error})")

    (folder / "unsupported_double.parquet").write_bytes(rejected)
    lines.extend([
        '  refuseOpen (← load folder "unsupported_double")',
        '    (.original (.physical ⟨4, ["items", "list", "element", "a"]⟩ .double))',
    ])
    V2["run_lean"](folder, "RecursiveTreeEvents.lean", lines)
    print(f"Checked {len(good) + len(authored_good)} accepted carriers, {total_groups} original groups and "
          "three typed refusals under five ordered views")


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert pins["producer"] == COMPILER["BASE"]["producer"]()
    good, authored_good, bad, rejected, schema, prefix = create()
    fingerprints = NATIVE["fingerprints"]
    assert pins["genuine_parquet"] == fingerprints(
        {label: case[-1] for label, case in good.items()} | {"unsupported_double": rejected})
    assert pins["authored_parquet"] == fingerprints(
        {label: case[-1] for label, case in authored_good.items()} | {label: case[0] for label, case in bad.items()})
    with tempfile.TemporaryDirectory() as scratch:
        verify(Path(scratch), good, authored_good, bad, rejected, schema, prefix)


if __name__ == "__main__":
    main()
