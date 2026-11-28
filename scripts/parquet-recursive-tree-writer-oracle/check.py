"""Compare checked Tree writer output with PyArrow and original signed page bytes."""

import json
from pathlib import Path
import runpy
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
SCALAR = runpy.run_path(str(HERE.parent / "parquet-recursive-tree-scalar-oracle/check.py"))
NESTED = runpy.run_path(str(HERE.parent / "parquet-recursive-tree-leading-struct-oracle/check.py"))
EVENTS, JOIN, NATIVE, V2, lst = (SCALAR[key] for key in ("EVENTS", "JOIN", "NATIVE", "V2", "lst"))
field_term = EVENTS["EVENTS"]["field_term"]


LEAN = """
module

import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.Defs

open Silmaril.Formats Silmaril.Formats.Parquet
open RecursiveSchema.Tree
open Arrow.RecursiveSchema (Schema)
open Arrow.RecursiveSchema.Batch.Rows (Observation)

set_option maxRecDepth 8192

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def check (folder : System.FilePath) (label : String) (schema : Schema)
    (groups : List Observation) : IO Unit := do
  let output ← take (Writer.emit {} ⟨schema, groups, true⟩)
  let source ← take (openFile {} output.bytes)
  unless source.schema.arrow == schema && source.snapshot.groupCount == groups.length do
    throw (IO.userError "original schema or group count differs")
  for (group, ordinal) in groups.zipIdx do
    let result ← take (Rows.readGroupChecked source.schema {} ordinal)
    unless result.observation == group do throw (IO.userError "reopened group differs")
  IO.FS.writeBinFile (folder / (label ++ ".parquet")) output.bytes.data

private def refuse (limits : Writer.Limits) (input : Writer.Input) (wanted : Writer.Error) : IO Unit :=
  match Writer.emit limits input with
  | .error actual =>
    unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")
  | .ok _ => throw (IO.userError "expected typed writer refusal")

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected output directory")
"""


def schema_term(schema):
    return f"⟨{lst(map(field_term, schema))}⟩"


def observations(schema, groups):
    return lst(NATIVE["expected_observation"](schema, group) for group in groups)


def cases():
    scalar, rows, *_ = SCALAR["create"]()
    nested, lists, *_ = NESTED["create"]()
    return {
        "mixed": (scalar, [rows[0], [], rows[1]], SCALAR),
        "nested": (nested, lists, NESTED),
        "schema_only": (scalar, [], SCALAR),
    }


def inspect(wire, schema, groups, profile):
    assert wire[:4] == wire[-4:] == b"PAR1"
    original = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert original.schema_arrow.equals(schema, check_metadata=True)
    assert [original.read_row_group(i).to_pylist() for i in range(original.num_row_groups)] == groups
    assert original.metadata.num_rows == sum(map(len, groups))
    layout = profile["LAYOUT"]
    assert len(layout) == original.metadata.num_columns
    assert [(original.schema.column(i).path, original.schema.column(i).max_repetition_level,
             original.schema.column(i).max_definition_level) for i in range(len(layout))] == [
        (".".join(path), repeated, definitions) for path, repeated, definitions, _, _ in layout]
    inspected, page_counts = JOIN["inspect"](wire, profile["traces"](groups), layout)
    assert page_counts[3] == 0
    assert page_counts[0] == len(groups) * len(layout)
    offset = 4
    for group, rows in enumerate(groups):
        row_group = original.metadata.row_group(group)
        assert row_group.num_rows == len(rows)
        group_start = offset
        for side in range(len(layout)):
            (start, stop), pages, points = inspected[group, side]
            assert start == offset and len(pages) == 1
            assert all(page == 0 and at == start for page, at, *_ in points)
            column = row_group.column(side)
            assert column.compression == "UNCOMPRESSED" and column.dictionary_page_offset is None
            assert column.num_values == len(points) and column.data_page_offset == start
            assert column.total_compressed_size == column.total_uncompressed_size == stop - start
            offset = stop
        assert row_group.total_byte_size == offset - group_start
    assert offset == len(wire) - 8 - int.from_bytes(wire[-8:-4], "little")
    return page_counts[0]


def verify(folder):
    fixtures = cases()
    code = [LEAN]
    for label, (schema, groups, _) in fixtures.items():
        code.append(f'  check folder "{label}" {schema_term(schema)} {observations(schema, groups)}')

    schema, groups, profile = fixtures["mixed"]
    traces = profile["traces"](groups)
    first_slots = sum(len(traces[0, side]) for side in range(len(profile["LAYOUT"])))
    all_slots = sum(map(len, traces.values()))
    code.append(f"  let mixed : Writer.Input := ⟨{schema_term(schema)}, {observations(schema, groups)}, true⟩")
    code.extend([
        '  let word : Schema := ⟨[.node (some "word") false .int32 []]⟩',
        '  let one : Writer.Input := ⟨word, [⟨1, [[some (.int32 4)]]⟩], false⟩',
        '  refuse { maxGroups := 2 } mixed (.groupLimit 3)',
        '  refuse { maxTotalRows := 7 } mixed (.totalRowLimit 8)',
        '  refuse { maxColumns := 7 } mixed (.columnLimit 8)',
        '  refuse { chunk.maxRows := 0 } one (.rowLimit 0 1)',
        '  refuse { chunk.maxSlots := 1 } mixed (.slotLimit 0 0 4)',
        f'  refuse {{ maxGroupSlots := 1 }} mixed (.groupSlotLimit 0 {first_slots})',
        f'  refuse {{ maxTotalSlots := {first_slots} }} mixed (.totalSlotLimit 2 {all_slots})',
        '  refuse { chunk.maxBodyBytes := 0 } one (.page 0 0 (.bodyLimit 0))',
        '  refuse { chunk.maxChunkBytes := 3 } one (.page 0 0 (.bodyLimit 0))',
        '  refuse { chunk.framing.maxHeaderBytes := 0 } one (.page 0 0 (.headerLimit 0))',
        '  refuse { chunk.framing.maxPages := 0 } one (.page 0 0 (.pageLimit 0))',
        '  refuse { schema.maxFileBytes := 0 } one (.schema .fileLimit)',
        '  refuse { schema.snapshot.maxSchemaDepth := 1 } one (.schema (.depth []))',
        '  refuse {} ⟨⟨word.fields ++ word.fields⟩, [], false⟩ (.schema (.duplicate ["word"]))',
        '  refuse {} ⟨⟨[.node none false .int32 []]⟩, [], false⟩ (.schema (.missingName []))',
        '  refuse {} ⟨word, [⟨1, []⟩], false⟩ (.rowCount 0 1 0)',
        '  refuse {} ⟨word, [⟨1, [[none]]⟩], false⟩ (.projection 0)',
        '  refuse {} ⟨word, [⟨1, [[some (.int64 1)]]⟩], false⟩ (.projection 0)',
    ])
    V2["run_lean"](folder, "TreeWriter.lean", code)

    emitted, pages = {}, 0
    for label, (schema, groups, profile) in fixtures.items():
        wire = (folder / f"{label}.parquet").read_bytes()
        pages += inspect(wire, schema, groups, profile)
        emitted[label] = wire
    print(f"Checked {len(emitted)} Lean Parquet files, {pages} original V1 pages and 18 typed controls")
    return dict(producer=EVENTS["COMPILER"]["BASE"]["producer"](), emitted_parquet=NATIVE["fingerprints"](emitted))


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    with tempfile.TemporaryDirectory() as scratch:
        assert verify(Path(scratch)) == pins


if __name__ == "__main__":
    main()
