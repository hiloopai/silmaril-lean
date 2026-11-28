"""Check shared topology and original slots of two signed LIST-of-Struct leaves."""

from importlib.metadata import version
from itertools import product
import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ROWS = runpy.run_path(str(HERE.parent / "parquet-recursive-repeated-rows-oracle/check.py"))
TWO = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-oracle/check.py"))
CHUNK, ARROW, THRIFT, MIXED, pack, fingerprints, lst, path_term, position, conflict = (
    ROWS[key] for key in ("CHUNK", "ARROW", "THRIFT", "MIXED", "pack", "fingerprints",
                         "lst", "path_term", "position", "conflict")
)
FRAMES, frame, raw_chunks, repack = (TWO[key] for key in ("FRAMES", "frame", "raw_chunks", "repack"))
LIST = 1, ("items",)
ELEMENT = 3, ("items", "list", "element")
PATHS = [ELEMENT[1] + (child,) for child in ("lo", "hi")]

LEAN = ROWS["LEAN"].replace(
    "import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs",
    "import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Shared.Defs",
) + """
open Parquet.RecursiveSchema.Repeated.Chunk (Word)

private structure SlotView where
  point : Point
  repetition : Nat
  definition : Nat
  word : Option Word
  deriving DecidableEq

private def checkColumns (file : Bytes) (group ceiling : Nat)
    (expected : List (List (List SlotView))) : IO Unit := do
  let source ← take (openFile {} file)
  let [.list outer wrapper (.group element [.leaf left, .leaf right])] := source.schema.fields
    | throw (IO.userError "original LIST-of-Struct declaration differs")
  let shared := sharedSteps outer wrapper element
  unless shared.length = ceiling ∧ left.steps = shared ++ childSteps left.site ∧
      right.steps = shared ++ childSteps right.site do
    throw (IO.userError "compiled common or child definition steps differ")
  let columns ← take ([0, 1].mapM (readColumn {} source.schema group))
  let actual : List (List (List SlotView)) := columns.map fun column => column.rows.toList.map fun row => row.toList.map fun slot =>
    ⟨slot.point, slot.atom.levels.repetition, slot.atom.levels.definition, slot.atom.word⟩
  unless actual = expected do throw (IO.userError "original addressed level and word slots differ")
  let [left, right] := columns | throw (IO.userError "expected two original columns")
  let topology := fun column : Column =>
    column.rows.toList.map fun row => row.toList.map (commonLevels ceiling ∘ Addressed.atom)
  unless topology left = topology right do throw (IO.userError "common repetition or definition differs")

private def footerRefusal (file : Bytes) (wanted : Parquet.RecursiveSchema.Repeated.Error) : IO Unit :=
  refuse wanted (openFile {} file)
"""


def native(nullable):
    outer, element, left, right = nullable
    struct = pa.struct([pa.field("lo", pa.int32(), left), pa.field("hi", pa.int64(), right)])
    schema = pa.schema([pa.field("items", pa.list_(pa.field("element", struct, element)), outer)])

    def pair(lo, hi):
        return {"lo": lo, "hi": hi}

    values = ([None] if element else []) + [
        pair(None if left else -17, None if right else 2**40),
        pair(-2**31, None if right else -2**63),
        pair(None if left else 2**31-1, -2**63),
        pair(2**31-1, 2**63-1),
    ]
    groups = [
        [None, [], values] if outer else [[], values],
        [values + [pair(i, -2**40 - i) for i in range(9)], [pair(-7, 2**40 + 7), pair(1, -1)], []],
    ]
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, compression="NONE", use_dictionary=False,
                          data_page_version="1.0", write_page_checksum=True, write_page_index=False,
                          use_compliant_nested_type=True, store_schema=False, data_page_size=48,
                          max_rows_per_page=1, write_batch_size=1) as writer:
        for group in groups:
            writer.write_table(pa.Table.from_pylist([{"items": value} for value in group], schema=schema))
    return schema, groups, sink.getvalue().to_pybytes()


def capture(wire, schema, groups):
    tabular = [[{"items": row} for row in group] for group in groups]
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.equals(schema, check_metadata=True)
    assert [parquet.read_row_group(i).to_pylist() for i in range(parquet.num_row_groups)] == tabular
    return list(CHUNK["capture"](wire, schema, [row for group in tabular for row in group], checksummed=True))


def frames_in(wire, group, column):
    meta = THRIFT["column_metadata"](MIXED["metadata"](wire), group, column)
    return FRAMES(wire, *MIXED["column_extent"](meta))


def point_at(wire, group, column, slot):
    left = slot
    for page, (at, header, _, _) in enumerate(frames_in(wire, group, column)):
        count = header[5][1][1][1]
        if left < count:
            return f"⟨⟨{group}, {column}, {path_term(PATHS[column])}⟩, {page}, {at}, {slot}⟩"
        left -= count
    raise AssertionError("expected a physical slot at the mismatch")


def fixtures():
    original, authored, controls = {}, {}, []
    for flags in product((False, True), repeat=4):
        label = "native_" + "".join(str(int(flag)) for flag in flags)
        original[label] = native(flags)
    schema, groups, wire = original["native_1111"]
    columns = {(col.group, col.index): col for col in capture(wire, schema, groups)}
    chunks = raw_chunks(wire)

    def slots(group, column):
        return [slot for page in columns[group, column].pages for slot in page.events]

    def replace(carrier, group, column, trace, cuts):
        original_frame = chunks[group, column][0]
        segments = [frame(original_frame, trace[lo:hi], columns[group, column].width)
                    for lo, hi in zip([0, *cuts], [*cuts, len(trace)], strict=True)]
        return carrier | {(group, column): segments}

    carrier = chunks
    for column, cut in enumerate((2, 4)):
        trace = slots(1, column)
        assert trace[cut][0] == 1
        carrier = replace(carrier, 1, column, trace, [cut, len(groups[1][0])])
    authored["independent_continuations"] = repack(wire, carrier)
    edited = capture(authored["independent_continuations"], schema, groups)
    assert [col.pages[1].before[0] for col in edited if col.group == 1] == [2, 4]
    assert all(col.pages[1].events[0][0] == 1 for col in edited if col.group == 1)

    def mismatch(label, group, trace, wanted):
        # Retain distinct original cuts on the other column so the expected
        # coordinates are always computed from the edited carrier.
        authored[label] = repack(wire, replace(carrier, group, 1, trace, []))
        controls.append((label, group, wanted(authored[label])))

    def conflict_at(wire, group, row, slot, site, element=None):
        return conflict(position(group, row, element), site,
                        point_at(wire, group, 0, slot), point_at(wire, group, 1, slot))

    group0 = slots(0, 1)
    assert group0[0] == (0, 0, None)
    mismatch("outer_null_empty", 0, [(0, 1, None), *group0[1:]],
             lambda edited: conflict_at(edited, 0, 0, 0, LIST))

    group1 = slots(1, 1)
    assert group1[0] == (0, 2, None)
    absent = [(0, 3, None), *group1[1:]]
    first = len(groups[1][0])
    cut = 4

    def shorten(trace):
        assert trace[cut][0] == 1 and trace[first][0] == 0
        return [*trace[:cut], (0, *trace[cut][1:]), *trace[cut+1:first],
                (1, *trace[first][1:]), *trace[first+1:]]

    def element_conflict(edited):
        return conflict_at(edited, 1, 0, 0, ELEMENT, (LIST, 0))

    mismatch("null_struct_present_struct", 1, absent, element_conflict)
    mismatch("earlier_conflict_before_length", 1, shorten(absent), element_conflict)
    mismatch("short_sibling", 1, shorten(group1), lambda edited:
             f".missing {position(1, 0, (LIST, cut))} ⟨1, {path_term(LIST[1])}⟩ "
             f"⟨1, 1, {path_term(PATHS[1])}⟩ (some {point_at(edited, 1, 0, cut)})")

    footer = MIXED["metadata"](wire)
    row_group = THRIFT["list_field"](footer, 4)[1]
    THRIFT["list_field"](row_group, 1).reverse()
    authored["swapped_paths"] = pack(wire, footer)
    controls.append(("swapped_paths", None, ".original (.snapshot (.invalidMetadata .columns))"))
    return original, authored, controls


def addressed_rows(column):
    partition, expected = [], []
    for page in column.pages:
        for ordinal, (rep, definition, word) in enumerate(page.events, page.before[0]):
            if rep == 0:
                partition.append([])
                expected.append([])
            term = ROWS["point"](column, page, ordinal)
            value = "none" if word is None else f"some (.int{column.width} ({word}))"
            expected[-1].append(f"⟨{term}, {rep}, {definition}, {value}⟩")
            partition[-1].append((rep, definition))
    return partition, lst(lst(row) for row in expected)


def verify(folder):
    native, authored, controls = fixtures()
    positives = native | {"independent_continuations": (*native["native_1111"][:2],
                                                         authored["independent_continuations"])}
    files = {label: value[2] for label, value in native.items()} | authored
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)
    code = [LEAN, "public def main (args : List String) : IO Unit := do",
            '  let [folder] := args | throw (IO.userError "expected fixture folder")']
    schema_oracle = ARROW["BATCH"]["SCHEMA_ORACLE"]
    counted = 0
    for label, (schema, groups, wire) in positives.items():
        fields = schema_oracle["fields_term"]([schema_oracle["pyarrow_field"](pa, field) for field in schema])
        expected = lst(ROWS["expected_observation"](schema, [{"items": row} for row in group]) for group in groups)
        code.append(f'  check (← load folder "{label}") ⟨{fields}⟩ {expected}')
        columns = capture(wire, schema, groups)
        ceiling = 1 + int(schema.field(0).nullable) + int(schema.field(0).type.value_field.nullable)
        counted += sum(len(column.pages) for column in columns)
        for group in range(len(groups)):
            (left, lhs), (right, rhs) = [addressed_rows(col) for col in columns if col.group == group]
            clamp = lambda rows: [[(rep, min(level, ceiling)) for rep, level in row] for row in rows]
            assert clamp(left) == clamp(right)
            code.append(f'  checkColumns (← load folder "{label}") {group} {ceiling} {lst([lhs, rhs])}')
    for label, group, wanted in controls:
        if group is None:
            code.append(f'  footerRefusal (← load folder "{label}") ({wanted})')
        else:
            code.append(f'  inconsistent (← load folder "{label}") {group} ({wanted})')
    driver = folder / "ListStruct.lean"
    driver.write_text("\n".join(code) + "\n", encoding="utf-8")
    subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                    "--run", str(driver), str(folder)], cwd=ROOT, check=True)
    print(f"Checked {len(positives)} inputs, {counted} original V1 pages and {len(controls)} typed refusals")
    return {"genuine_parquet": fingerprints({label: value[2] for label, value in native.items()}),
            "authored_parquet": fingerprints(authored)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for category, fixtures in captured.items():
        assert fixtures == pins[category], f"{category} fixture pins changed"


if __name__ == "__main__":
    main()
