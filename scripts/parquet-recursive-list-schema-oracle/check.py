"""Compare recursive Parquet LIST plans with PyArrow's original footer metadata."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREDECESSOR = runpy.run_path(str(HERE.parent / "parquet-recursive-schema-oracle/check.py"))
THRIFT, MIXED, pack, fingerprints, location_term, lst, string = (
    PREDECESSOR[key] for key in ("THRIFT", "MIXED", "pack", "fingerprints",
                                 "location_term", "lst", "string")
)

LEAN = """\
module
import Batteries.Data.Except

import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Defs

open Silmaril Silmaril.Formats
open Parquet.RecursiveSchema.Repeated (Leaf Slot LevelError Error openFile)

private def load (folder : System.FilePath) (name : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (name ++ ".parquet"))⟩

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"unexpected refusal: {repr cause}")

private def refuse {α : Type} (wanted : Error) (result : Except Error α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"accepted input expected to fail with {repr wanted}")
  | .error actual =>
    unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")

private def check (file : Bytes) (schema : Arrow.RecursiveSchema.Schema)
    (expected : List (Leaf × Nat × Nat)) : IO Unit := do
  let result ← take (openFile {} file)
  unless result.schema.arrow == schema do throw (IO.userError "Arrow declarations differ")
  let leaves := result.schema.leaves.toList
  unless leaves.map (fun plan => (plan, plan.maxRepetition, plan.maxDefinition)) = expected do
    throw (IO.userError s!"physical leaves or level plans differ: {repr leaves}")

private def pairs (file : Bytes) (observations : List (Nat × Nat × Nat × Except LevelError Slot)) :
    IO Unit := do
  let result ← take (openFile {} file)
  for (column, repetition, definition, expected) in observations do
    let some plan := result.schema.leaves[column]? | throw (IO.userError "missing leaf")
    unless plan.classify 7 repetition definition = expected do
      throw (IO.userError s!"column {column}, repetition {repetition}, definition {definition}")

private def predecessor (file : Bytes) : IO Unit := do
  let old ← take (Parquet.RecursiveSchema.openFile {} file)
  let new ← take (openFile {} file)
  unless old.schema.arrow == new.schema.arrow do throw (IO.userError "nonrepeated schema differs")
  unless old.schema.leaves.toList.map Leaf.ofNonRepeated = new.schema.leaves.toList do
    throw (IO.userError "nonrepeated plan differs")

private def standalone (file : Bytes) : IO Unit := do
  let old ← take (Parquet.ListFile.openFile {} file)
  let new ← take (openFile {} file)
  let [plan] := new.schema.leaves.toList | throw (IO.userError "expected one standalone leaf")
  unless plan.site.location.path = old.shape.path ∧ plan.maxRepetition = 1 ∧ plan.maxDefinition = 3 do
    throw (IO.userError "standalone plan differs")
"""


def write(schema, rows):
    sink = pa.BufferOutputStream()
    pq.write_table(pa.Table.from_pylist(rows, schema=schema), sink, row_group_size=3,
                   use_dictionary=False, compression="NONE", data_page_version="1.0",
                   use_compliant_nested_type=False, store_schema=False)
    return sink.getvalue().to_pybytes()


def fixtures():
    int32, int64 = pa.int32(), pa.int64()
    nested = pa.struct([pa.field("hi", int64)])
    element = pa.struct([pa.field("lo", int32, nullable=False), pa.field("nested", nested)])
    items = pa.list_(pa.field("élément", element))
    packet = pa.struct([pa.field("items", items), pa.field("flag", int32, nullable=False)])
    nullable = pa.schema([pa.field("packet", packet), pa.field("seq", int64, nullable=False)])
    nullable_rows = [{"packet": value, "seq": i} for i, value in enumerate([
        None,
        {"items": None, "flag": 1},
        {"items": [], "flag": 2},
        {"items": [None, {"lo": -2**31, "nested": None},
                   {"lo": 9, "nested": {"hi": None}},
                   {"lo": 2**31 - 1, "nested": {"hi": -2**63}}], "flag": 3},
        {"items": [{"lo": -7, "nested": {"hi": 2**63 - 1}}], "flag": 4},
    ])]
    required = pa.schema([
        pa.field("wide", pa.list_(pa.field("tick", int64, nullable=False)), nullable=False),
        pa.field("optional_element", pa.list_(pa.field("item", int32)), nullable=False),
        pa.field("required_element", pa.list_(pa.field("unit", int32, nullable=False))),
    ])
    required_rows = [
        {"wide": [], "optional_element": [], "required_element": None},
        {"wide": [-2**63, 2**63-1], "optional_element": [None, -1], "required_element": []},
        {"wide": [2**45], "optional_element": [2], "required_element": [3, -4]},
    ]
    alone = pa.schema([pa.field("items", pa.list_(pa.field("element", int32)))])
    alone_rows = [{"items": value} for value in (None, [], [None, -1, 2])]
    deep_repeat = pa.schema([pa.field("outer", pa.list_(pa.field("entry", pa.struct([
        pa.field("inner", pa.list_(pa.field("value", int32)))
    ]))))])
    samples = {
        "nullable_lists": (nullable, nullable_rows),
        "required_lists": (required, required_rows),
        "standalone": (alone, alone_rows),
        "nested_repeated": (deep_repeat, [{"outer": [{"inner": [1, 2]}]}]),
    }
    genuine = {name: write(schema, rows) for name, (schema, rows) in samples.items()}
    wire = genuine["nullable_lists"]

    def edit(change):
        footer = MIXED["metadata"](wire)
        change(THRIFT["list_field"](footer, 2))
        return pack(wire, footer)

    def raw_repeated(elements):
        del elements[2][6], elements[2][10]

    def bad_outer(elements):
        elements[1][6], elements[1][10] = elements[2][6], elements[2][10]

    return genuine, samples, {
        "raw_repeated": edit(raw_repeated),
        "bad_outer": edit(bad_outer),
        "bad_wrapper": edit(lambda elements: elements[3].__setitem__(3, (TType.I32, 1))),
        "wrong_converted": edit(lambda elements: elements[2].__setitem__(6, (TType.I32, 0))),
    }


def describe(wire, expected_schema, expected_rows):
    footer = MIXED["metadata"](wire)
    elements = THRIFT["list_field"](footer, 2)
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    assert parquet.schema_arrow.equals(expected_schema)
    assert parquet.read().to_pylist() == expected_rows
    assert elements[0][5][1] == len(expected_schema)
    cursor, leaves = 1, []

    def visit(field, path, steps, boundary, element=False):
        nonlocal cursor
        ordinal = cursor
        cursor += 1
        original = elements[ordinal]
        path += (field.name,)
        location = ordinal, path
        assert original[4][1].decode() == field.name
        assert original[3][1] == int(field.nullable)
        assert 2 not in original
        nullable = str(field.nullable).lower()
        if pa.types.is_list(field.type):
            assert boundary is None
            assert 1 not in original and original[5][1] == 1 and original[6][1] == 3
            assert original[10][1] == {3: (TType.STRUCT, {})}
            wrapper = elements[cursor]
            assert wrapper[3][1] == 2 and wrapper[4][1].decode() == "list"
            assert wrapper[5][1] == 1 and not (set(wrapper) & {1, 2, 6, 10})
            physical = cursor, path + ("list",)
            cursor += 1
            if field.nullable:
                steps += (f".optional {location_term(location)} .list",)
            boundary = location, physical, len(steps)
            steps += (f".emptyList {location_term(location)} {location_term(physical)}",)
            children = [visit(field.type.value_field, physical[1], steps, boundary, element=True)]
            kind = ".list"
        else:
            assert not (set(original) & {6, 10})
            if field.nullable:
                role = "element" if element else "descendant" if boundary else "node"
                steps += (f".optional {location_term(location)} .{role}",)
            if pa.types.is_struct(field.type):
                assert 1 not in original and original[5][1] == field.type.num_fields
                children = [visit(child, path, steps, boundary) for child in field.type]
                kind = ".struct"
            else:
                assert field.type in (pa.int32(), pa.int64())
                assert original[1][1] == (1 if field.type.bit_width == 32 else 2)
                kind, children = f".int{field.type.bit_width}", []
                leaves.append((location, field, steps, boundary))
        return f".node (some {string(field.name)}) {nullable} {kind} {lst(children)}"

    arrow = [visit(field, (), (), None) for field in expected_schema]
    assert cursor == len(elements)
    assert len(parquet.schema) == len(leaves)
    for column, (location, field, steps, boundary) in enumerate(leaves):
        original = parquet.schema.column(column)
        assert original.path == ".".join(location[1])
        assert original.max_definition_level == len(steps)
        assert original.max_repetition_level == int(boundary is not None)
        for group in range(parquet.num_row_groups):
            metadata = THRIFT["column_metadata"](footer, group, column)
            assert tuple(item.decode() for item in THRIFT["list_field"](metadata, 3)) == location[1]
            assert metadata[1][1] == (1 if field.type.bit_width == 32 else 2)
            assert parquet.metadata.row_group(group).column(column).path_in_schema == original.path
    return arrow, leaves


def leaf_term(leaf):
    location, field, steps, boundary = leaf
    site = f"⟨{location_term(location)}, {string(field.name)}, {str(field.nullable).lower()}⟩"
    repeated = "none"
    if boundary:
        outer, wrapper, empty = boundary
        repeated = f"(some ⟨{location_term(outer)}, {location_term(wrapper)}, {empty}⟩)"
    return f"(⟨{site}, .int{field.type.bit_width}, {lst(steps)}, {repeated}⟩, {int(boundary is not None)}, {len(steps)})"


def classify_pairs(leaves):
    for index, (location, _, steps, boundary) in enumerate(leaves):
        max_rep, max_def = int(boundary is not None), len(steps)
        site = location_term(location)
        for rep in range(max_rep + 2):
            for definition in range(max_def + 2):
                if rep > max_rep:
                    answer = f".error (.repetition {site} 7 {rep} {max_rep})"
                elif definition > max_def:
                    answer = f".error (.definition {site} 7 {definition} {max_def})"
                elif rep == 1 and definition <= boundary[2]:
                    answer = f".error (.continuation {site} 7 {definition})"
                else:
                    position = ".continuation" if rep else ".rowStart"
                    presence = ".value" if definition == max_def else f".absent ({steps[definition]})"
                    answer = f".ok ⟨{position}, {presence}⟩"
                yield f"({index}, {rep}, {definition}, {answer})"


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    prior = json.loads(PREDECESSOR["MANIFEST"].read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert platform.python_version() == prior["producer"]["cpython"]
    assert pa.__version__ == prior["producer"]["pyarrow"]
    assert version("thrift") == prior["producer"]["thrift"]
    genuine, samples, edited = fixtures()
    assert fingerprints(genuine) == pins["genuine_parquet"]
    assert fingerprints(edited) == pins["labeled_edits"]
    admitted, controls, _ = PREDECESSOR["fixtures"]()
    preserved = {"nonrepeated": admitted["deep"][2], "annotated": controls["annotated"]}
    assert fingerprints(preserved) == {key: prior["genuine_parquet"][name]
                                       for key, name in (("nonrepeated", "deep"), ("annotated", "annotated"))}
    code = [LEAN, "public def main (args : List String) : IO Unit := do",
            '  let [folder] := args | throw (IO.userError "expected fixture folder")']
    count = 0
    for label in ("nullable_lists", "required_lists", "standalone"):
        fields, leaves = describe(genuine[label], *samples[label])
        tests = list(classify_pairs(leaves))
        count += len(tests)
        code.extend([
            f'  let source_{label} ← load folder "{label}"',
            f'  check source_{label} ⟨{lst(fields)}⟩ {lst(map(leaf_term, leaves))}',
            f'  pairs source_{label} {lst(tests)}',
        ])
        print(f"{label}: {len(leaves)} original ordered leaves and {len(tests)} level pairs", flush=True)
    code.extend([
        '  predecessor (← load folder "nonrepeated")',
        '  standalone source_standalone',
        '  refuse (.original (.snapshot (.invalidMetadata .schemaDepth))) '
        '(openFile { maxSchemaDepth := 6 } source_nullable_lists)',
        '  refuse (.original (.repetition ⟨3, ["packet", "items", "list"]⟩ (some .repeated))) '
        '(openFile {} (← load folder "raw_repeated"))',
        '  refuse (.listShape ⟨1, ["packet"]⟩) (openFile {} (← load folder "bad_outer"))',
        '  refuse (.wrapper ⟨3, ["packet", "items", "list"]⟩) '
        '(openFile {} (← load folder "bad_wrapper"))',
        '  refuse (.annotation ⟨2, ["packet", "items"]⟩ .invalidList) '
        '(openFile {} (← load folder "wrong_converted"))',
        '  refuse (.annotation ⟨1, ["date"]⟩ .invalidList) (openFile {} (← load folder "annotated"))',
        '  refuse (.nestedRepeated ⟨4, ["outer", "list", "entry", "inner"]⟩ ⟨2, ["outer", "list"]⟩) '
        '(openFile {} (← load folder "nested_repeated"))',
    ])
    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        for label, wire in (genuine | edited | preserved).items():
            (scratch / f"{label}.parquet").write_bytes(wire)
        driver = scratch / "Check.lean"
        driver.write_text("\n".join(code) + "\n", encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        "--run", str(driver), directory], cwd=ROOT, check=True)
    print(f"Verified {count} local level pairs and seven typed footer refusals")


if __name__ == "__main__":
    main()
