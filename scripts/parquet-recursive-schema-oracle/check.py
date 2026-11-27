"""Compare Lean footer bindings with genuine PyArrow schemas and original definition words."""

from hashlib import sha256
from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MANIFEST = HERE / "fixtures.json"
ORACLE = runpy.run_path(str(HERE.parent / "parquet-nested-point-ipc-oracle/check.py"))
THRIFT, MIXED, FRAMES, HYBRID = (ORACLE[name] for name in ("THRIFT", "MIXED", "FRAMES", "HYBRID"))

LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Defs

open Silmaril Silmaril.Formats
open Parquet.RecursiveSchema

private def takeResult {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def refuse {ε α : Type} [Repr ε] [DecidableEq ε] (expected : ε)
    (result : Except ε α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"accepted an input expected to fail with {repr expected}")
  | .error actual =>
    unless actual = expected do
      throw (IO.userError s!"expected {repr expected}, got {repr actual}")

private def load (folder : System.FilePath) (name : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (name ++ ".parquet"))⟩

private structure ExpectedChunk where
  start : Nat
  stop : Nat
  levels : List Nat
  presence : List Presence

private def verify (file : Bytes) (expected : Arrow.RecursiveSchema.Schema)
    (leaves : List (Leaf × Nat)) (groups : List (Nat × List ExpectedChunk)) :
    IO Unit := do
  let source ← takeResult (openFile {} file)
  unless source.schema.arrow == expected do throw (IO.userError "ordered Arrow declaration differs")
  unless source.schema.leaves.toList = leaves.map Prod.fst do
    throw (IO.userError "leaf ordinal, path, type or nullable ancestry differs")
  unless source.schema.leaves.toList.map Leaf.bitWidth = leaves.map Prod.snd do
    throw (IO.userError "definition bit width differs")
  unless source.snapshot.groupCount = groups.length do throw (IO.userError "group count differs")
  for ((rows, chunks), group) in groups.zipIdx do
    unless chunks.length = source.schema.leaves.size do throw (IO.userError "test width differs")
    for (want, column) in chunks.zipIdx do
      let bound ← takeResult (bindChunk source.schema group column)
      unless bound.rowGroup.numRows = Int.ofNat rows ∧ bound.span.start = want.start ∧
          bound.span.stop = want.stop ∧ want.levels.length = rows do
        throw (IO.userError s!"original row count or chunk extent differs at {group}, {column}")
      let seen ← takeResult (want.levels.zipIdx.mapM fun (level, row) => bound.leaf.classify row level)
      unless seen = want.presence do
        throw (IO.userError s!"definition presence differs at {group}, {column}")
      let high := bound.leaf.maxDefinition + 1
      refuse (.level bound.leaf.site.location rows high bound.leaf.maxDefinition)
        (bound.leaf.classify rows high)
"""


def pack(wire, footer):
    size, = struct.unpack_from("<I", wire, len(wire) - 8)
    encoded = THRIFT["encode"](footer)
    return wire[:-8-size] + encoded + struct.pack("<I", len(encoded)) + b"PAR1"


def write(schema, groups, *, codec="NONE", encoding=None):
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, compression=codec, use_dictionary=False, data_page_version="1.0",
                          data_page_size=32, write_batch_size=2, write_page_checksum=False,
                          store_schema=False, column_encoding=encoding) as writer:
        for rows in groups:
            writer.write_table(pa.Table.from_pylist(rows, schema=schema))
    return sink.getvalue().to_pybytes()


def fixtures():
    i32, i64 = pa.int32(), pa.int64()
    tail = pa.struct([pa.field("signed", i32, False), pa.field("wide", i64)])
    deep = pa.struct([pa.field("tail", tail), pa.field("count", i32)])
    must = pa.struct([pa.field("deep", deep)])
    packet = pa.struct([pa.field("must", must, False), pa.field("旁", i64)])
    schema = pa.schema([pa.field("packet", packet), pa.field("seq", i32, False)])

    def present(sequence, deep_value, side=None):
        return {"packet": {"must": {"deep": deep_value}, "旁": side}, "seq": sequence}

    groups = [[{"packet": None, "seq": 1}, present(2, None), present(3, {"tail": None, "count": 3}),
               present(4, {"tail": {"signed": -(2**31), "wide": None}, "count": None}),
               present(5, {"tail": {"signed": 2**31 - 1, "wide": -(2**63)}, "count": 17}, 2**45)],
              [present(-9, {"tail": {"signed": -3, "wide": 2**63 - 1}, "count": -8}, -(2**42)),
               present(0, {"tail": None, "count": None}), {"packet": None, "seq": -10}]]

    # A required path has no definition prefix. The optional sibling
    # can be absent or present with all nullable children absent.
    inner = pa.struct([pa.field("n", i64, False), pa.field("k", i32, False)])
    required = pa.struct([pa.field("inner", inner, False)])
    note = pa.struct([pa.field("optional", i32)])
    other = pa.schema([pa.field("note", note), pa.field("required", required, False)])
    other_rows = [[{"note": None, "required": {"inner": {"n": -(2**63), "k": -(2**31)}}},
                   {"note": {"optional": None}, "required": {"inner": {"n": 2**63 - 1, "k": 2**31 - 1}}}],
                  [{"note": {"optional": 17}, "required": {"inner": {"n": -(2**50), "k": 0}}}]]

    admitted = {
        "deep": (schema, groups, write(schema, groups)),
        "required_path": (other, other_rows, write(other, other_rows)),
        "schema_only": (schema, [], write(schema, [])),
    }
    checks = {
        "annotated": write(pa.schema([pa.field("date", pa.date32())]), [[{"date": 1}]]),
        "list": write(pa.schema([pa.field("items", pa.list_(i32))]), [[{"items": [0, None]}]]),
        "float": write(pa.schema([pa.field("float", pa.float32())]), [[{"float": -1.5}]]),
        "snappy": write(other, other_rows, codec="SNAPPY"),
        "delta": write(other, other_rows, encoding="DELTA_BINARY_PACKED"),
    }
    footer = MIXED["metadata"](checks["list"])
    outer = THRIFT["list_field"](footer, 2)[1]
    assert {6, 10} <= set(outer)
    del outer[6], outer[10]
    return admitted, checks, {"unannotated_repeated": pack(checks["list"], footer)}


def lst(items):
    return "[" + ", ".join(items) + "]"


def string(value):
    return json.dumps(value, ensure_ascii=False)


def path_term(path):
    return lst(map(string, path))


def location_term(location):
    ordinal, path = location
    return f"⟨{ordinal}, {path_term(path)}⟩"


def describe(schema, footer):
    elements = THRIFT["list_field"](footer, 2)
    assert elements[0][5][1] == len(schema) and not (set(elements[0]) & {1, 6, 10})
    ordinal = 0
    leaves = []

    def enter(field, parent, optional):
        nonlocal ordinal
        ordinal += 1
        location = ordinal, parent + (field.name,)
        original = elements[ordinal]
        assert original[3][1] == int(field.nullable) and original[4][1].decode() == field.name
        assert not (set(original) & {2, 6, 10})
        steps = optional + (location,) if field.nullable else optional
        if pa.types.is_struct(field.type):
            assert original[5][1] == field.type.num_fields and 1 not in original
            children = [enter(child, location[1], steps) for child in field.type]
            kind = ".struct"
        else:
            assert field.type in (pa.int32(), pa.int64())
            assert original[1][1] == (1 if field.type.bit_width == 32 else 2)
            children = []
            kind = f".int{field.type.bit_width}"
            leaves.append((location, field, steps))
        return f".node (some {string(field.name)}) {str(field.nullable).lower()} {kind} {lst(children)}"

    nodes = [enter(field, (), ()) for field in schema]
    assert ordinal + 1 == len(elements)
    return nodes, leaves


def leaf_term(declaration):
    location, field, steps = declaration
    site = f"⟨{location_term(location)}, {string(field.name)}, {str(field.nullable).lower()}⟩"
    plan = f"⟨{site}, .int{field.type.bit_width}, {lst(map(location_term, steps))}⟩"
    return f"({plan}, {len(steps).bit_length()})"


def inspect_group(wire, footer, group, schema, rows, leaves, parquet):
    producer = parquet.metadata.row_group(group)
    assert producer.num_rows == len(rows)
    captured = {}
    terms = []
    for ordinal, (location, field, steps) in enumerate(leaves):
        path = location[1]
        column = THRIFT["column_metadata"](footer, group, ordinal)
        assert [part.decode() for part in THRIFT["list_field"](column, 3)] == list(path)
        assert column[1][1] == (1 if field.type.bit_width == 32 else 2)
        assert column[4][1] == 0 and column[5][1] == len(rows)
        start, stop = MIXED["column_extent"](column)
        assert start == producer.column(ordinal).data_page_offset
        assert stop - start == producer.column(ordinal).total_compressed_size
        level_words, slots = [], []
        for _, header, _, body in FRAMES(wire, start, stop):
            assert header[1][1] == 0 and 4 not in header and header[2][1] == header[3][1] == len(body)
            info = header[5][1]
            assert [info[i][1] for i in (2, 3, 4)] == [0, 3, 3]
            count = info[1][1]
            if steps:
                extent, = struct.unpack_from("<I", body)
                levels = HYBRID(body[4:4+extent], len(steps).bit_length(), count)
                payload = body[4+extent:]
            else:
                levels, payload = [0] * count, body
            assert len(levels) == count
            level_words.extend(levels)
            code = "<i" if field.type.bit_width == 32 else "<q"
            signed = [word for word, in struct.iter_unpack(code, payload)]
            assert len(signed) == levels.count(len(steps))
            values = iter(signed)
            for level in levels:
                assert 0 <= level <= len(steps)
                slots.append((None, next(values)) if level == len(steps) else (steps[level], None))
        assert len(slots) == len(rows)
        captured[path] = slots
        # Derive the expected Lean states independently from PyArrow's nested rows.
        expected = []
        for row in rows:
            current = row
            for index, name in enumerate(path):
                current = current[name]
                if current is None:
                    missing = next(step for step in steps if step[1] == path[:index+1])
                    expected.append((missing, None))
                    break
            else:
                expected.append((None, current))
        assert slots == expected
        states = [".value" if missing is None else f".absent {location_term(missing)}"
                  for missing, _ in expected]
        terms.append(f"⟨{start}, {stop}, {lst(map(str, level_words))}, {lst(states)}⟩")

    def read_field(field, parent, row):
        path = parent + (field.name,)
        if pa.types.is_struct(field.type):
            evidence = [slots[row][0] for key, slots in captured.items() if key[:len(path)] == path]
            absent_here = [item is not None and item[1] == path for item in evidence]
            if any(absent_here):
                assert all(absent_here), "siblings disagree about the same original ancestor"
                return None
            return {child.name: read_field(child, path, row) for child in field.type}
        missing, value = captured[path][row]
        assert missing is None or missing[1] == path
        return value

    restored = [{field.name: read_field(field, (), row) for field in schema} for row in range(len(rows))]
    assert restored == rows
    return f"({len(rows)}, {lst(terms)})"


def compare(admitted, controls, edits):
    code = [LEAN, "public def main (args : List String) : IO Unit := do",
            '  let [folder] := args | throw (IO.userError "expected fixture folder")']
    for label, (schema, expected_rows, wire) in admitted.items():
        footer = MIXED["metadata"](wire)
        parquet = pq.ParquetFile(pa.BufferReader(wire))
        assert parquet.schema_arrow.equals(schema)
        assert parquet.num_row_groups == len(expected_rows)
        nodes, leaves = describe(schema, footer)
        terms = []
        for group, expected in enumerate(expected_rows):
            rows = parquet.read_row_group(group).to_pylist()
            assert rows == expected
            terms.append(inspect_group(wire, footer, group, schema, rows, leaves, parquet))
        code.append(f'  verify (← load folder "{label}") ⟨{lst(nodes)}⟩ '
                    f'{lst(map(leaf_term, leaves))} {lst(terms)}')
        print(f"{label}: original ordered columns and nested rows in groups {[len(rows) for rows in expected_rows]}")
    code.extend([
        '  refuse (.annotation ⟨1, ["date"]⟩) (openFile {} (← load folder "annotated"))',
        '  refuse (.annotation ⟨1, ["items"]⟩) (openFile {} (← load folder "list"))',
        '  refuse (.physical ⟨1, ["float"]⟩ .float) (openFile {} (← load folder "float"))',
        '  refuse (.repetition ⟨2, ["items", "list"]⟩ (some .repeated)) '
        '(openFile {} (← load folder "unannotated_repeated"))',
        '  let snappy ← takeResult (openFile {} (← load folder "snappy"))',
        '  refuse (.column 1 0 ["note", "optional"] (.codec 1)) (bindChunk snappy.schema 1 0)',
        '  let delta ← takeResult (openFile {} (← load folder "delta"))',
    ])
    delta_encodings = THRIFT["list_field"](THRIFT["column_metadata"](MIXED["metadata"](controls["delta"]), 1, 0), 2)
    assert 5 in delta_encodings
    code.extend([
        f'  refuse (.column 1 0 ["note", "optional"] (.encodings {lst(map(str, delta_encodings))})) '
        '(bindChunk delta.schema 1 0)',
        '  refuse (.groupOrdinal 2) (bindChunk delta.schema 2 0)',
        '  refuse (.columnOrdinal 3) (bindChunk delta.schema 1 3)',
        '  let deep ← takeResult (openFile {} (← load folder "deep"))',
        '  refuse (.depth ⟨4, ["packet", "must", "deep", "tail"]⟩) '
        '(compile { maxSchemaDepth := 4 } deep.snapshot)',
        '  IO.println "Checked native footer compilation, chunk bindings and indexed definition classifications"',
    ])
    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        inputs = {name: item[2] for name, item in admitted.items()} | controls | edits
        for name, data in inputs.items():
            (scratch / f"{name}.parquet").write_bytes(data)
        driver = scratch / "Check.lean"
        driver.write_text("\n".join(code) + "\n", encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        "--run", str(driver), directory], cwd=ROOT, check=True)


def fingerprints(files):
    return {name: {"bytes": len(data), "sha256": sha256(data).hexdigest()} for name, data in files.items()}


def main():
    pins = json.loads(MANIFEST.read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython" and platform.python_version() == pins["producer"]["cpython"]
    assert pa.__version__ == pins["producer"]["pyarrow"] and version("thrift") == pins["producer"]["thrift"]
    admitted, controls, edits = fixtures()
    genuine = {name: item[2] for name, item in admitted.items()} | controls
    assert fingerprints(genuine) == pins["genuine_parquet"]
    assert fingerprints(edits) == pins["labeled_edits"]
    compare(admitted, controls, edits)


if __name__ == "__main__":
    main()
