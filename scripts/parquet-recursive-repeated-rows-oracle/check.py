"""Compare checked repeated Parquet rows and source-coordinate refusals."""

from copy import deepcopy
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
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ORACLES = HERE.parent
CHUNK = runpy.run_path(str(ORACLES / "parquet-recursive-repeated-chunk-oracle/check.py"))
ARROW = runpy.run_path(str(ORACLES / "arrow-recursive-rows-oracle/check.py"))
SCHEMA = CHUNK["SCHEMA"]
THRIFT, MIXED, pack, fingerprints, location_term, lst = (
    SCHEMA[key] for key in ("THRIFT", "MIXED", "pack", "fingerprints", "location_term", "lst")
)
path_term, HYBRID = (CHUNK[key] for key in ("path_term", "HYBRID"))

LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs

open Silmaril Silmaril.Formats
open Parquet.RecursiveSchema.Repeated (openFile)
open Parquet.RecursiveSchema.Repeated.Rows
open Arrow.RecursiveSchema.Batch.Rows (Observation)

set_option maxRecDepth 4096

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"unexpected refusal: {repr cause}")

private def refuse {ε α : Type} [DecidableEq ε] [Repr ε] (wanted : ε) (result : Except ε α) :
    IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"accepted input expected to fail with {repr wanted}")
  | .error actual =>
    unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")

private def check (file : Bytes) (schema : Arrow.RecursiveSchema.Schema)
    (expected : List Observation) : IO Unit := do
  let source ← take (openFile {} file)
  unless source.schema.arrow == schema do throw (IO.userError "Arrow declarations differ")
  let groups ← take (readAll {} source.schema)
  unless groups == expected do throw (IO.userError s!"ordered groups differ: {repr groups}")

private def inconsistent (file : Bytes) (group : Nat) (wanted : Error) : IO Unit := do
  let source ← take (openFile {} file)
  for column in List.range source.schema.leaves.size do
    let _ ← take (readColumn {} source.schema group column)
  refuse wanted (readGroup {} source.schema group)
  refuse wanted (readAll {} source.schema)
"""


def explicit_empty(wire, schema, rows):
    footer = MIXED["metadata"](wire)
    groups = THRIFT["list_field"](footer, 4)
    _, leaves = SCHEMA["describe"](wire, schema, rows)
    empty = deepcopy(groups[0])
    length, = struct.unpack_from("<I", wire, len(wire) - 8)
    prefix = wire[:-8-length]
    payload = bytearray()
    for column, (_, _, steps, repeated) in zip(THRIFT["list_field"](empty, 1), leaves, strict=True):
        body = b"\0" * (4 * (int(bool(steps)) + int(repeated is not None)))
        header = THRIFT["encode"]({
            1: (TType.I32, 0), 2: (TType.I32, len(body)), 3: (TType.I32, len(body)),
            5: (TType.STRUCT, {i: (TType.I32, v) for i, v in enumerate((0, 0, 3, 3), 1)}),
        })
        offset = len(prefix) + len(payload)
        payload.extend(header + body)
        column[2] = TType.I64, offset
        metadata = column[3][1]
        metadata[2] = TType.LIST, (TType.I32, [0, 3])
        metadata[5] = TType.I64, 0
        metadata[6] = metadata[7] = TType.I64, len(header) + len(body)
        metadata[9] = TType.I64, offset
        metadata.pop(12, None)
    empty[2], empty[3] = (TType.I64, len(payload)), (TType.I64, 0)
    if 5 in empty:
        empty[5] = TType.I64, len(prefix)
    if 6 in empty:
        empty[6] = TType.I64, len(payload)
    groups.insert(1, empty)
    for ordinal, group in enumerate(groups):
        if 7 in group:
            group[7] = group[7][0], ordinal
    encoded = THRIFT["encode"](footer)
    return prefix + payload + encoded + struct.pack("<I", len(encoded)) + b"PAR1"


def edit_packed(wire, page, width, which, replacements):
    start = page.payload
    if which == "definition":
        start += 4 + struct.unpack_from("<I", wire, start)[0]
    length, = struct.unpack_from("<I", wire, start)
    start += 4
    section = wire[start:start+length]
    assert section[0] == 3 and length == 1 + width
    packed = int.from_bytes(section[1:], "little")
    expected = [entry[which == "definition"] for entry in page.events]
    assert HYBRID(section, width, len(expected)) == expected
    for index, value in replacements.items():
        shift = index * width
        packed = (packed & ~(((1 << width) - 1) << shift)) | (value << shift)
        expected[index] = value
    changed = bytes([3]) + packed.to_bytes(width, "little")
    assert HYBRID(changed, width, len(expected)) == expected
    return wire[:start] + changed + wire[start+length:]


def point(column, page, slot):
    return f"⟨⟨{column.group}, {column.index}, {path_term(column.path)}⟩, {page.index}, {page.header}, {slot}⟩"


def position(group, row, element=None):
    site = "none" if element is None else f"(some ({location_term(element[0])}, {element[1]}))"
    return f"⟨{group}, {row}, {site}⟩"


def conflict(position_term, site, first, other):
    return f".conflict {position_term} {location_term(site)} {first} {other}"


def nested_fixture():
    payload = pa.struct([pa.field("value", pa.int64()), pa.field("note", pa.int32())])
    element = pa.struct([pa.field("id", pa.int32(), nullable=False), pa.field("payload", payload)])
    schema = pa.schema([pa.field("items", pa.list_(pa.field("element", element)))])
    rows = [{"items": [
        {"id": -2**31, "payload": None},
        {"id": 1, "payload": {"value": None, "note": None}},
        {"id": 2**31-1, "payload": {"value": 2**63-1, "note": -4}},
    ]}]
    return schema, rows, SCHEMA["write"](schema, rows)


def fixtures(scratch):
    old, prior_edits, prior = CHUNK["fixtures"](scratch)
    old_pins = json.loads((ORACLES / "parquet-recursive-repeated-chunk-oracle/fixtures.json")
                          .read_text(encoding="utf-8"))
    for label in ("nested", "mixed_required", "multipage_crc"):
        assert fingerprints({label: old[label]})[label] == (
            old_pins["genuine_parquet"][label])
    assert fingerprints({"authored_continuation": prior_edits["authored_continuation"]}) == {
        "authored_continuation": old_pins["labeled_edits"]["authored_continuation"]}
    expected = {name: (*prior[name][:2], old[name])
                for name in ("nested", "mixed_required", "multipage_crc")}
    expected["authored_continuation"] = (*prior["authored_continuation"][:2],
                                         prior_edits["authored_continuation"])
    nested_schema, nested_rows, nested = nested_fixture()
    expected["nested_siblings"] = nested_schema, nested_rows, nested
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, nested_schema, use_compliant_nested_type=True, store_schema=False):
        pass
    schema_only = sink.getvalue().to_pybytes()
    expected["schema_only"] = nested_schema, [], schema_only

    schema, rows, wire = expected["nested"]
    original = {(col.group, col.index): col for col in CHUNK["capture"](wire, schema, rows)}
    extended = explicit_empty(wire, schema, rows)
    expected["explicit_empty"] = schema, rows, extended
    early_first, early_other = original[0, 0], original[0, 1]
    late_first, late_other = original[1, 0], original[1, 1]
    list_site = 2, ("packet", "items")
    element_site = 4, ("packet", "items", "list", "élément")
    edits = {
        "ancestor_presence": (edit_packed(wire, early_other.pages[0], 3, "definition", {0: 1}), 0,
            conflict(position(0, 0), (1, ("packet",)),
                     point(early_first, early_first.pages[0], 0), point(early_other, early_other.pages[0], 0))),
        "null_vs_empty": (edit_packed(wire, early_other.pages[0], 3, "definition", {1: 2}), 0,
            conflict(position(0, 1), list_site,
                     point(early_first, early_first.pages[0], 1), point(early_other, early_other.pages[0], 1))),
        "element_presence": (edit_packed(wire, late_other.pages[0], 3, "definition", {0: 4}), 1,
            conflict(position(1, 0, (list_site, 0)), element_site,
                     point(late_first, late_first.pages[0], 0), point(late_other, late_other.pages[0], 0))),
        "cardinality": (edit_packed(wire, late_other.pages[0], 1, "repetition", {3: 0, 4: 1}), 1,
            f".missing {position(1, 0, (list_site, 3))} {location_term(list_site)} "
            f"⟨1, 1, {path_term(late_other.path)}⟩ "
            f"(some {point(late_first, late_first.pages[0], 3)})"),
    }
    _, inner_first, inner_other = CHUNK["capture"](nested, nested_schema, nested_rows)
    step = inner_other.pages[0].events[0][1]
    assert inner_other.steps[step].endswith(".descendant")
    assert inner_other.pages[0].events[0][2] is None
    edits["nested_presence"] = (
        edit_packed(nested, inner_other.pages[0], len(inner_other.steps).bit_length(), "definition", {0: step + 1}),
        0,
        conflict(position(0, 0, ((1, ("items",)), 0)), (5, ("items", "list", "element", "payload")),
                 point(inner_first, inner_first.pages[0], 0), point(inner_other, inner_other.pages[0], 0)),
    )
    native = {"nested_siblings": nested, "schema_only": schema_only}
    labeled = {name: value[0] for name, value in edits.items()} | {"explicit_empty": extended}
    return expected, edits, native, labeled


def expected_observation(schema, rows):
    cells = [lst(ARROW["lean_cell"](pa, field.type, row[field.name]) for field in schema)
             for row in rows]
    return f"⟨{len(rows)}, {lst(cells)}⟩"


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    inherited = json.loads(SCHEMA["PREDECESSOR"]["MANIFEST"].read_text(encoding="utf-8"))["producer"]
    assert platform.python_implementation() == "CPython"
    assert platform.python_version() == inherited["cpython"]
    assert pa.__version__ == inherited["pyarrow"] and version("thrift") == inherited["thrift"]
    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        expected, edits, native, labeled = fixtures(scratch)
        assert fingerprints(native) == pins["genuine_parquet"]
        assert fingerprints(labeled) == pins["labeled_edits"]
        code = [LEAN, "public def main (args : List String) : IO Unit := do",
                '  let [folder] := args | throw (IO.userError "expected fixture folder")']
        for name, (schema, all_rows, wire) in expected.items():
            parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
            assert parquet.schema_arrow.equals(schema) and parquet.read().to_pylist() == all_rows
            rows = [parquet.read_row_group(i).to_pylist() for i in range(parquet.num_row_groups)]
            fields = [ARROW["BATCH"]["SCHEMA_ORACLE"]["pyarrow_field"](pa, field) for field in schema]
            declaration = ARROW["BATCH"]["SCHEMA_ORACLE"]["fields_term"](fields)
            groups = lst(expected_observation(schema, group) for group in rows)
            code.append(f'  check (← load folder "{name}") ⟨{declaration}⟩ {groups}')
            print(f"{name}: ordered row groups {[len(group) for group in rows]}", flush=True)
        for label, (_, group, wanted) in edits.items():
            code.append(f'  inconsistent (← load folder "{label}") {group} ({wanted})')
        code.extend([
            '  let nested ← take (openFile {} (← load folder "nested"))',
            '  refuse (.slotLimit 0 12) (readGroup { maxSlots := 11 } nested.schema 0)',
            '  let split ← take (openFile {} (← load folder "authored_continuation"))',
            '  refuse (.rowLimit 0 3) (readGroup { chunk.maxRows := 2 } split.schema 0)',
        ])
        for name, wire in ({name: item[2] for name, item in expected.items()} | labeled).items():
            (scratch / f"{name}.parquet").write_bytes(wire)
        driver = scratch / "Check.lean"
        driver.write_text("\n".join(code) + "\n", encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        "--run", str(driver), directory], cwd=ROOT, check=True)
    print("Verified exact logical rows and five intra-column-valid sibling edits")


if __name__ == "__main__":
    main()
