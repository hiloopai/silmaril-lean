"""Verify native Lean-written TwoListStruct PAR1 with PyArrow and raw V1 checks."""

from importlib.metadata import version
from itertools import product
import json
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
EVENTS = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-events-oracle/check.py"))
NATIVE = EVENTS["NATIVE"]
THRIFT, FRAMES, LEVEL, lst = (NATIVE[key] for key in ("THRIFT", "FRAMES", "LEVEL", "lst"))
field_term, batches_term = EVENTS["field_term"], EVENTS["batches_term"]


LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Defs

open Silmaril.Formats
open Parquet.RecursiveSchema.TwoListStruct
open Parquet.RecursiveSchema.TwoListStruct.Writer

set_option maxRecDepth 8192

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError (reprStr cause))

private def write (folder : System.FilePath) (label : String) (input : Input) : IO Unit := do
  let output ← take (emit {} input)
  let original ← take (openFile {} output.bytes)
  let recovered ← take (Reader.readAll {} original.schema)
  unless original.schema.plan.arrow == input.schema && recovered == input.groups &&
      original.snapshot.groupCount == input.groups.length do
    throw (IO.userError "checked native readback differs")
  IO.FS.writeBinFile (folder / (label ++ ".parquet")) output.bytes.data

private def deny {α : Type} (expected : Writer.Error) (result : Except Writer.Error α) : IO Unit := do
  let .error actual := result | throw (IO.userError "expected a writer refusal")
  unless actual = expected do throw (IO.userError s!"expected {repr expected}, got {repr actual}")

private def refuse (expected : Writer.Error) (limits : Limits) (input : Input) : IO Unit :=
  deny expected (emit limits input)

private def refuseReadback (input : Input) : IO Unit := do
  let output ← take (emit {} input)
  deny .readbackMismatch (certify {} { input with groups := input.groups.reverse } output)

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture directory")
"""


def cases():
    for flags in product((False, True), repeat=4):
        original, groups, _ = NATIVE["native"](flags)
        outer = original.field(0)
        inner = outer.type.value_field
        element = inner.type.value_field
        bits = "".join(str(int(flag)) for flag in flags)
        yield f"32_64_{bits}", original, groups, True
        swapped = pa.field(element.name, pa.struct(list(reversed(list(element.type)))), False)
        reversed_inner = pa.field(inner.name, pa.list_(swapped), inner.nullable)
        yield f"64_32_{bits}", pa.schema([pa.field(outer.name, pa.list_(reversed_inner), outer.nullable)]), groups, True
    schema, groups, _ = EVENTS["renamed"]()
    yield "renamed_no_crc_empty_group", schema, [groups[0], [], groups[0]], False
    yield "schema_only", schema, [], True


def input_term(schema, rows, crc=True):
    batches = [[{schema.field(0).name: row} for row in group] for group in rows]
    return f"⟨⟨{lst(map(field_term, schema))}⟩, {batches_term(schema, batches)}, {str(crc).lower()}⟩"


def section(values):
    runs = b"".join(bytes((2, value)) for value in values)
    return struct.pack("<I", len(runs)) + runs


def inspect(wire, schema, groups, crc):
    assert wire[:4] == wire[-4:] == b"PAR1"
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.equals(schema, check_metadata=True)
    assert parquet.num_row_groups == len(groups)
    outer = schema.field(0)
    inner = outer.type.value_field
    element = inner.type.value_field
    children = list(element.type)
    nullable = (outer.nullable, inner.nullable, *(child.nullable for child in children))
    shared = NATIVE["steps"](nullable)[2]
    physical = [1 if child.type.bit_width == 32 else 2 for child in children]
    footer = NATIVE["metadata"](wire)
    entries = THRIFT["list_field"](footer, 2)
    assert len(entries) == 8 and footer[1][1] == 1
    assert footer[3][1] == parquet.metadata.num_rows == sum(map(len, groups))
    assert entries[0][4][1] == b"schema" and entries[0][5][1] == 1
    for i, field in ((1, outer), (3, inner)):
        node, wrapper = entries[i:i+2]
        assert node[3][1] == field.nullable and node[4][1] == field.name.encode() and node[5][1] == 1
        assert node[6][1] == 3 and node[10][1] == {3: (TType.STRUCT, {})}
        assert set(wrapper) == {3, 4, 5}
        assert wrapper[3][1] == 2 and wrapper[4][1] == b"list" and wrapper[5][1] == 1
    declaration = entries[5]
    assert set(declaration) == {3, 4, 5}
    assert declaration[3][1] == 0 and declaration[4][1] == element.name.encode() and declaration[5][1] == 2
    for leaf, child, kind in zip(entries[6:], children, physical, strict=True):
        assert set(leaf) == {1, 3, 4}
        assert leaf[1][1] == kind and leaf[3][1] == child.nullable and leaf[4][1] == child.name.encode()

    output_groups = THRIFT["list_field"](footer, 4)
    columns = list(NATIVE["V2"]["columns"](wire))
    assert len(output_groups) == len(groups) and len(columns) == 2 * len(groups)
    offset = 4
    for group, rows in enumerate(groups):
        assert parquet.read_row_group(group).column(0).to_pylist() == rows
        group_footer = output_groups[group]
        assert set(group_footer) == {1, 2, 3} and group_footer[3][1] == len(rows)
        group_start = offset
        for side, child in enumerate(children):
            position, chunk, lo, hi = columns[2 * group + side]
            assert position == (group, side) and lo == offset
            assert set(THRIFT["list_field"](group_footer, 1)[side]) == {2, 3}
            assert set(chunk) == {1, 2, 3, 4, 5, 6, 7, 9}
            assert chunk[1][1] == physical[side] and THRIFT["list_field"](chunk, 2) == [0, 3]
            path = [outer.name, "list", inner.name, "list", element.name, child.name]
            assert [name.decode() for name in THRIFT["list_field"](chunk, 3)] == path
            assert chunk[4][1] == 0 and chunk[9][1] == lo

            [(at, header, body_at, body)] = FRAMES(wire, lo, hi)
            assert at == lo and body_at + len(body) == hi
            assert header[1][1] == 0 and header[2][1] == header[3][1] == len(body)
            assert chunk[6][1] == body_at - at + header[2][1] == hi - lo
            assert chunk[7][1] == body_at - at + header[3][1] == hi - lo
            assert (4 in header) == crc
            if crc:
                assert header[4][1] & 0xffffffff == zlib.crc32(body)

            expected = NATIVE["trace"](rows, nullable, side, tuple(field.name for field in children))
            count = len(expected)
            assert chunk[5][1] == count and [header[5][1][i][1] for i in range(1, 5)] == [count, 0, 3, 3]
            maximum = shared + int(child.nullable)
            reps, rest = LEVEL(body, 2, count)
            defs, suffix = LEVEL(rest, maximum, count)
            fmt = "<i" if physical[side] == 1 else "<q"
            assert len(suffix) == defs.count(maximum) * struct.calcsize(fmt)
            words = iter(word for word, in struct.iter_unpack(fmt, suffix))
            observed = [(rep, definition, next(words) if definition == maximum else None)
                        for rep, definition in zip(reps, defs, strict=True)]
            assert observed == expected and (not reps or reps[0] == 0) and reps.count(0) == len(rows)
            assert body == (section(rep for rep, _, _ in expected) + section(definition for _, definition, _ in expected)
                            + b"".join(struct.pack(fmt, word) for _, _, word in expected if word is not None))
            offset = hi
        assert group_footer[2][1] == offset - group_start
    assert offset == len(wire) - 8 - struct.unpack("<I", wire[-8:-4])[0]


def refusals(positives):
    _, schema, groups, _ = next(case for case in positives if case[0] == "32_64_1111")
    valid = input_term(schema, groups)
    slots = len(NATIVE["trace"](groups[0], (True,) * 4, 0))
    struct_field = schema.field(0).type.value_type.value_field
    bad_struct = pa.field(struct_field.name, struct_field.type, True)
    bad_inner = pa.field("element", pa.list_(bad_struct), True)
    invalid = input_term(pa.schema([pa.field("items", pa.list_(bad_inner))]), [])
    return [
        f'  refuse .declaration {{}} {invalid}',
        '  refuse .declaration {} ⟨⟨[]⟩, [], false⟩',
        '  refuse .declaration {} ⟨⟨[.node none false .list []]⟩, [], false⟩',
        f'  refuse (.groupLimit 2) {{ maxGroups := 1 }} {valid}',
        f'  refuse (.totalRowLimit {sum(map(len, groups))}) {{ maxTotalRows := 0 }} {valid}',
        f'  refuse (.rowLimit 0 {len(groups[0])}) {{ chunk.maxRows := 0 }} {valid}',
        f'  refuse (.slotLimit 0 {slots}) {{ chunk.maxSlots := 0 }} {valid}',
        f'  refuse (.totalSlotLimit 0 {2 * slots}) {{ maxTotalSlots := {slots} }} {valid}',
        f'  refuse (.column 0 .left (.pageLimit 0)) {{ chunk.framing.maxPages := 0 }} {valid}',
        f'  refuse (.column 0 .left (.levelLimit 0)) {{ chunk.levels := ⟨1024, 0⟩ }} {valid}',
        f'  refuse (.column 0 .left (.bodyLimit 0)) {{ chunk.maxBodyBytes := 0 }} {valid}',
        f'  refuse (.column 0 .left (.headerLimit 0)) {{ chunk.framing.maxHeaderBytes := 0 }} {valid}',
        f'  refuse (.schema (.depth [])) {{ schema.snapshot.maxSchemaDepth := 6 }} {valid}',
        f'  refuse (.schema .fieldLimit) {{ schema.maxFields := 7 }} {valid}',
        f'  refuse (.schema .fileLimit) {{ schema.maxFileBytes := 11 }} {valid}',
        f'  refuse (.schema (.compact .byteLimit)) {{ schema.snapshot.footer.maxFooterBytes := 0 }} {valid}',
        f'  refuse (.rowCount 0 2 1) {{}} ({{ ({valid} : Input) with groups := [⟨2, [[none]]⟩] }})',
        f'  refuse (.projection 0) {{}} ({{ ({valid} : Input) with groups := '
        '[⟨1, [[some (.list [some (.list [none])])]]⟩] })',
        f'  refuse (.projection 0) {{}} ({{ ({valid} : Input) with groups := '
        '[⟨1, [[some (.list [some (.list [some (.struct [none])])])]]⟩] })',
        f'  refuse (.column 0 .right (.projection 0)) {{}} ({{ ({valid} : Input) with groups := '
        '[⟨1, [[some (.list [some (.list [some (.struct [none, some (.int32 4)])])])]]⟩] })',
        f'  refuseReadback {valid}',
    ]


def verify(folder):
    positives = list(cases())
    denied = refusals(positives)
    code = [LEAN]
    for label, schema, groups, crc in positives:
        code.append(f'  write folder "{label}" {input_term(schema, groups, crc)}')
    driver = folder / "TwoListStructWriter.lean"
    driver.write_text("\n".join(code + denied) + "\n", encoding="utf-8")
    subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                    "--run", str(driver), str(folder)], cwd=ROOT, check=True)
    emitted = {}
    for label, schema, groups, crc in positives:
        wire = (folder / f"{label}.parquet").read_bytes()
        inspect(wire, schema, groups, crc)
        emitted[label] = wire
    pages = 2 * sum(len(groups) for _, _, groups, _ in positives)
    print(f"Checked {len(emitted)} Lean Parquet files, {pages} original V1 pages and {len(denied)} typed refusals")
    return NATIVE["fingerprints"](emitted)


def producer():
    assert platform.python_implementation() == "CPython"
    return {"cpython": platform.python_version(), "pyarrow": pa.__version__, "thrift": version("thrift")}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert producer() == pins["producer"]
    with tempfile.TemporaryDirectory() as directory:
        assert verify(Path(directory)) == pins["lean_parquet"], "Lean Parquet output pins changed"


if __name__ == "__main__":
    main()
