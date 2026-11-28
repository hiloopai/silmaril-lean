"""Verify Lean-written LIST-path Parquet with PyArrow and independent wire inspection."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import struct
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
EVENTS = runpy.run_path(str(HERE.parent / "parquet-recursive-list-path-events-oracle/check.py"))
NATIVE = EVENTS["NATIVE"]
V1, V2, FRAMES, LEVEL, lst, fingerprints, metadata, list_field = (
    NATIVE[key] for key in ("V1", "V2", "FRAMES", "LEVEL", "lst", "fingerprints", "metadata", "list_field")
)
schema_for, samples, levels = (NATIVE[key] for key in ("schema_for", "samples", "levels"))
field_term, batch_term = (NATIVE["CORE"]["ROWS"][key] for key in ("field_term", "batch_term"))

LEAN = EVENTS["LEAN"].split("\nprivate def checkReframe", 1)[0].replace("module\n", """module

import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.Defs
""", 1) + """
open Parquet.RecursiveSchema
open Parquet.RecursiveSchema.ListPath.Writer (Input Limits emit certify)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events (fieldName)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private def write (folder : System.FilePath) (label : String) (depth : Nat) (input : Input) : IO Unit := do
  let cap : Limits := { schema.snapshot.maxSchemaDepth := 2 * depth + 2, schema.maxFields := 2 * depth + 2 }
  let output ← take (emit cap input)
  let source ← take (ListPath.openFile cap.schema.snapshot output.bytes)
  let groups ← take (ListPath.Reader.readAll {} source.schema)
  unless source.schema.plan.arrow == input.schema && groups == input.groups do
    throw (IO.userError "native schema or group differs")
  checkFile output.bytes depth (input.schema.fields.map fun field => (fieldName field, field)) input.groups
  if depth = 1 then
    let old ← take (Repeated.openFile {} output.bytes)
    let groups ← take (Repeated.Rows.readAll {} old.schema)
    unless old.schema.arrow == input.schema && groups == input.groups do
      throw (IO.userError "one-LIST predecessor differs")
  if depth = 2 then
    let fixed ← take (TwoList.Writer.emit {} ⟨input.schema, input.groups, input.checksum⟩)
    unless fixed.bytes = output.bytes do throw (IO.userError "two-LIST writer bytes differ")
  IO.FS.writeBinFile (folder / (label ++ ".parquet")) output.bytes.data

private abbrev WriteError := ListPath.Writer.Error

private def deny {α : Type} (expected : WriteError) (result : Except WriteError α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"unexpected acceptance, expected {repr expected}")
  | .error actual =>
    unless actual = expected do throw (IO.userError s!"expected {repr expected}, got {repr actual}")

private def refuse (expected : WriteError) (limits : Limits) (input : Input) : IO Unit :=
  deny expected (emit limits input)

private def refuseReadback (input : Input) : IO Unit := do
  let output ← take (emit {} input)
  deny .readbackMismatch (certify {} { input with groups := input.groups.reverse } output)
"""


def input_term(schema, groups, width, crc=True):
    fields = lst(field_term(field).replace(json.dumps(field.name), json.dumps(field.name, ensure_ascii=False))
                 for field in schema)
    batches = lst(batch_term(group, width) for group in groups)
    return f"⟨⟨{fields}⟩, {batches}, {str(crc).lower()}⟩"


def cases():
    for width in (32, 64):
        for depth in (1, 2, 3, 4, 6, 16):
            all_optional = (1 << (depth + 1)) - 1
            bits_choices = range(all_optional + 1) if depth <= 3 else (0, all_optional // 3 * 2, all_optional)
            for bits in bits_choices:
                nullable = tuple(bool(bits & (1 << i)) for i in range(depth + 1))
                yield (f"signed_{width}_depth_{depth}_{bits}", schema_for(nullable, width), nullable,
                       width, samples(nullable, width), True)
    nullable = (True, False, True, True, False)
    field = pa.field("word", pa.int64(), nullable[-1])
    for name, optional in reversed(list(zip(("series_λ", "inner", "next", "tail"), nullable[:-1], strict=True))):
        field = pa.field(name, pa.list_(field), optional)
    first, second = samples(nullable, 64)
    yield "empty_group_no_crc", pa.schema([field]), nullable, 64, [first, [], second], False
    yield "schema_only", pa.schema([field]), nullable, 64, [], False


def singleton_section(values, maximum):
    width = (maximum.bit_length() + 7) // 8
    runs = b"".join(b"\x02" + value.to_bytes(width, "little") for value in values)
    return struct.pack("<I", len(runs)) + runs


def inspect(wire, schema, nullable, width, groups, crc):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.equals(schema, check_metadata=True)
    footer = metadata(wire)
    entries = list_field(footer, 2)
    assert parquet.num_row_groups == len(groups)
    assert parquet.metadata.num_rows == footer[3][1] == sum(map(len, groups))
    assert footer[1][1] == 1 and entries[0][4][1] == b"schema" and entries[0][5][1] == 1
    depth = len(nullable) - 1
    maximum = depth + sum(nullable)
    signed = 1 if width == 32 else 2
    assert len(entries) == 2 * depth + 2
    field, path = schema.field(0), []
    for i in range(depth):
        node, wrapper = entries[2 * i + 1:2 * i + 3]
        assert node[4][1].decode() == field.name and node[3][1] == int(nullable[i])
        assert node[5][1] == 1 and node[6][1] == 3 and list(node[10][1]) == [3]
        assert set(wrapper) == {3, 4, 5} and wrapper[3][1] == 2
        assert wrapper[4][1] == b"list" and wrapper[5][1] == 1
        path.extend((field.name, "list"))
        field = field.type.value_field
    leaf = entries[-1]
    assert set(leaf) == {1, 3, 4} and leaf[1][1] == signed
    assert leaf[4][1].decode() == field.name and leaf[3][1] == int(nullable[-1])
    path.append(field.name)

    row_groups = list_field(footer, 4)
    columns = list(V2["columns"](wire))
    assert len(row_groups) == len(columns) == len(groups)
    offset = 4
    fmt = "<i" if width == 32 else "<q"
    for group, (position, column, lo, hi) in enumerate(columns):
        assert position == (group, 0) and lo == offset
        group_footer = row_groups[group]
        assert set(group_footer) == {1, 2, 3}
        assert group_footer[2][1] == hi - lo and group_footer[3][1] == len(groups[group])
        assert set(list_field(group_footer, 1)[0]) == {2, 3}
        assert set(column) == {1, 2, 3, 4, 5, 6, 7, 9}
        assert column[1][1] == signed and list_field(column, 2) == [0, 3]
        assert [name.decode() for name in list_field(column, 3)] == path
        assert column[4][1] == 0 and column[9][1] == lo
        assert parquet.read_row_group(group).column(0).to_pylist() == groups[group]

        [(header_at, header, body_at, body)] = FRAMES(wire, lo, hi)
        assert header_at == lo and body_at + len(body) == hi
        assert header[1][1] == 0 and header[2][1] == header[3][1] == len(body)
        assert column[6][1] == body_at - header_at + header[2][1] == hi - lo
        assert column[7][1] == body_at - header_at + header[3][1] == hi - lo
        assert (4 in header) == crc
        if crc:
            assert header[4][1] & 0xffffffff == zlib.crc32(body)
        expected = levels(groups[group], nullable)
        count = len(expected)
        assert column[5][1] == count and [header[5][1][i][1] for i in range(1, 5)] == [count, 0, 3, 3]
        reps, rest = LEVEL(body, depth, count)
        defs, suffix = LEVEL(rest, maximum, count)
        assert len(suffix) == defs.count(maximum) * (width // 8)
        words = iter(word for word, in struct.iter_unpack(fmt, suffix))
        observed = [(rep, definition, next(words) if definition == maximum else None)
                    for rep, definition in zip(reps, defs, strict=True)]
        assert observed == expected and (not reps or reps[0] == 0) and reps.count(0) == len(groups[group])
        assert body == (singleton_section([rep for rep, _, _ in expected], depth)
                        + singleton_section([definition for _, definition, _ in expected], maximum)
                        + b"".join(struct.pack(fmt, word) for _, _, word in expected if word is not None))
        offset = hi
    assert wire[:4] == wire[-4:] == b"PAR1"
    assert offset == len(wire) - 8 - struct.unpack("<I", wire[-8:-4])[0]


def verify(folder):
    positives = list(cases())
    code = [LEAN, *V1["ENTRY"]]
    for label, schema, nullable, width, groups, crc in positives:
        code.append(f'  write folder "{label}" {len(nullable) - 1} {input_term(schema, groups, width, crc)}')

    nullable = (True,) * 4
    schema, groups = schema_for(nullable, 32), samples(nullable, 32)
    valid = input_term(schema, groups, 32)
    slots = [len(levels(group, nullable)) for group in groups]
    rows = sum(map(len, groups))
    deep = input_term(schema_for((True,) * 17, 64), [], 64)
    first_body = 8 + 4 * slots[0] + 4 * sum(word is not None for _, _, word in levels(groups[0], nullable))
    refusals = [
        f'  refuse (.groupLimit 2) {{ maxGroups := 1 }} {valid}',
        f'  refuse (.totalRowLimit {rows}) {{ maxTotalRows := 0 }} {valid}',
        f'  refuse (.rowLimit 0 {len(groups[0])}) {{ chunk.maxRows := 0 }} {valid}',
        f'  refuse (.slotLimit 0 {slots[0]}) {{ chunk.maxSlots := 0 }} {valid}',
        f'  refuse (.slotLimit 0 {slots[0]}) {{ chunk.levels := ⟨0, 1024⟩ }} {valid}',
        f'  refuse (.totalSlotLimit 1 {sum(slots)}) {{ maxTotalSlots := {slots[0]} }} {valid}',
        f'  refuse (.pageLimit 0) {{ chunk.framing.maxPages := 0 }} {valid}',
        f'  refuse (.levelLimit 0) {{ chunk.levels := ⟨1024, 0⟩ }} {valid}',
        f'  refuse (.bodyLimit 0) {{ chunk.maxBodyBytes := 0 }} {valid}',
        f'  refuse (.headerLimit 0) {{ chunk.framing.maxHeaderBytes := 0 }} {valid}',
        f'  refuse (.chunkLimit 0) {{ chunk.maxChunkBytes := {first_body} }} {valid}',
        f'  refuse (.schema .fileLimit) {{ schema.maxFileBytes := 11 }} {valid}',
        f'  refuse (.schema (.compact .byteLimit)) {{ schema.snapshot.footer.maxFooterBytes := 0 }} {valid}',
        f'  refuse (.schema .fieldLimit) {{ schema.maxFields := 7 }} {valid}',
        f'  refuse (.schema (.depth {lst(json.dumps(name) for name in ["chain"] + ["list", "element"] * 15)})) '
        f'{{ schema.snapshot.maxSchemaDepth := 32 }} {deep}',
        f'  refuse (.schema (.nameBudget [])) {{ schema.snapshot.footer.compact.maxBinaryBytes := 5 }} {valid}',
        '  refuse .declaration {} ⟨⟨[]⟩, [], false⟩',
        '  refuse .declaration {} ⟨⟨[.node (some "leaf") false .int32 []]⟩, [], false⟩',
        '  refuse .declaration {} ⟨⟨[.node (some "a") true .list [.node none false .int32 []]]⟩, [], false⟩',
        '  refuse .declaration {} ⟨⟨[.node (some "a") true .list [.node (some "s") true .struct []]]⟩, [], false⟩',
        f'  refuse (.rowCount 0 2 1) {{}} ({{ ({valid} : Input) with groups := [⟨2, [[none]]⟩] }})',
        f'  refuse (.projection 0) {{}} {input_term(schema_for((False,) * 4, 32), [[[[[None]]]]], 32)}',
        f'  refuse (.projection 0) {{}} ({{ ({valid} : Input) with groups := '
        '[⟨1, [[some (.list [some (.list [some (.list [some (.int64 7)])])])]]⟩] })',
        f'  refuseReadback {valid}',
    ]
    code.extend(refusals)
    V2["run_lean"](folder, "ListPathWriter.lean", code)
    emitted = {}
    for label, schema, nullable, width, groups, crc in positives:
        wire = (folder / f"{label}.parquet").read_bytes()
        inspect(wire, schema, nullable, width, groups, crc)
        emitted[label] = wire
    print(f"Checked {len(emitted)} Lean Parquet files, {sum(len(case[4]) for case in positives)} original V1 pages, "
          f"full and empty Events through EOS, and {len(refusals)} typed refusals")
    return fingerprints(emitted)


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        assert verify(Path(directory)) == pins["lean_parquet"], "native Parquet fixture pins changed"


if __name__ == "__main__":
    main()
