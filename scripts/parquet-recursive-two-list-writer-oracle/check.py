"""Read native Lean two-LIST Parquet with PyArrow and inspect its original frames."""

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
EVENTS = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-events-oracle/check.py"))
V1, V2, FRAMES, samples, schema_for, lst, field_term, batch_term, fingerprints = (
    EVENTS[k] for k in ("V1", "V2", "FRAMES", "samples", "schema_for", "lst", "field_term", "batch_term", "fingerprints")
)
TWO = EVENTS["ROWS"]["TWO"]
expected_slots = TWO["expected_slots"]
level_section = TWO["CHUNK"]["level_section"]
list_field = TWO["THRIFT"]["list_field"]
metadata = TWO["MIXED"]["metadata"]

LEAN = EVENTS["LEAN"].split("\nprivate def checkReframe", 1)[0].replace(
    "Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.Defs",
    "Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.Defs",
) + """
open Silmaril.Formats.Arrow.RecursiveSchema (Schema)
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList (openFile)
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows (readAll)
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer (Input Limits emit certify)
private abbrev WriteError := Parquet.RecursiveSchema.TwoList.Writer.Error

set_option maxRecDepth 8192

private def writeFile (folder : System.FilePath) (label : String) (input : Input) : IO Unit := do
  let output ← take (emit {} input)
  let source ← take (openFile {} output.bytes)
  let rows ← take (readAll {} source.schema)
  unless rows == input.groups do throw (IO.userError "logical row groups differ")
  let fields := input.schema.fields.map fun field =>
    (Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.fieldName field, field)
  checkFile output.bytes fields input.groups
  IO.FS.writeBinFile (folder / (label ++ ".parquet")) output.bytes.data

private def deny {α : Type} (expected : WriteError) (result : Except WriteError α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"unexpected acceptance, expected {reprStr expected}")
  | .error actual =>
    unless actual = expected do throw (IO.userError s!"expected {reprStr expected}, got {reprStr actual}")

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
        for bits in range(8):
            nullable = tuple(bool(bits & (1 << bit)) for bit in range(3))
            yield (f"signed_{width}_{bits}", schema_for(nullable, width), nullable, width,
                   samples(nullable, width), True)
    nullable = (True, True, True)
    schema = schema_for(nullable, 64)
    yield "schema_only", schema, nullable, 64, [], False
    alternate = pa.schema([pa.field("series_λ", pa.list_(pa.field("inner",
                      pa.list_(pa.field("word", pa.int64(), True)), True)), True)])
    first, second = samples(nullable, 64)
    yield "empty_group_no_crc", alternate, nullable, 64, [first, [], second], False


def inspect(wire, schema, nullable, width, groups, crc):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.equals(schema, check_metadata=True)
    assert parquet.num_row_groups == len(groups)
    assert parquet.metadata.num_rows == sum(map(len, groups))
    footer = metadata(wire)
    entries = list_field(footer, 2)
    outer, inner, leaf = nullable
    outer_field = schema.field(0)
    inner_field = outer_field.type.value_field
    path = [outer_field.name, "list", inner_field.name, "list", inner_field.type.value_field.name]
    signed = 1 if width == 32 else 2
    assert footer[1][1] == 1 and footer[3][1] == sum(map(len, groups))
    assert len(entries) == 6 and entries[0][4][1] == b"schema" and entries[0][5][1] == 1
    assert [entry[4][1].decode() for entry in entries[1:]] == path
    assert [entry[3][1] for entry in entries[1:]] == [int(outer), 2, int(inner), 2, int(leaf)]
    assert [entry[5][1] for entry in entries[1:5]] == [1, 1, 1, 1]
    assert [entries[i][6][1] for i in (1, 3)] == [3, 3]
    assert [list(entries[i][10][1]) for i in (1, 3)] == [[3], [3]]
    assert set(entries[5]) == {1, 3, 4} and entries[5][1][1] == signed

    row_groups = list_field(footer, 4)
    columns = list(V2["columns"](wire))
    assert len(row_groups) == len(columns) == len(groups)
    offset = 4
    maximum = TWO["thresholds"](nullable)[2]
    fmt = "<i" if width == 32 else "<q"
    for group, (position, column, lo, hi) in enumerate(columns):
        assert position == (group, 0) and lo == offset
        row_group = row_groups[group]
        assert row_group[2][1] == hi - lo and row_group[3][1] == len(groups[group])
        # The footer contains only the ordinary column metadata, with no
        # dictionary, index, statistics or alternate page offsets.
        assert set(list_field(row_group, 1)[0]) == {2, 3}
        assert set(column) == {1, 2, 3, 4, 5, 6, 7, 9}
        assert column[1][1] == signed and list_field(column, 2) == [0, 3]
        assert [part.decode() for part in list_field(column, 3)] == path
        assert column[4][1] == 0 and column[6][1] == column[7][1] == hi - lo and column[9][1] == lo
        assert parquet.read_row_group(group).column(0).to_pylist() == groups[group]

        [(header_at, header, body_at, body)] = FRAMES(wire, lo, hi)
        assert header_at == lo and body_at + len(body) == hi
        assert header[1][1] == 0 and header[2][1] == header[3][1] == len(body)
        if crc:
            assert header[4][1] & 0xffffffff == zlib.crc32(body)
        else:
            assert 4 not in header
        expected = expected_slots(groups[group], nullable)
        count = len(expected)
        assert column[5][1] == count and [header[5][1][i][1] for i in range(1, 5)] == [count, 0, 3, 3]
        reps, rest = level_section(body, 2, count)
        defs, suffix = level_section(rest, maximum, count)
        words = iter(word for word, in struct.iter_unpack(fmt, suffix))
        observed = [(rep, definition, next(words) if definition == maximum else None)
                    for rep, definition in zip(reps, defs, strict=True)]
        assert next(words, None) is None and observed == expected
        assert (not reps or reps[0] == 0) and reps.count(0) == len(groups[group])
        rep_bytes = b"".join(bytes((2, rep)) for rep, _, _ in expected)
        def_bytes = b"".join(bytes((2, definition)) for _, definition, _ in expected)
        word_bytes = b"".join(struct.pack(fmt, word) for _, _, word in expected if word is not None)
        assert body == struct.pack("<I", len(rep_bytes)) + rep_bytes + struct.pack("<I", len(def_bytes))             + def_bytes + word_bytes
        offset = hi
    assert wire[:4] == wire[-4:] == b"PAR1"
    assert offset == len(wire) - 8 - struct.unpack("<I", wire[-8:-4])[0]


def verify(scratch):
    code = [LEAN, *V1["ENTRY"]]
    positives = list(cases())
    for label, schema, _, width, groups, crc in positives:
        code.append(f'  writeFile folder "{label}" {input_term(schema, groups, width, crc)}')

    nullable = (True, True, True)
    schema = schema_for(nullable, 32)
    groups = samples(nullable, 32)
    valid = input_term(schema, groups, 32)
    slots = [len(expected_slots(group, nullable)) for group in groups]
    refusals = [
        f'  refuse (.groupLimit 2) {{ maxGroups := 1 }} {valid}',
        f'  refuse (.totalRowLimit {sum(map(len, groups))}) {{ maxTotalRows := 0 }} {valid}',
        f'  refuse (.rowLimit 0 {len(groups[0])}) {{ chunk.maxRows := 0 }} {valid}',
        f'  refuse (.slotLimit 0 {slots[0]}) {{ chunk.maxSlots := 0 }} {valid}',
        f'  refuse (.slotLimit 0 {slots[0]}) {{ chunk.levels := ⟨0, 1024⟩ }} {valid}',
        f'  refuse (.totalSlotLimit 1 {sum(slots)}) {{ maxTotalSlots := {slots[0]} }} {valid}',
        f'  refuse (.pageLimit 0) {{ chunk.framing.maxPages := 0 }} {valid}',
        f'  refuse (.levelLimit 0) {{ chunk.levels := ⟨1024, 0⟩ }} {valid}',
        f'  refuse (.bodyLimit 0) {{ chunk.maxBodyBytes := 0 }} {valid}',
        f'  refuse (.headerLimit 0) {{ chunk.framing.maxHeaderBytes := 0 }} {valid}',
        f'  refuse (.chunkLimit 0) {{ chunk.maxChunkBytes := '
        f'{8 + 4 * slots[0] + 4 * sum(word is not None for _, _, word in expected_slots(groups[0], nullable))} }} {valid}',
        f'  refuse (.schema .fileLimit) {{ schema.maxFileBytes := 11 }} {valid}',
        f'  refuse (.schema (.compact .byteLimit)) {{ schema.snapshot.footer.maxFooterBytes := 0 }} {valid}',
        f'  refuse (.schema .fieldLimit) {{ schema.maxFields := 5 }} {valid}',
        f'  refuse (.declaration) {{}} ({{ ({valid} : Input) with schema := ⟨[]⟩ }})',
        f'  refuse (.declaration) {{}} ({{ ({valid} : Input) with schema := ⟨['
        f'{field_term(schema.field(0)).replace("(some " + json.dumps("series") + ")", "none", 1)}]⟩ }})',
        f'  refuse (.projection 0) {{}} ({{ ({valid} : Input) with groups := [⟨1, '
        '[[some (.list [some (.list [some (.int64 7)])])]]⟩] })',
        f'  refuse (.projection 0) {{}} {input_term(schema_for((False, False, False), 32), [[[None]]], 32)}',
        f'  refuse (.rowCount 0 2 1) {{}} ({{ ({valid} : Input) with groups := [⟨2, [[none]]⟩] }})',
        f'  refuseReadback {valid}',
    ]
    code.extend(refusals)
    V2["run_lean"](scratch, "TwoListWriter.lean", code)
    emitted = {}
    for label, schema, nullable, width, groups, crc in positives:
        wire = (scratch / f"{label}.parquet").read_bytes()
        inspect(wire, schema, nullable, width, groups, crc)
        emitted[label] = wire
    print(f"Checked {len(emitted)} native Lean files, {sum(len(item[4]) for item in positives)} original V1 pages, "
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
