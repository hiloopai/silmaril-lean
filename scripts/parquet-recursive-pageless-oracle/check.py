"""Check original PyArrow pageless row groups and complete Lean IPC output."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import struct
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
V2 = runpy.run_path(str(HERE.parent / "parquet-recursive-v2-oracle/check.py"))
BRIDGE, CHUNK, SCHEMA, STREAM, THRIFT = (V2[name] for name in ("BRIDGE", "CHUNK", "SCHEMA", "STREAM", "THRIFT"))
MIXED, fingerprints, lst = (V2[name] for name in ("MIXED", "fingerprints", "lst"))

LEAN = BRIDGE["LEAN"] + """\

private def emptyGroup (input : Bytes) (index : Nat) (paths : List (List String)) : IO Unit := do
  let src ← take (openFile {} input)
  let some group := src.snapshot.groupAt index | throw (IO.userError "missing original group")
  unless src.snapshot.groupCount = 3 ∧ src.snapshot.admitsPageLessRecursive group = true ∧
      group.numRows = 0 ∧ group.totalByteSize = 0 ∧ group.fileOffset = some 0 ∧
      group.totalCompressedSize = some 0 ∧ group.columns.length = paths.length do
    throw (IO.userError "original empty group metadata differs")
  for (path, column) in paths.zipIdx do
    let binding ← take (Parquet.RecursiveSchema.Repeated.Chunk.bindChunk src.schema index column)
    let seen ← take (Parquet.RecursiveSchema.Repeated.Chunk.read
      { maxChunkBytes := 0, maxRows := 0, maxSlots := 0, framing.maxPages := 0 } binding)
    let m := binding.chunk.metadata
    unless binding.span? = none ∧ m.pathInSchema = path ∧ binding.leaf.site.location.path = path ∧
        m.dataPageOffset = 0 ∧ m.totalCompressedSize = 0 ∧ m.totalUncompressedSize = 0 ∧
        m.numValues = 0 ∧ m.encodings = [3] ∧ seen.pages.isEmpty ∧ seen.levels.isEmpty do
      throw (IO.userError "pageless column disagrees with original metadata")

private def rowGroups (input : Bytes) (wanted : List Observation) : IO Unit := do
  let src ← take (openFile {} input)
  let groups ← take (Parquet.RecursiveSchema.Repeated.Rows.readAll {} src.schema)
  unless groups == wanted do throw (IO.userError "rows or group boundaries differ")

private def strictRefusal (input : Bytes) : IO Unit :=
  refuse (.invalidMetadata .pageInterval) (Parquet.Snapshot.check (Failure := Unit) {} input)
"""


def produce(schema, groups, page_version, statistics):
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, compression="NONE", use_dictionary=False,
                          use_compliant_nested_type=False, store_schema=False,
                          data_page_version=page_version, write_page_checksum=True,
                          write_page_index=False, write_statistics=statistics) as writer:
        for rows in groups:
            writer.write_table(pa.Table.from_pylist(rows, schema=schema))
    return sink.getvalue().to_pybytes()


def raw_groups(wire):
    return THRIFT["list_field"](MIXED["metadata"](wire), 4)


def inspect(wire, page_tag):
    metadata = MIXED["metadata"](wire)
    assert metadata[1][1] == 2 and metadata[3][1] == 5
    assert metadata[6][1] == b"parquet-cpp-arrow version 26.0.1"
    footer_bytes, = struct.unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - footer_bytes
    groups = raw_groups(wire)
    assert [group[3][1] for group in groups] == [3, 0, 2]
    empty = groups[1]
    assert list(empty) == [1, 2, 3, 5, 6]
    assert [empty[key][1] for key in (2, 3, 5, 6)] == [0, 0, 0, 0]
    paths = []
    cursor = 4
    for ordinal, group in enumerate(groups):
        group_paths = []
        for chunk in THRIFT["list_field"](group, 1):
            col = chunk[3][1]
            group_paths.append((col[1][1], THRIFT["list_field"](col, 3)))
            start, stop = MIXED["column_extent"](col)
            if ordinal == 1:
                assert list(chunk) == [2, 3] and chunk[2][1] == 0
                assert list(col) == [1, 2, 3, 4, 5, 6, 7, 9, 13]
                assert THRIFT["list_field"](col, 2) == [3]
                assert [col[key][1] for key in (4, 5, 6, 7, 9)] == [0, 0, 0, 0, 0]
                assert col[13] == (TType.LIST, (TType.STRUCT, []))
                assert start == stop == 0
            else:
                assert start == cursor and start < stop
                frames = list(CHUNK["FRAMES"](wire, start, stop))
                assert frames and all(header[1][1] == page_tag and 4 in header
                                      for _, header, _, _ in frames)
                cursor = stop
        if ordinal == 0:
            paths = group_paths
        else:
            assert group_paths == paths
    assert cursor == footer_start
    return [[component.decode("utf-8") for component in path] for _, path in paths]


def edits(wire):
    i64 = lambda value: (TType.I64, value)
    i32 = lambda value: (TType.I32, value)
    interval = ".original (.snapshot (.invalidMetadata .pageInterval))"
    raw = ".pageLess (.raw (.emptyMetadata 1))"
    output, expected = {}, {}

    def edit(name, refusal, change):
        footer = MIXED["metadata"](wire)
        group = THRIFT["list_field"](footer, 4)[1]
        chunk = THRIFT["list_field"](group, 1)[0]
        change(group, chunk, chunk[3][1])
        output[name] = SCHEMA["pack"](wire, footer)
        expected[name] = refusal

    for name, key in (("group_rows", 3), ("group_size", 2), ("group_offset", 5), ("group_compressed", 6)):
        edit(name, interval, lambda group, _, __: group.__setitem__(key, i64(1)))
    for name, key in (("slots", 5), ("uncompressed_size", 6), ("compressed_size", 7),
                      ("data_offset", 9), ("dictionary_offset", 11)):
        edit(name, interval, lambda _, __, col: col.__setitem__(key, i64(4)))
    edit("chunk_offset", interval, lambda _, chunk, __: chunk.__setitem__(2, i64(4)))
    edit("empty_external_path", raw, lambda _, chunk, __: chunk.__setitem__(1, (TType.STRING, b"")))
    edit("index", interval, lambda _, chunk, __: chunk.update({4: i64(4), 5: i32(1)}))
    edit("extra_metadata", raw, lambda _, __, col: col.__setitem__(12, (TType.STRUCT, {})))
    edit("wrong_type", ".original (.snapshot (.invalidMetadata .columns))", lambda _, __, col: col.__setitem__(1, i32(2)))
    edit("wrong_path", ".original (.snapshot (.invalidMetadata .columns))", lambda _, __, col:
         col.__setitem__(3, (TType.LIST, (TType.STRING, [b"unrelated"]))))
    size, = struct.unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - size
    output["undeclared_byte"] = wire[:footer_start] + b"\0" + wire[footer_start:]
    expected["undeclared_byte"] = f".pageLess (.dataExtent {footer_start + 1} {footer_start})"
    return output, expected


def verify(scratch):
    _, samples, _ = SCHEMA["fixtures"]()
    schema, rows = samples["nullable_lists"]
    groups = [rows[:3], [], rows[3:]]
    genuine = {
        f"pyarrow_{page}_{stats}": produce(schema, groups, version, stats == "stats")
        for page, version in (("v1", "1.0"), ("v2", "2.0"))
        for stats in ("stats", "no_stats")
    }
    labeled, refusals = edits(genuine["pyarrow_v2_stats"])
    for name, wire in (genuine | labeled).items():
        (scratch / f"{name}.parquet").write_bytes(wire)
    code = [LEAN, "public def main (args : List String) : IO Unit := do",
            '  let [folder] := args | throw (IO.userError "expected fixture folder")']
    for name, wire in genuine.items():
        paths = inspect(wire, 0 if "v1" in name else 3)
        lean_paths = lst(lst(json.dumps(item, ensure_ascii=False) for item in path) for path in paths)
        fields, rows, counts = BRIDGE["observed"](wire)
        assert counts == [3, 0, 2]
        code.extend([
            f'  let {name} ← load folder "{name}"',
            f'  strictRefusal {name}',
            f'  emptyGroup {name} 1 {lean_paths}',
            f'  rowGroups {name} {rows}',
            f'  emit folder "{name}" {name} {fields} {rows}',
            BRIDGE["check"](name, f"project {name} []", BRIDGE["observed"](wire, positions=[])),
        ])
    for name, cause in refusals.items():
        code.append(f'  refuse ({cause}) (openFile {{}} (← load folder "{name}"))')
    V2["run_lean"](scratch, "Pageless.lean", code)

    ipc = {}
    for name, wire in genuine.items():
        raw = (scratch / f"{name}.arrow").read_bytes()
        original = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
        reader = pa.ipc.open_stream(raw)
        assert reader.schema == original.schema_arrow
        batches = list(reader)
        assert [batch.num_rows for batch in batches] == [3, 0, 2]
        for ordinal, batch in enumerate(batches):
            assert [col.to_pylist() for col in batch.columns] == [
                col.to_pylist() for col in original.read_row_group(ordinal).columns]
        _, cursor = STREAM["metadata"](raw)
        for count in (3, 0, 2):
            record = STREAM["read_record"](raw, cursor)
            assert record.rows == count
            cursor = record.end
        assert raw[cursor:] == STREAM["EOS"]
        ipc[name] = raw
    print(f"Checked {len(genuine)} genuine V1/V2 files, {len(ipc)} Lean IPC streams and {len(refusals)} typed edits")
    return {"genuine_parquet": fingerprints(genuine), "labeled_edits": fingerprints(labeled),
            "lean_ipc": fingerprints(ipc)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for kind, values in captured.items():
        assert values == pins[kind], f"{kind} fixture pins changed"


if __name__ == "__main__":
    main()
