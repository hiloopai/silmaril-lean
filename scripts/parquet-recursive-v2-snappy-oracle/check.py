"""Check the original Snappy V2 sections, strict failures and native IPC."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
V2 = runpy.run_path(str(HERE.parent / "parquet-recursive-v2-oracle/check.py"))
BRIDGE, SCHEMA, STREAM, CHUNK, THRIFT, MIXED, FRAMES, fingerprints, lst = (
    V2[key] for key in ("BRIDGE", "SCHEMA", "STREAM", "CHUNK", "THRIFT", "MIXED", "FRAMES",
                         "fingerprints", "lst")
)


def write(schema, groups, *, compression="SNAPPY", page_version="2.0"):
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, compression=compression, use_dictionary=False,
                          use_compliant_nested_type=False, store_schema=False,
                          data_page_version=page_version, write_page_checksum=True,
                          write_page_index=False, write_statistics=True,
                          data_page_size=256, write_batch_size=8, max_rows_per_page=12) as writer:
        for rows in groups:
            writer.write_table(pa.Table.from_pylist(rows, schema=schema))
    return sink.getvalue().to_pybytes()


def raw_chunks(wire):
    return {key: list(FRAMES(wire, start, stop)) for key, _, start, stop in V2["columns"](wire)}


def resolved(header):
    return header[8][1].get(7, (None, True))[1]


def level_size(header):
    return header[8][1][5][1] + header[8][1][6][1]


def header_raw_size(header):
    return header[2][1] - level_size(header)


def encode(header, body, *, crc=True):
    header[3] = TType.I32, len(body)
    if crc:
        value = zlib.crc32(body)
        header[4] = TType.I32, value if value < 2**31 else value - 2**32
    return THRIFT["encode"](header) + body


def pack_chunks(wire, chunks):
    """Test-only carrier with distinct header-inclusive stored and raw extents."""
    raw_extents = {
        key: sum(payload - byte + header[2][1]
                 for byte, header, payload, _ in FRAMES(data, 0, len(data)))
        for key, data in chunks.items()
    }
    packed = V2["wrap_pages"](wire, chunks)
    footer = MIXED["metadata"](packed)
    for group, row_group in enumerate(THRIFT["list_field"](footer, 4)):
        spans = THRIFT["list_field"](row_group, 1)
        for column, chunk in enumerate(spans):
            chunk[3][1][6] = TType.I64, raw_extents[group, column]
        row_group[2] = TType.I64, sum(raw_extents[group, col] for col in range(len(spans)))
    return SCHEMA["pack"](packed, footer)


def replace_page(wire, location, edit):
    """Splice one labeled test frame and recompute both footer size vectors."""
    target_group, target_column, target_page = location
    chunks = {}
    for key, _, start, stop in V2["columns"](wire):
        if key == (target_group, target_column):
            frames = list(FRAMES(wire, start, stop))
            byte, header, payload, body = frames[target_page]
            changed = edit(header, body)
            chunks[key] = wire[start:byte] + changed + wire[payload + len(body):stop]
        else:
            chunks[key] = wire[start:stop]
    return pack_chunks(wire, chunks)


def fixture_edits(wire, where):
    def omitted(header, body):
        assert header[8][1].pop(7) == (TType.BOOL, True)
        return encode(header, body)

    def trailing(header, body):
        return encode(header, body + b"\0")

    def truncated(header, body):
        return encode(header, body[:level_size(header)] + b"\x01")

    def short_output(header, body):
        return encode(header, body[:level_size(header)] + b"\0")

    def wrong_raw_size(header, body):
        header[2] = TType.I32, header[2][1] + 1
        return encode(header, body)

    def bad_crc(header, body):
        return encode(header, body[:-1] + bytes([body[-1] ^ 1]), crc=False)

    def crc_over_decoded(header, body):
        sizes = level_size(header)
        raw = pa.Codec("snappy").decompress(body[sizes:], header_raw_size(header)).to_pybytes()
        digest = zlib.crc32(body[:sizes] + raw)
        header[4] = TType.I32, digest if digest < 2**31 else digest - 2**32
        return encode(header, body, crc=False)

    def bad_extent(header, body):
        assert level_size(header) > 0
        header[2] = TType.I32, level_size(header) - 1
        return encode(header, body)

    changed = {edit.__name__: replace_page(wire, where, edit) for edit in
               (omitted, trailing, truncated, short_output, wrong_raw_size, bad_crc, crc_over_decoded, bad_extent)}
    footer = MIXED["metadata"](wire)
    meta = THRIFT["column_metadata"](footer, where[0], where[1])
    meta[6] = TType.I64, meta[6][1] + 1
    changed["wrong_chunk_total"] = SCHEMA["pack"](wire, footer)
    return changed


def lean_state(observation):
    slot, row, live = observation
    return f"⟨{slot}, {row}, {str(live).lower()}⟩"


def verify(scratch):
    _, samples, _ = SCHEMA["fixtures"]()
    schema, rows = samples["nullable_lists"]
    values = [{"packet": {"flag": 0, "items": [
        {"lo": -7, "nested": {"hi": -2**63}}] * 9}, "seq": 2**40}] * 16
    groups = [rows[:3], values + rows[3:]]
    native = write(schema, groups)
    genuine = {
        "nested_snappy": native,
        "mixed_snappy": write(schema, groups, compression={
            "packet.items.list.élément.lo": "SNAPPY",
            "packet.items.list.élément.nested.hi": "SNAPPY",
        }),
        "v1_snappy": write(schema, [rows], page_version="1.0"),
        "pageless_snappy": write(schema, [rows[:3], [], rows[3:]]),
        "gzip_v2": write(schema, [rows], compression="GZIP"),
    }
    for key, metadata, start, stop in V2["columns"](genuine["pageless_snappy"]):
        if key[0] == 1:
            assert [metadata[index][1] for index in (4, 5, 6, 7, 9)] == [1, 0, 0, 0, 0]
            assert stop == start == 0

    assert [metadata[4][1] for _, metadata, _, _ in V2["columns"](genuine["mixed_snappy"])] == [1, 1, 0, 0] * 2
    frames = raw_chunks(native)
    compressed = [(group, col, ordinal) for (group, col), pages in frames.items()
                  for ordinal, (_, header, _, _) in enumerate(pages) if resolved(header)]
    raw = [(group, col, ordinal) for (group, col), pages in frames.items()
           for ordinal, (_, header, _, _) in enumerate(pages) if not resolved(header)]
    assert compressed and raw
    target = next(key for key in compressed
                  if key[0] == 1 and key[1] == 0 and
                  frames[key[:2]][key[2]][1][2][1] > frames[key[:2]][key[2]][1][3][1])
    labeled = fixture_edits(native, target)
    files = genuine | labeled
    for name, wire in files.items():
        (scratch / f"{name}.parquet").write_bytes(wire)
    start = ["public def main (args : List String) : IO Unit := do",
             '  let [folder] := args | throw (IO.userError "expected fixture folder")']
    code, bridge = [V2["LEAN"], *start], [BRIDGE["LEAN"], *start]
    captured = {}
    for label in ("nested_snappy", "mixed_snappy", "omitted"):
        codec = None if label == "mixed_snappy" else 1
        seen = list(V2["capture"](files[label], schema, groups[0] + groups[1], codec=codec))
        captured[label] = {(column.group, column.index): column for column, _ in seen }
        for column, spans in seen:
            code.append(CHUNK["check_term"](column, label))
            code.append(f'  spans (← load folder "{label}") {column.group} {column.index} {lst(spans)}')
        fields, observations, counts = BRIDGE["observed"](files[label])
        assert counts == [3, 18]
        bridge.append(f'  emit folder "{label}" (← load folder "{label}") {fields} {observations}')

    group, column, ordinal = target
    before = lean_state(captured["nested_snappy"][group, column].pages[ordinal].before)
    path = json.dumps(captured["nested_snappy"][group, column].path, ensure_ascii=False)
    address = f"⟨{group}, {column}, {path}⟩"

    def page_error(label, cause, limits="{}"):
        byte = raw_chunks(files[label])[group, column][ordinal][0]
        error = f".page {address} ⟨{ordinal}, {byte}, {before}⟩ ({cause})"
        code.append(f'  refuse (← load folder "{label}") {group} {column} {limits} ({error})')
        return error

    _, header, _, stored = frames[group, column][ordinal]
    assert ordinal == 0, "the page-level budget probe must reach the target before any other page"
    page_error("nested_snappy", ".payload .outputLimit", f"{{ maxBodyBytes := {len(stored)} }}")
    page_error("nested_snappy", ".checksum .byteLimit", f"{{ maxBodyBytes := {len(stored) - 1} }}")
    page_error("trailing", ".payload (.trailingInput .snappy)")
    page_error("short_output", ".payload .outputSizeMismatch")
    late = page_error("truncated", ".payload (.malformed .snappy)")
    page_error("wrong_raw_size", f".v2SignedExtent {header_raw_size(header)+1} {header_raw_size(header)}")
    page_error("bad_extent", ".framing (.header .invalidV2Lengths)")
    for label in ("bad_crc", "crc_over_decoded"):
        _, crc_header, _, damaged = raw_chunks(files[label])[group, column][ordinal]
        page_error(label, f".checksum (.mismatch {crc_header[4][1] & 0xffffffff} {zlib.crc32(damaged)})")
    col = captured["nested_snappy"][group, column]
    raw_total = THRIFT["column_metadata"](MIXED["metadata"](native), group, column)[6][1]
    code.append(f'  refuse (← load folder "wrong_chunk_total") {group} {column} {{}} '
                f'(.chunk {address} ⟨{col.start}, {col.stop}⟩ (.uncompressedSize {raw_total+1} {raw_total}))')
    first_path = '["packet", "items", "list", "élément", "lo"]'
    code.extend([
        f'  bindFailure (← load folder "gzip_v2") 0 0 (.column ⟨0, 0, {first_path}⟩ (.codec 2))',
        '  deny (.original (.snapshot (.invalidMetadata .pageInterval))) (openFile {} (← load folder "pageless_snappy"))',
    ])

    expected = BRIDGE["observed"](native, limit=1)
    projected = BRIDGE["observed"](native, positions=[], limit=1)
    terminal = f".readError (.group 1 (.chunk ({late})))"
    bridge.extend([
        BRIDGE["check"]("Snappy late failure", 'direct (← load folder "truncated")', expected, terminal),
        BRIDGE["check"]("Snappy projected late failure", 'project (← load folder "truncated") []',
                        projected, terminal),
        f'  sourceFailure (← load folder "truncated") (.chunk ({late}))',
    ])
    V2["run_lean"](scratch, "Chunk.lean", code)
    V2["run_lean"](scratch, "Bridge.lean", bridge)
    ipc = {}
    for name in captured:
        parquet = pq.ParquetFile(pa.BufferReader(files[name]), page_checksum_verification=True)
        wire = (scratch / f"{name}.arrow").read_bytes()
        reader = pa.ipc.open_stream(wire)
        assert reader.schema == parquet.schema_arrow
        batches = list(reader)
        assert [batch.to_pylist() for batch in batches] == groups
        _, cursor = STREAM["metadata"](wire)
        for count in (3, 18):
            frame = STREAM["read_record"](wire, cursor)
            assert frame.rows == count
            cursor = frame.end
        assert wire[cursor:] == STREAM["EOS"]
        ipc[name] = wire
    pages = sum(len(col.pages) for fixture in captured.values() for col in fixture.values())
    print(f"Checked {pages} original pages including {len(compressed)} compressed and {len(raw)} raw "
          "in the all-Snappy input, three native IPC streams and twelve typed refusals")
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
