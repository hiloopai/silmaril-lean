"""Independent native PyArrow V2 dictionary fallback and labeled controls."""

from copy import deepcopy
from hashlib import sha256
from io import BytesIO
import os
from pathlib import Path
import runpy
import struct
import subprocess
import sys

from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
v2 = runpy.run_path(str(HERE.parent / "parquet-list-snappy-dictionary-v2" / "Oracle.py"))
pa, pq, schema, snappy, metadata, frames_at, checksum, hybrid, replace_last = (
    v2[key] for key in ("pa", "pq", "SCHEMA", "SNAPPY", "metadata", "frames_at", "checksum",
                       "hybrid", "replace_last")
)
ROWS = [
    [None, [], [None, -2147483648, -2147483648], [-2147483648], [0, 1, 2, 3, 4, 5],
     [2147483647, None], [6] * 20, [7, None] * 16],
    [[], None, [None, -7, -7], [-7], [-1, 0, 1, 2, 3, 4],
     [-2147483648, None], [2147483647] * 20, [-8, None] * 16],
]


def produce(path):
    values = pa.array(sum(ROWS, []), type=schema.field(0).type)
    pq.write_table(pa.table({"items": values}, schema=schema), path, compression="SNAPPY",
                   use_dictionary=True, data_page_version="2.0", write_statistics=False,
                   write_page_checksum=True, row_group_size=8, write_batch_size=1,
                   data_page_size=1, max_rows_per_page=2, dictionary_pagesize_limit=8)
    return path.read_bytes()


def inspect(raw):
    footer, meta = metadata(raw)
    frames = frames_at(raw, footer, meta)
    reader = pq.ParquetFile(BytesIO(raw), page_checksum_verification=True)
    assert reader.schema_arrow == schema and reader.num_row_groups == len(ROWS)
    assert meta[3] == sum(map(len, ROWS))
    print(f"Native PyArrow {pa.__version__} SHA-256 {sha256(raw).hexdigest()}, footer [{footer}, {len(raw) - 8})")
    for group, (pages, expected) in enumerate(zip(frames, ROWS, strict=True)):
        assert reader.read_row_group(group, use_threads=False)[0].to_pylist() == expected
        assert all(frame.header[4] == checksum(frame.body) for frame in pages)
        dictionary, *data = pages
        words = snappy.decompress(dictionary.body, dictionary.header[2]).to_pybytes()
        entries = [value for (value,) in struct.iter_unpack("<i", words)]
        assert dictionary.header[7] == {1: len(entries), 2: 0, 3: False}
        assert entries == v2["expected_entries"](expected[:5])
        assert [page.header[8][4] for page in data] == [8] * 5 + [0] * 3
        print(f"  group {group} dictionary @{dictionary.offset}, signed entries {entries}")
        rows = []
        plain_flags = set()
        for i, page in enumerate(data, 1):
            h = page.header[8]
            rep, defs = h[6], h[5]
            level_end = rep + defs
            repetitions = hybrid(page.body[:rep], 1, h[1])
            definitions = hybrid(page.body[rep:level_end], 2, h[1])
            expected_bytes = page.header[2] - level_end
            assert repetitions[0] == 0 and repetitions.count(0) == h[3]
            assert h[1] - definitions.count(3) == h[2]
            scalars = page.body[level_end:]
            if h.get(7, True):
                scalars = snappy.decompress(scalars, expected_bytes).to_pybytes()
            assert len(scalars) == expected_bytes
            if h[4] == 8:
                width, runs = scalars[0], scalars[1:]
                indices = hybrid(runs, width, h[1] - h[2])
                assert all(index < len(entries) for index in indices)
                values = [entries[index] for index in indices]
            else:
                plain_flags.add(h[7])
                values = [value for (value,) in struct.iter_unpack("<i", scalars)]
            assert len(values) == definitions.count(3)
            ordered = iter(values)
            for r, d in zip(repetitions, definitions, strict=True):
                if r == 0:
                    rows.append(None if d == 0 else [])
                if d >= 2:
                    assert rows[-1] is not None
                    rows[-1].append(None if d == 2 else next(ordered))
            print(f"    page {i} @{page.offset}, rep [{page.payload}, {page.payload + rep}), "
                  f"def [{page.payload + rep}, {page.payload + level_end}), "
                  f"suffix [{page.payload + level_end}, {page.stop}), tag {h[4]}, "
                  f"compressed {h[7]}, slots/rows/nulls {h[1]}/{h[3]}/{h[2]}")
        assert rows == expected and plain_flags == {True, False}
    return frames


def mutate_tag(raw, frame, tag):
    transport = TMemoryBuffer(raw[frame.offset:frame.payload])
    protocol = TCompactProtocol(transport)
    protocol.readStructBegin()
    while True:
        _, kind, field = protocol.readFieldBegin()
        assert kind != TType.STOP
        if field == 8:
            assert kind == TType.STRUCT
            break
        protocol.skip(kind)
        protocol.readFieldEnd()
    protocol.readStructBegin()
    while True:
        _, kind, field = protocol.readFieldBegin()
        assert kind != TType.STOP
        if field == 4:
            assert kind == TType.I32
            offset = frame.offset + transport.cstringio_buf.tell()
            assert protocol.readI32() == frame.header[8][4]
            assert frame.offset + transport.cstringio_buf.tell() == offset + 1
            assert tag in (0, 8)
            return raw[:offset] + bytes([tag << 1]) + raw[offset + 1:]
        protocol.skip(kind)
        protocol.readFieldEnd()


def controls(raw, pages):
    last = pages[-1]
    reentry = mutate_tag(raw, last, 8)
    yield "reentry", reentry, len(pages) - 1, last.offset
    for label, page, payload_offset, baseline in (
        ("late-plain-crc", last, last.header[8][6] + last.header[8][5], raw),
        ("early-index-crc-before-reentry", pages[3], 0, reentry),
    ):
        damaged = bytearray(baseline)
        damaged[page.payload + payload_offset] ^= 0x80
        assert checksum(damaged[page.payload:page.stop]) != page.header[4]
        if label == "late-plain-crc":
            reference = pq.ParquetFile(BytesIO(damaged), page_checksum_verification=True)
            assert reference.read_row_group(0, use_threads=False)[0].to_pylist() == ROWS[0]
            try:
                reference.read_row_group(1, use_threads=False)
            except OSError as error:
                assert "CRC" in str(error)
            else:
                raise AssertionError("expected PyArrow to reject the stored CRC mismatch")
        yield label, bytes(damaged), pages.index(page), page.offset
    yield "missing-prefix", mutate_tag(raw, pages[1], 0), 1, pages[1].offset
    header = deepcopy(last.header)
    header[8][3] += 1
    yield "wrong-plain-rows", replace_last(raw, last, header, last.body), len(pages) - 1, last.offset


def run(out, mode):
    out.mkdir(parents=True, exist_ok=True)
    out = out.resolve()
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    input_path = out / "native-fallback-v2.parquet"
    raw = produce(input_path)
    frames = inspect(raw)
    if mode == "generate":
        return
    assert raw == (ROOT / "data/parquet-list-snappy-dictionary-fallback-v2" / input_path.name).read_bytes()
    driver = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
              "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
    output = out / "native-fallback-v2.arrows"
    subprocess.run([*driver, "write", str(input_path), str(output)], cwd=ROOT, check=True)
    ipc = output.read_bytes()
    with pa.ipc.open_stream(ipc) as reader:
        assert reader.schema == schema
        assert [batch.column(0).to_pylist() for batch in reader] == ROWS
    messages = list(pa.ipc.MessageReader.open_stream(ipc))
    assert [m.type for m in messages] == ["schema", "record batch", "record batch"]
    assert all(m.metadata_version == pa.ipc.MetadataVersion.V5 for m in messages)
    eos = sum(8 + m.metadata.size + (m.body.size if m.body else 0) for m in messages)
    assert ipc[eos:] == bytes.fromhex("ff ff ff ff 00 00 00 00")
    print(f"Lean Arrow SHA-256 {sha256(ipc).hexdigest()}, exact EOS [{eos}, {len(ipc)})")
    for label, damaged, ordinal, offset in controls(raw, frames[1]):
        provenance = "assembled" if label == "wrong-plain-rows" else "mutated"
        path = out / f"{provenance}-{label}.parquet"
        path.write_bytes(damaged)
        print(f"{path.name} SHA-256 {sha256(damaged).hexdigest()}")
        print(subprocess.check_output([*driver, "refuse", label, str(path), str(ordinal), str(offset)],
                                      cwd=ROOT, text=True).strip())


if __name__ == "__main__":
    run(Path(sys.argv[1]), sys.argv[2] if len(sys.argv) > 2 else "check")
