"""Assemble mixed chunks from pinned PyArrow and previously assembled LIST pages."""

from copy import deepcopy
from hashlib import sha256
from io import BytesIO
import os
from pathlib import Path
import runpy
import struct
import subprocess
import sys

from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
v1 = runpy.run_path(str(HERE.parent / "parquet-list-snappy-v1" / "Oracle.py"))
v2 = runpy.run_path(str(HERE.parent / "parquet-list-snappy-v2" / "Oracle.py"))
pa, pq, metadata, footer, compact, Frame, checksum, SNAPPY, SCHEMA = (
    v1[name] for name in ("pa", "pq", "metadata", "footer", "compact", "Frame", "checksum", "SNAPPY", "SCHEMA")
)
compact_header, read_fields, levels = (v2[name] for name in ("compact_header", "read_fields", "levels"))
FIRST = [None, [], v1["NATIVE"][0][2], v2["ROWS"][0][3]]
SECOND = [None, [], v1["NATIVE"][1][2], v2["ROWS"][1][3]]
CONTINUED = [None, [], [-7, None, 0, None], v2["ROWS"][1][3]]


def read_frames(raw):
    start, meta = metadata(raw)
    result = []
    cursor = 4
    for group in meta[4]:
        [chunk] = group[1]
        column = chunk[3]
        assert column[1] == 1 and column[3] == [b"items", b"list", b"element"] and column[4] == 1
        assert cursor == column[9]
        stop = cursor + column[7]
        assert cursor < stop <= start
        frames = []
        expanded = 0
        while cursor < stop:
            transport = TMemoryBuffer(raw[cursor:stop])
            header = read_fields(TCompactProtocol(transport), (5, 8))
            payload = cursor + transport.cstringio_buf.tell()
            end = payload + header[3]
            assert cursor < payload <= end <= stop
            assert header[1] in (0, 3)
            frames.append(Frame(cursor, payload, end, header, raw[payload:end]))
            expanded += payload - cursor + header[2]
            cursor = end
        assert expanded == group[2] == column[6]
        assert sum(info(frame.header)[1] for frame in frames) == column[5]
        result.append(frames)
    assert cursor == start
    return meta, start, result


def info(header):
    return header[5 if header[1] == 0 else 8]


def input_frames(name, filename):
    return read_frames((ROOT / f"data/parquet-list-snappy-{name}" / filename).read_bytes())


def assemble(meta, groups, row_counts):
    """Rebuild the exact local chunk and footer totals from the chosen frames."""
    meta = deepcopy(meta)
    data = bytearray(b"PAR1")
    for group, frames, rows in zip(meta[4], groups, row_counts, strict=True):
        column = group[1][0][3]
        column[9] = len(data)
        expanded = 0
        count = 0
        for header, body in frames:
            packed = compact_header(header)
            assert len(body) == header[3]
            data += packed + body
            expanded += len(packed) + header[2]
            count += info(header)[1]
        column[5], column[6], column[7] = count, expanded, len(data) - column[9]
        group[2], group[3] = expanded, rows
    meta[3] = sum(row_counts)
    packed = compact(footer, meta)
    return bytes(data) + packed + struct.pack("<I", len(packed)) + b"PAR1"


def decode_wire(frame):
    header, body = frame.header, frame.body
    count = info(header)[1]
    if header[1] == 0:
        assert header[5] == {1: count, 2: 0, 3: 3, 4: 3}
        expanded = SNAPPY.decompress(body, header[2]).to_pybytes()
        rep_length = struct.unpack_from("<I", expanded)[0]
        rep = expanded[4:4 + rep_length]
        definition_at = 4 + rep_length
        def_length = struct.unpack_from("<I", expanded, definition_at)[0]
        start = definition_at + 4
        definition = expanded[start:start + def_length]
        values = expanded[start + def_length:]
    else:
        v = header[8]
        assert v[4] == 0
        rep_length, def_length = v[6], v[5]
        rep = body[:rep_length]
        definition = body[rep_length:rep_length + def_length]
        values = body[rep_length + def_length:]
        if v.get(7, True):
            values = SNAPPY.decompress(values, header[2] - rep_length - def_length).to_pybytes()
        assert len(values) + rep_length + def_length == header[2]
    repetitions, definitions = levels(rep, 1, count), levels(definition, 2, count)
    signed = [value for (value,) in struct.iter_unpack("<i", values)]
    assert len(signed) == definitions.count(3)
    if header[1] == 3:
        assert not repetitions or repetitions[0] == 0
        assert info(header)[2] == count - len(signed)
        assert info(header)[3] == repetitions.count(0)
    return repetitions, definitions, signed


def reconstruct(pages):
    rows = []
    for repetitions, definitions, values in pages:
        physical = iter(values)
        for repetition, definition in zip(repetitions, definitions, strict=True):
            if repetition == 0:
                rows.append(None if definition == 0 else [])
            if definition >= 2:
                rows[-1].append(None if definition == 2 else next(physical))
    return rows


def inspect(label, raw, expected):
    meta, footer_at, groups = read_frames(raw)
    assert meta[3] == sum(map(len, expected))
    print(f"{label} SHA-256 {sha256(raw).hexdigest()}, footer [{footer_at}, {len(raw) - 8})")
    for ordinal, (frames, rows) in enumerate(zip(groups, expected, strict=True)):
        decoded = []
        for index, frame in enumerate(frames):
            assert frame.header[4] == checksum(frame.body)
            repetitions, definitions, values = decode_wire(frame)
            decoded.append((repetitions, definitions, values))
            print(f"  group {ordinal} page {index} type {frame.header[1]}, header @{frame.offset}, "
                  f"payload [{frame.payload}, {frame.stop}), slots {len(repetitions)}, "
                  f"row starts {repetitions.count(0)}, null slots {len(repetitions) - len(values)}")
        assert reconstruct(decoded) == rows
        assert meta[4][ordinal][3] == len(rows)
    reader = pq.ParquetFile(BytesIO(raw), page_checksum_verification=True)
    assert reader.schema_arrow == SCHEMA
    assert reader.num_row_groups == len(expected)
    actual = [reader.read_row_group(i, use_threads=False)[0].to_pylist() for i in range(reader.num_row_groups)]
    assert actual == expected
    print("  independent Thrift/level reconstruction and PyArrow agree")
    return groups


def pair(frame):
    return frame.header, frame.body


def make(directory):
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    directory.mkdir(parents=True, exist_ok=True)
    print(f"PyArrow {pa.__version__}")
    meta, _, a = input_frames("v1", "native-crc-v1.parquet")
    _, _, b = input_frames("v2", "native-crc-v2.parquet")
    _, _, c = input_frames("v1", "assembled-continuation-v1.parquet")

    first = list(map(pair, [a[0][0], b[0][1], a[0][2], b[0][3]]))
    second = list(map(pair, [b[1][0], a[1][1], a[1][2], b[1][3]]))
    main = assemble(meta, [first, second], [4, 4])
    (directory / "assembled-mixed.parquet").write_bytes(main)
    frames = inspect("assembled-mixed.parquet", main, [FIRST, SECOND])

    continuation = pair(c[1][3])
    v1_run = list(map(pair, [b[1][0], b[1][1], a[1][2]])) + [continuation, pair(b[1][3])]
    continued = assemble(meta, [first, v1_run], [4, 4])
    (directory / "assembled-v1-continuation.parquet").write_bytes(continued)
    inspect("assembled-v1-continuation.parquet", continued, [FIRST, CONTINUED])

    v2_header, v2_body = deepcopy(second[-1][0]), second[-1][1]
    assert v2_body[:2] == b"\x03\xfe"
    changed = v2_body[:1] + b"\xff" + v2_body[2:]
    v2_header[4] = checksum(changed)
    v2_starts_mid_row = assemble(meta, [first, second[:-1] + [(v2_header, changed)]], [4, 4])
    (directory / "assembled-starts-v2-mid-row.parquet").write_bytes(v2_starts_mid_row)

    v2_run = list(map(pair, b[1][:3]))
    after_v2 = assemble(meta, [first, v2_run + [continuation]], [4, 3])
    (directory / "assembled-continues-after-v2.parquet").write_bytes(after_v2)

    zero_body = SNAPPY.compress(bytes(8)).to_pybytes()
    zero_header = {1: 0, 2: 8, 3: len(zero_body), 4: checksum(zero_body), 5: {1: 0, 2: 0, 3: 3, 4: 3}}
    across_empty = assemble(meta, [first, v2_run + [(zero_header, zero_body), continuation]], [4, 3])
    (directory / "assembled-continues-through-empty.parquet").write_bytes(across_empty)

    for name, group, index in [("v1-crc", 1, 2), ("v2-crc", 1, 3)]:
        frame = frames[group][index]
        damaged = bytearray(main)
        damaged[frame.payload] ^= 0x80
        assert checksum(damaged[frame.payload:frame.stop]) != frame.header[4]
        reference = pq.ParquetFile(BytesIO(damaged), page_checksum_verification=True)
        assert reference.read_row_group(0, use_threads=False)[0].to_pylist() == FIRST
        try:
            reference.read_row_group(1, use_threads=False)
        except OSError as error:
            assert "CRC" in str(error)
        else:
            raise AssertionError("expected the mixed chunk CRC to fail")
        (directory / f"mutated-{name}.parquet").write_bytes(damaged)
    return frames


def run(directory):
    directory = directory.resolve()
    frames = make(directory)
    driver = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
              "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
    for name, expected in [("assembled-mixed", [FIRST, SECOND]), ("assembled-v1-continuation", [FIRST, CONTINUED])]:
        source = directory / f"{name}.parquet"
        assert source.read_bytes() == (ROOT / "data/parquet-list-snappy-mixed" / source.name).read_bytes()
        output = directory / f"{name}.arrows"
        subprocess.run([*driver, "write", str(source), str(output)], cwd=ROOT, check=True)
        raw = output.read_bytes()
        with pa.ipc.open_stream(raw) as reader:
            assert reader.schema == SCHEMA
            assert [batch.column(0).to_pylist() for batch in reader] == expected
        messages = list(pa.ipc.MessageReader.open_stream(raw))
        assert [message.type for message in messages] == ["schema", "record batch", "record batch"]
        assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
        eos_at = sum(8 + message.metadata.size + (message.body.size if message.body else 0) for message in messages)
        assert raw[eos_at:] == bytes.fromhex("ff ff ff ff 00 00 00 00")
        print(f"{output.name} SHA-256 {sha256(raw).hexdigest()}, EOS [{eos_at}, {len(raw)})")
    cases = [("starts-v2-mid-row", 3, "assembled"), ("continues-after-v2", 3, "assembled"),
             ("continues-through-empty", 4, "assembled"), ("v1-crc", 2, "mutated"), ("v2-crc", 3, "mutated")]
    for label, index, kind in cases:
        source = directory / f"{kind}-{label}.parquet"
        raw = source.read_bytes()
        _, _, original = read_frames(raw)
        offset = original[1][index].offset
        print(f"{source.name} SHA-256 {sha256(raw).hexdigest()}")
        verdict = subprocess.check_output(
            [*driver, "refuse", label, str(source), str(index), str(offset)], cwd=ROOT, text=True
        )
        print(verdict.strip())
    budget = sum(frame.header[2] for group in frames for frame in group) - 1
    assembled_path = directory / "assembled-mixed.parquet"
    verdict = subprocess.check_output(
        [*driver, "budget", str(assembled_path), str(frames[1][3].offset), str(budget)], cwd=ROOT, text=True
    )
    print(verdict.strip())


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--fixtures":
        make(Path(sys.argv[2]))
    else:
        run(Path(sys.argv[1]))
