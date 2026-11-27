"""Pinned native Snappy V2 LIST differential and labeled assembled controls."""

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
v1 = runpy.run_path(str(HERE.parent / "parquet-list-snappy-v1" / "Oracle.py"))
pa, pq, metadata, footer, compact, Frame, checksum, SNAPPY, SCHEMA = (
    v1[name] for name in ("pa", "pq", "metadata", "footer", "compact", "Frame", "checksum", "SNAPPY", "SCHEMA")
)
idl = runpy.run_path(str(HERE.parent / "parquet-flat-snappy" / "Oracle.py"))
read_fields = idl["fields"]
ROWS = [[None, [], [-7, None], [-(1 << 31), (1 << 31) - 1]],
        [None, [], [None], [0] * 32 + [None] + [0] * 7]]


def compact_header(header):
    def write(protocol, mapping):
        protocol.writeStructBegin("")
        for tag, value in sorted(mapping.items()):
            if isinstance(value, dict):
                protocol.writeFieldBegin("", TType.STRUCT, tag)
                write(protocol, value)
            elif isinstance(value, bool):
                protocol.writeFieldBegin("", TType.BOOL, tag)
                protocol.writeBool(value)
            else:
                protocol.writeFieldBegin("", TType.I32, tag)
                protocol.writeI32(value)
            protocol.writeFieldEnd()
        protocol.writeFieldStop()
        protocol.writeStructEnd()

    buffer = TMemoryBuffer()
    write(TCompactProtocol(buffer), header)
    return buffer.getvalue()


def produce(path, checksums):
    values = pa.array([row for batch in ROWS for row in batch], type=SCHEMA.field(0).type)
    pq.write_table(pa.table({"items": values}, schema=SCHEMA), path, compression="SNAPPY",
                   use_dictionary=False, data_page_version="2.0", write_statistics=False,
                   write_page_checksum=checksums, row_group_size=4, write_batch_size=1,
                   max_rows_per_page=1, data_page_size=1)
    return path.read_bytes()


def frames_at(source, meta, footer_at):
    result = []
    cursor = 4
    for group in meta[4]:
        [chunk] = group[1]
        column = chunk[3]
        assert column[1] == 1 and column[3] == [b"items", b"list", b"element"] and column[4] == 1
        assert cursor == column[9]
        stop = cursor + column[7]
        assert cursor < stop <= footer_at
        frames = []
        while cursor < stop:
            transport = TMemoryBuffer(source[cursor:stop])
            header = read_fields(TCompactProtocol(transport), (8,))
            payload = cursor + transport.cstringio_buf.tell()
            end = payload + header[3]
            assert cursor < payload <= end <= stop
            assert header[1] == 3 and header[8][4] == 0
            frames.append(Frame(cursor, payload, end, header, source[payload:end]))
            cursor = end
        result.append(frames)
    assert cursor == footer_at
    return result


def levels(raw, width, count):
    actual = []
    cursor = 0
    while cursor < len(raw):
        header = 0
        shift = 0
        while True:
            digit = raw[cursor]
            cursor += 1
            header |= (digit & 127) << shift
            if digit < 128:
                break
            shift += 7
        run = header >> 1
        assert run > 0
        if header & 1:
            size = run * width
            assert cursor + size <= len(raw)
            word = int.from_bytes(raw[cursor:cursor + size], "little")
            actual.extend((word >> (index * width)) & ((1 << width) - 1) for index in range(run * 8))
            cursor += size
        else:
            assert len(actual) + run <= count and raw[cursor] < 1 << width
            actual += [raw[cursor]] * run
            cursor += 1
    assert count <= len(actual) < count + 8 and all(value == 0 for value in actual[count:])
    return actual[:count]


def expected_slots(row):
    if not row:
        return [0], [0 if row is None else 1], []
    return ([0] + [1] * (len(row) - 1), [2 if x is None else 3 for x in row],
            [x for x in row if x is not None])


def inspect(label, source, has_crc, missing_flag=False):
    footer_at, meta = metadata(source)
    assert meta[2] == [{3: 0, 4: b"schema", 5: 1},
                       {3: 1, 4: b"items", 5: 1, 6: 3, 10: {3: {}}},
                       {3: 2, 4: b"list", 5: 1}, {1: 1, 3: 1, 4: b"element"}]
    reader = pq.ParquetFile(BytesIO(source), page_checksum_verification=True)
    assert reader.schema_arrow == SCHEMA and reader.num_row_groups == len(ROWS)
    assert [reader.read_row_group(i, use_threads=False)[0].to_pylist()
            for i in range(reader.num_row_groups)] == ROWS
    frames = frames_at(source, meta, footer_at)
    assert meta[3] == sum(map(len, ROWS))
    print(f"{label} SHA-256 {sha256(source).hexdigest()}, footer [{footer_at}, {len(source) - 8})")
    flags = set()
    for ordinal, (group, pages, rows) in enumerate(zip(meta[4], frames, ROWS, strict=True)):
        assert group[3] == len(rows)
        assert group[1][0][3][5] == sum(frame.header[8][1] for frame in pages)
        for index, (frame, row) in enumerate(zip(pages, rows, strict=True)):
            header, body = frame.header, frame.body
            info = header[8]
            count, nulls, rows_in_page, _, def_size, rep_size = (info[tag] for tag in range(1, 7))
            prefix = rep_size + def_size
            assert prefix <= min(header[2], header[3])
            assert header.get(4) == (checksum(body) if has_crc else None)
            compressed = info.get(7, True)
            assert (7 not in info) == (missing_flag and (ordinal, index) == (1, 3))
            flags.add(compressed)
            reps = levels(body[:rep_size], 1, count)
            defs = levels(body[rep_size:prefix], 2, count)
            decoded_size = header[2] - prefix
            values = body[prefix:]
            if compressed:
                values = SNAPPY.decompress(values, decoded_size).to_pybytes()
            assert len(values) == decoded_size == 4 * (count - nulls)
            signed = [value for (value,) in struct.iter_unpack("<i", values)]
            assert (reps, defs, signed) == expected_slots(row)
            assert rows_in_page == reps.count(0) == 1 and nulls == sum(value < 3 for value in defs)
            print(f"  group {ordinal} page {index} header @{frame.offset}, "
                  f"rep [{frame.payload}, {frame.payload + rep_size}), "
                  f"def [{frame.payload + rep_size}, {frame.payload + prefix}), "
                  f"stored values [{frame.payload + prefix}, {frame.stop}) -> {decoded_size} bytes, "
                  f"flag {info.get(7, 'absent/default true')}, CRC {header.get(4)}, slots {count}, nulls {nulls}, rows {rows_in_page}")
    assert flags == {False, True}
    return frames


def assembled(source, replacement, group_rows=None):
    """Retain unaffected frames and rebuild the minimal checked footer."""
    footer_at, original = metadata(source)
    meta = deepcopy(original)
    data = bytearray(b"PAR1")
    for ordinal, (group, frames) in enumerate(zip(meta[4], frames_at(source, original, footer_at), strict=True)):
        column = group[1][0][3]
        column[9] = len(data)
        uncompressed = 0
        for index, frame in enumerate(frames):
            if (ordinal, index) in replacement:
                header, body = replacement[ordinal, index]
                prefix = compact_header(header)
                data += prefix + body
                uncompressed += len(prefix) + header[2]
            else:
                data += source[frame.offset:frame.stop]
                uncompressed += frame.payload - frame.offset + frame.header[2]
        column[6], column[7], group[2] = uncompressed, len(data) - column[9], uncompressed
    if group_rows is not None:
        meta[4][1][3] = group_rows
        meta[3] = sum(group[3] for group in meta[4])
    compact_footer = compact(footer, meta)
    return bytes(data) + compact_footer + struct.pack("<I", len(compact_footer)) + b"PAR1"


def make(out):
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    print(f"PyArrow {pa.__version__}")
    native = produce(out / "native-crc-v2.parquet", True)
    frames = inspect("native-crc-v2.parquet", native, True)
    optional = produce(out / "native-no-crc-v2.parquet", False)
    inspect("native-no-crc-v2.parquet", optional, False)

    last = frames[1][3]
    header = deepcopy(last.header)
    assert header[8].pop(7) is True
    default = assembled(native, {(1, 3): (header, last.body)})
    (out / "assembled-default-v2.parquet").write_bytes(default)
    inspect("assembled-default-v2.parquet", default, True, missing_flag=True)

    for label, offset in (("crc-level", last.payload),
                          ("crc-values", last.payload + last.header[8][5] + last.header[8][6])):
        changed = bytearray(native)
        changed[offset] ^= 0x80
        assert checksum(changed[last.payload:last.stop]) != last.header[4]
        reader = pq.ParquetFile(BytesIO(changed), page_checksum_verification=True)
        assert reader.read_row_group(0, use_threads=False)[0].to_pylist() == ROWS[0]
        try:
            reader.read_row_group(1, use_threads=False)
        except OSError as error:
            assert "CRC" in str(error)
        else:
            raise AssertionError("expected a late CRC failure")
        (out / f"mutated-{label}-v2.parquet").write_bytes(changed)

    for label in ("geometry", "level-split", "continued", "page-rows", "page-nulls", "page-slots"):
        header, body = deepcopy(last.header), last.body
        info = header[8]
        if label == "geometry":
            info[5] = header[3] + 1
        elif label == "level-split":
            info[6] += 1
            info[5] -= 1
        elif label == "continued":
            assert body[:2] == b"\x03\xfe"
            body = body[:1] + b"\xff" + body[2:]
            header[4] = checksum(body)
        elif label == "page-rows":
            info[3] += 1
        elif label == "page-nulls":
            info[2] -= 1
        else:
            info[1] += 1
        raw = assembled(native, {(1, 3): (header, body)})
        (out / f"assembled-{label}-v2.parquet").write_bytes(raw)

    (out / "assembled-group-rows-v2.parquet").write_bytes(assembled(native, {}, group_rows=5))
    return frames


def run(out):
    out = out.resolve()
    frames = make(out)
    driver = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
              "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
    for label in ("native-crc", "native-no-crc", "assembled-default"):
        source = out / f"{label}-v2.parquet"
        assert source.read_bytes() == (ROOT / "data/parquet-list-snappy-v2" / source.name).read_bytes()
        ipc = out / f"{label}-v2.arrows"
        subprocess.run([*driver, "write", str(source), str(ipc)], cwd=ROOT, check=True)
        raw = ipc.read_bytes()
        with pa.ipc.open_stream(raw) as reader:
            assert reader.schema == SCHEMA
            assert [batch.column(0).to_pylist() for batch in reader] == ROWS
        messages = list(pa.ipc.MessageReader.open_stream(raw))
        assert [message.type for message in messages] == ["schema", "record batch", "record batch"]
        assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
        eos = sum(8 + message.metadata.size + (message.body.size if message.body else 0) for message in messages)
        assert raw[eos:] == bytes.fromhex("ff ff ff ff 00 00 00 00")
        print(f"{ipc.name} SHA-256 {sha256(raw).hexdigest()}, EOS [{eos}, {len(raw)})")
    for label in ("crc-level", "crc-values", "geometry", "level-split", "continued", "page-rows", "page-nulls",
                  "page-slots", "group-rows", "budget"):
        family = "mutated" if label.startswith("crc-") else "assembled"
        source = out / ("native-crc-v2.parquet" if label == "budget" else f"{family}-{label}-v2.parquet")
        print(f"{source.name} SHA-256 {sha256(source.read_bytes()).hexdigest()}")
        answer = subprocess.check_output(
            [*driver, "refuse", label, str(source), str(frames[1][3].offset)], cwd=ROOT, text=True
        )
        print(answer.strip())


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--fixtures":
        make(Path(sys.argv[2]))
    else:
        run(Path(sys.argv[1]))
