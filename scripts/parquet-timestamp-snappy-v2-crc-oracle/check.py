"""Pin real Snappy PLAIN V2 checksums and verify native TIMESTAMP IPC."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
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
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PLAIN = runpy.run_path(str(HERE.parent / "parquet-timestamp-snappy-oracle/check.py"))
DICTIONARY = runpy.run_path(str(HERE.parent / "parquet-timestamp-snappy-dictionary-oracle/check.py"))
THRIFT = PLAIN["THRIFT"]


def checked_v2(wire, rows, unit, zone, nullable, checksum):
    footer_start = PLAIN["footer_start"](wire)
    memory = TMemoryBuffer(wire[footer_start:-8])
    footer = THRIFT["read_struct"](TCompactProtocol(memory))
    assert memory.cstringio_buf.tell() == len(wire) - 8 - footer_start
    _, leaf = THRIFT["list_field"](footer, 2)
    assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(nullable))
    assert leaf[4] == (TType.STRING, b"event_time")
    timestamp = leaf[10][1][8][1]
    assert timestamp[1] == (TType.BOOL, zone == "UTC")
    assert timestamp[2][1] == {{"ms": 1, "us": 2, "ns": 3}[unit]: (TType.STRUCT, {})}
    assert leaf.get(6) == {"ms": (TType.I32, 9), "us": (TType.I32, 10), "ns": None}[unit]
    reader = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert reader.metadata.num_row_groups == len(rows)
    assert [PLAIN["read_group"](reader, index) for index in range(len(rows))] == rows
    result, flags = [], set()
    for group, expected in enumerate(rows):
        column = reader.metadata.row_group(group).column(0)
        assert column.physical_type == "INT64" and column.compression == "SNAPPY"
        assert column.encodings == ("RLE", "PLAIN") and not column.has_dictionary_page
        metadata = THRIFT["column_metadata"](footer, group, 0)
        assert metadata[1] == (TType.I32, 2) and metadata[4] == (TType.I32, 1)
        assert THRIFT["list_field"](metadata, 3) == [b"event_time"]
        assert metadata[5] == (TType.I64, len(expected)) and 11 not in metadata
        cursor = metadata[9][1]
        stop = cursor + metadata[7][1]
        assert 4 <= cursor == column.data_page_offset < stop <= footer_start
        local, count = [], 0
        while cursor < stop:
            memory = TMemoryBuffer(wire[cursor:stop])
            header = THRIFT["read_struct"](TCompactProtocol(memory))
            start = cursor + memory.cstringio_buf.tell()
            end = start + header[3][1]
            assert cursor < start <= end <= stop
            assert header[1][1] == 3 and (4 in header) == checksum
            if checksum:
                assert header[4][1] % 2**32 == zlib.crc32(wire[start:end])
            info = header[8][1]
            slots, nulls, page_rows, tag, definitions, repetitions = [info[key][1] for key in range(1, 7)]
            assert slots == page_rows and tag == repetitions == 0
            assert 0 <= definitions <= min(header[2][1], header[3][1])
            values = expected[count:count + slots]
            assert len(values) == slots and values.count(None) == nulls
            stored_levels = wire[start:start + definitions]
            if nullable:
                assert DICTIONARY["hybrid"](stored_levels, 1, slots) == [int(v is not None) for v in values]
            else:
                assert not stored_levels and nulls == 0
            compressed = info.get(7, (TType.BOOL, True))[1]
            stored_scalars = wire[start + definitions:end]
            scalar_size = header[2][1] - definitions
            if compressed:
                scalar = PLAIN["SNAPPY"].decompress(stored_scalars, scalar_size).to_pybytes()
            else:
                scalar = stored_scalars
            assert len(scalar) == scalar_size == 8 * (slots - nulls)
            assert list(struct.iter_unpack("<q", scalar)) == [(v,) for v in values if v is not None]
            local.append((cursor, header, start, start + definitions, end))
            flags.add(compressed)
            count += slots
            cursor = end
        assert count == len(expected) and cursor == stop
        result.append(local)
    assert flags == ({False, True} if nullable else {True}), (nullable, checksum, flags)
    return result


def check_bad_source(wire, rows, message):
    reader = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert [PLAIN["read_group"](reader, group) for group in (0, 1)] == rows[:2]
    try:
        PLAIN["read_group"](reader, 2)
    except (pa.ArrowException, OSError) as error:
        assert message in str(error)
    else:
        raise AssertionError("PyArrow accepted the damaged suffix")


def bad_crc(wire, frame, at, rows):
    offset, header, start, _, end = frame
    assert start <= at < end
    bad = wire[:at] + bytes([wire[at] ^ 1]) + wire[at + 1:]
    declared = header[4][1] % 2**32
    actual = zlib.crc32(bad[start:end])
    assert declared != actual
    check_bad_source(bad, rows, "CRC")
    return bad, [offset, declared, actual]


def bad_snappy_size(wire, frame, rows):
    offset, header, start, suffix, end = frame
    info = header[8][1]
    assert info.get(7, (TType.BOOL, True))[1]
    target = header[2][1] - info[5][1]
    assert 0 < target < 126 and wire[suffix] == target
    changed = wire[:suffix] + bytes([target + 1]) + wire[suffix + 1:]
    crc = zlib.crc32(changed[start:end])
    header[4] = TType.I32, (crc + 2**31) % 2**32 - 2**31
    raw_header = THRIFT["encode"](header)
    assert len(raw_header) == start - offset
    changed = changed[:offset] + raw_header + changed[start:]
    check_bad_source(changed, rows, "Output buffer size")
    return changed


def fixtures():
    rows = PLAIN["groups"]()
    required = [[0 if slot is None else slot for slot in group] for group in rows]
    produce = PLAIN["produce"]
    positives = {
        "utc_nanos": ("ns", "UTC", True, rows, True),
        "local_micros": ("us", None, True, rows, True),
        "required_millis": ("ms", "UTC", False, required, True),
        "checksum_free": ("us", None, True, rows, False),
    }
    files, observations = {}, {}
    for name, (unit, zone, nullable, expected, checksum) in positives.items():
        files[name] = produce(unit, zone, "2.0", expected, checksum=checksum, nullable=nullable)
        observations[name] = checked_v2(files[name], expected, unit, zone, nullable, checksum)
    level, suffix = observations["utc_nanos"][2]
    assert level[2] < level[3] < level[4] and suffix[3] < suffix[4]
    files["bad_levels"], level_evidence = bad_crc(files["utc_nanos"], level, level[2], rows)
    files["bad_suffix"], suffix_evidence = bad_crc(files["utc_nanos"], suffix, suffix[3], rows)
    files["bad_size"] = bad_snappy_size(files["utc_nanos"], suffix, rows)
    files["v1"] = produce("us", None, "1.0", rows, checksum=True)
    files["dictionary"] = DICTIONARY["DICTIONARY"]["produce"](
        "us", None, "2.0", codec="SNAPPY", groups=DICTIONARY["GROUPS"], checksum=True)
    files["wrong_codec"] = produce("us", None, "2.0", rows, checksum=True, codec="NONE")
    return files, positives, [*level_evidence, *suffix_evidence]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, positives, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-snappy-v2-crc-") as temporary:
        directory = Path(temporary)
        for name, wire in files.items():
            (directory / (name + ".parquet")).write_bytes(wire)
        for index, group in enumerate(PLAIN["groups"]()[:2]):
            (directory / f"rows-{index}.txt").write_text("\n".join("null" if v is None else str(v) for v in group))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(directory),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in directory.glob("*.arrows")} == set(positives)
        for name, (unit, zone, nullable, rows, _) in positives.items():
            output = (directory / (name + ".arrows")).read_bytes()
            PLAIN["verify_ipc"](name, files[name], output, rows, pa.timestamp(unit, zone), nullable=nullable)


if __name__ == "__main__":
    main()
