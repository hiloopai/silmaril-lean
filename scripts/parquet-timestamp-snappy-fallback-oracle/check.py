"""Pin genuine codec-1 TIMESTAMP fallback and compare the emitted Arrow streams."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import random
import runpy
import struct
import subprocess
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SNAPPY = runpy.run_path(str(HERE.parent / "parquet-timestamp-snappy-dictionary-oracle/check.py"))
DICTIONARY = SNAPPY["DICTIONARY"]
THRIFT = DICTIONARY["THRIFT"]
MIN, MAX = DICTIONARY["MIN"], DICTIONARY["MAX"]
BATCH = 256


def groups():
    random_bits = random.Random(2429)

    def noise():
        return [None if i % 7 == 0 else random_bits.getrandbits(64) + MIN for i in range(BATCH)]

    return [
        [MIN, None, -11, MIN, MAX, -11, None, MAX] * 32 + [-7, None, -7, 8, None, 8, -7, 8] * 32 + noise(),
        [-17, MAX, None, MIN, MIN, None, -17, MAX] * 32 + noise() + [5, None, -5, 5, -5, None, 5, -5] * 32,
    ]


def read_group(parquet, index):
    return DICTIONARY["read_group"](parquet, index)


def expand(stored, size):
    result = SNAPPY["SNAPPY"].decompress(stored, size).to_pybytes()
    assert len(result) == size
    return result


def inspect(wire, page_version, checksum, rows):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema.column(0).physical_type == "INT32"
    assert [read_group(parquet, i) for i in range(parquet.metadata.num_row_groups)] == rows
    observations, compressed = [], set()
    for group_index, expected in enumerate(rows):
        column = parquet.metadata.row_group(group_index).column(1)
        assert column.physical_type == "INT64" and column.compression == "SNAPPY"
        assert column.encodings == ("PLAIN", "RLE", "RLE_DICTIONARY")
        assert column.num_values == len(expected)
        dictionary, *pages = SNAPPY["raw_frames"](wire, column)
        for _, header, _, stored in (dictionary, *pages):
            assert (4 in header) == checksum
            if checksum:
                assert header[4][1] % 2**32 == zlib.crc32(stored)
        offset, header, _, stored = dictionary
        assert offset == column.dictionary_page_offset and header[1][1] == 2
        assert header[7][1][2][1] == 0
        entries = [word for word, in struct.iter_unpack("<q", expand(stored, header[2][1]))]
        assert len(entries) == header[7][1][1][1]
        assert entries == list(dict.fromkeys(value for value in expected[:BATCH] if value is not None))
        assert pages[0][0] == column.data_page_offset
        data, tags, cursor = [], [], 0
        for frame in pages:
            header_offset, header, start, stored = frame
            assert header[1][1] == (0 if page_version == "1.0" else 3)
            info = header[5 if page_version == "1.0" else 8][1]
            count = info[1][1]
            assert count == BATCH
            slots = expected[cursor:cursor + count]
            cursor += count
            if page_version == "1.0":
                assert [info[i][1] for i in (3, 4)] == [3, 3]
                expanded = expand(stored, header[2][1])
                level_size, = struct.unpack_from("<I", expanded)
                levels = expanded[4:4 + level_size]
                values = expanded[4 + level_size:]
                tag, flag, suffix_start = info[2][1], True, start
            else:
                assert [info[i][1] for i in (2, 3, 6)] == [slots.count(None), count, 0]
                tag, flag, level_size = info[4][1], info[7][1], info[5][1]
                levels, suffix = stored[:level_size], stored[level_size:]
                size = header[2][1] - level_size
                values = expand(suffix, size) if flag else suffix
                assert len(values) == size
                suffix_start = start + level_size
            assert SNAPPY["hybrid"](levels, 1, len(slots)) == [int(value is not None) for value in slots]
            present = [value for value in slots if value is not None]
            if tag == 8:
                indices = SNAPPY["hybrid"](values[1:], values[0], len(present))
                assert [entries[index] for index in indices] == present
            else:
                assert tag == 0
                assert list(struct.iter_unpack("<q", values)) == [(value,) for value in present]
            tags.append(tag)
            compressed.add((tag, flag))
            data.append((frame, suffix_start, flag))
            print(f"V{page_version[0]} group {group_index} header {header_offset}: tag {tag}, compressed {flag}")
        assert cursor == len(expected) and tags == [8, 0, 0]
        observations.append((dictionary, data))
    expected_flags = {(8, True), (0, True)}
    if page_version == "2.0":
        expected_flags.add((0, False))
    assert compressed == expected_flags
    return observations


def corrupt(wire, frame, at, checksum, rows):
    offset, header, start, body = frame
    assert start <= at < start + len(body)
    changed = wire[:at] + bytes([wire[at] ^ 1]) + wire[at + 1:]
    reader = pq.ParquetFile(pa.BufferReader(changed), page_checksum_verification=True)
    assert read_group(reader, 0) == rows[0]
    try:
        read_group(reader, 1)
    except (pa.ArrowException, OSError) as error:
        if checksum:
            assert "CRC" in str(error)
    else:
        raise AssertionError("PyArrow admitted the late corrupted page")
    evidence = [offset]
    if checksum:
        declared = header[4][1] % 2**32
        computed = zlib.crc32(changed[start:start + len(body)])
        assert declared != computed
        evidence += [declared, computed]
    return changed, evidence


def fixtures():
    rows = groups()
    produce = DICTIONARY["produce"]
    options = dict(codec="SNAPPY", fallback=True, groups=rows, fallback_batch_size=BATCH)
    v1 = produce("ns", "UTC", "1.0", checksum=True, **options)
    v2 = produce("us", None, "2.0", checksum=True, **options)
    legacy = DICTIONARY["legacy_micros"](produce("us", "UTC", "2.0", **options))
    _, (dictionary, pages) = inspect(v1, "1.0", True, rows)
    bad_dictionary, bad_dict_evidence = corrupt(v1, dictionary, dictionary[2], True, rows)
    last, start, _ = pages[-1]
    bad_v1_plain, bad_plain_evidence = corrupt(v1, last, start, True, rows)
    _, (_, pages) = inspect(v2, "2.0", True, rows)
    last, suffix_start, _ = pages[-1]
    assert last[2] < suffix_start
    bad_levels, bad_levels_evidence = corrupt(v2, last, last[2], True, rows)
    _, (_, pages) = inspect(legacy, "2.0", False, rows)
    last, suffix_start, flag = pages[-1]
    assert flag and last[2] < suffix_start
    bad_suffix, bad_suffix_evidence = corrupt(legacy, last, suffix_start, False, rows)
    older, _ = SNAPPY["fixtures"]()
    uncompressed = produce("us", None, "2.0", fallback=True)
    return {
        "v1": v1, "v2": v2, "legacy": legacy, "bad_dictionary": bad_dictionary,
        "bad_v1_plain": bad_v1_plain, "bad_levels": bad_levels, "bad_suffix": bad_suffix,
        "dictionary_only": older["v2"], "uncompressed": uncompressed,
    }, [*bad_dict_evidence, *bad_plain_evidence, *bad_levels_evidence, *bad_suffix_evidence]


def verify_ipc(name, parquet_wire, output, unit, zone, rows):
    expected = pa.field("ticks", pa.timestamp(unit, zone), nullable=True)
    assert pq.ParquetFile(pa.BufferReader(parquet_wire)).schema_arrow.field(1).equals(expected)
    source = pa.BufferReader(output)
    with pa.ipc.open_stream(source) as stream:
        assert stream.schema.equals(pa.schema([expected]), check_metadata=True)
        assert [batch.column(0).cast(pa.int64()).to_pylist() for batch in stream] == rows
    assert source.tell() == len(output) and output.endswith(DICTIONARY["EOS"])
    messages = list(pa.ipc.MessageReader.open_stream(output))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(rows)
    assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
    print(f"{name}: exact {expected.type}, {[len(group) for group in rows]}, IPC SHA-256 {sha256(output).hexdigest()}")


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    print(f"Indexed CRC and suffix failure evidence {evidence}", flush=True)
    rows = groups()
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-snappy-fallback-") as temporary:
        directory = Path(temporary)
        for name, wire in files.items():
            (directory / (name + ".parquet")).write_bytes(wire)
        # A byte-exact independent golden for the complete prefix before the late fault.
        (directory / "prefix.txt").write_text("\n".join("null" if v is None else str(v) for v in rows[0]))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(directory),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in directory.glob("*.arrows")} == {"v1", "v2", "legacy"}
        for name, unit, zone in (("v1", "ns", "UTC"), ("v2", "us", None), ("legacy", "us", "UTC")):
            verify_ipc(name, files[name], (directory / (name + ".arrows")).read_bytes(), unit, zone, rows)


if __name__ == "__main__":
    main()
