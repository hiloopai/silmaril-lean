"""Check genuine GZIP V2 TIMESTAMP dictionary pages and native Arrow IPC."""

from copy import deepcopy
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
GZIP = runpy.run_path(str(HERE.parent / "parquet-timestamp-gzip-dictionary-v1-oracle/check.py"))
ORACLE, THRIFT = GZIP["ORACLE"], GZIP["THRIFT"]
GROUPS = ORACLE["GROUPS"]


def produce(field, rows, *, checksum=True, codec="GZIP", page_version="2.0"):
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False), field])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version, compression=codec,
                          use_dictionary=["ticks"], write_statistics=False, store_schema=False,
                          write_page_checksum=checksum) as writer:
        for group in rows:
            ticks = pa.array(group, type=pa.int64()).view(field.type)
            writer.write_table(pa.Table.from_arrays([pa.array(range(len(group)), type=pa.int32()), ticks],
                                                    schema=schema))
    return sink.getvalue().to_pybytes()


def inspect(wire, field, groups, checksum):
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - footer_size
    memory = TMemoryBuffer(wire[footer_start:-8])
    footer = THRIFT["read_struct"](TCompactProtocol(memory))
    assert memory.cstringio_buf.tell() == footer_size
    _, _, leaf = THRIFT["list_field"](footer, 2)
    assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(field.nullable))
    stamp = leaf[10][1][8][1]
    assert stamp[1] == (TType.BOOL, field.type.tz == "UTC")
    unit = {"us": 2, "ns": 3}[field.type.unit]
    assert stamp[2][1] == {unit: (TType.STRUCT, {})}

    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.field(1).equals(field) and parquet.metadata.num_row_groups == len(groups)
    captures, flags, dictionaries = [], [], []
    for group, rows in enumerate(groups):
        column = parquet.metadata.row_group(group).column(1)
        metadata = THRIFT["column_metadata"](footer, group, 1)
        assert metadata[1] == (TType.I32, 2) and metadata[4] == (TType.I32, 2)
        assert THRIFT["list_field"](metadata, 3) == [b"ticks"]
        assert set(THRIFT["list_field"](metadata, 2)) == {0, 3, 8}
        assert metadata[5][1] == column.num_values == len(rows)
        assert metadata[11][1] == column.dictionary_page_offset and metadata[9][1] == column.data_page_offset
        assert metadata[7][1] == column.total_compressed_size
        assert 4 <= metadata[11][1] < metadata[9][1] < metadata[11][1] + metadata[7][1] <= footer_start
        assert GZIP["read_group"](parquet, group) == rows

        dictionary, data = list(ORACLE["raw_frames"](wire, column))
        assert dictionary[0] == column.dictionary_page_offset and data[0] == column.data_page_offset
        assert dictionary[1][1][1] == 2 and dictionary[1][7][1][2] == (TType.I32, 0)
        entries = [word for word, in struct.iter_unpack("<q", GZIP["member"](dictionary, checksum))]
        assert len(entries) == dictionary[1][7][1][1][1]
        assert entries == list(dict.fromkeys(v for v in rows if v is not None))
        dictionaries.append(tuple(entries))

        _, header, _, stored = data
        assert header[1][1] == 3 and header[3][1] == len(stored)
        assert (4 in header) == checksum
        if checksum:
            assert header[4][1] % 2**32 == zlib.crc32(stored)
        info = header[8][1]
        assert [info[i][1] for i in (1, 2, 3, 4, 6)] == [len(rows), rows.count(None), len(rows), 8, 0]
        level_size, compressed = info[5][1], info[7][1]
        assert 0 <= level_size <= min(header[2][1], header[3][1])
        definitions, suffix = stored[:level_size], stored[level_size:]
        mask = [int(value is not None) for value in rows]
        if field.nullable:
            assert ORACLE["hybrid"](definitions, 1, len(rows)) == mask
        else:
            assert not definitions and all(mask)
        if compressed:
            decoder = zlib.decompressobj(wbits=31)
            references = decoder.decompress(suffix) + decoder.flush()
            assert decoder.eof and not decoder.unused_data and not decoder.unconsumed_tail
            assert struct.unpack("<II", suffix[-8:]) == (zlib.crc32(references), len(references))
        else:
            references = suffix
        assert len(references) == header[2][1] - level_size and references
        indices = ORACLE["hybrid"](references[1:], references[0], sum(mask))
        assert [entries[i] for i in indices] == [value for value in rows if value is not None]
        flags.append(compressed)
        captures.append((dictionary, data))
        print(f"{field.type} group {group}: raw levels {level_size}, "
              f"stored references {len(suffix)}, GZIP storage {compressed}, header {data[0]}")
    assert flags == [True, False, True] and len(set(dictionaries)) == len(groups)
    return captures


def check_bad(wire, group, reason):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert [GZIP["read_group"](parquet, i) for i in range(group)] == GROUPS[:group]
    try:
        GZIP["read_group"](parquet, group)
    except (pa.ArrowException, OSError) as error:
        assert reason.lower() in str(error).lower(), str(error)
    else:
        raise AssertionError("PyArrow accepted a damaged group")


def rewrite_with_outer_crc(wire, frame, stored):
    offset, header, body, original = frame
    assert len(stored) == len(original)
    edited = deepcopy(header)
    crc = zlib.crc32(stored)
    edited[4] = (TType.I32, (crc + 2**31) % 2**32 - 2**31)
    encoded = THRIFT["encode"](edited)
    assert len(encoded) == body - offset
    return wire[:offset] + encoded + stored + wire[body + len(original):]


def corrupt_member_suffix(wire, data):
    _, header, _, stored = data
    info = header[8][1]
    assert info[7][1]
    changed = stored[:-8] + bytes([stored[-8] ^ 1]) + stored[-7:]
    try:
        zlib.decompress(changed[info[5][1]:], wbits=31)
    except zlib.error as error:
        assert "incorrect data check" in str(error), str(error)
    else:
        raise AssertionError("zlib accepted the damaged GZIP member")
    return rewrite_with_outer_crc(wire, data, changed)


def corrupt_raw_suffix(wire, data):
    _, header, _, stored = data
    info = header[8][1]
    assert not info[7][1]
    start = info[5][1]
    assert stored[start] <= 32
    changed = stored[:start] + b"\x21" + stored[start + 1:]
    return rewrite_with_outer_crc(wire, data, changed)


def fixtures():
    required = [[v if v is not None else 0 for v in group] for group in GROUPS]
    admitted = {
        "utc_nanos": (pa.field("ticks", pa.timestamp("ns", "UTC"), nullable=True), GROUPS, True),
        "local_micros": (pa.field("ticks", pa.timestamp("us"), nullable=False), required, False),
    }
    files, captures = {}, {}
    for name, (field, rows, checksum) in admitted.items():
        files[name] = produce(field, rows, checksum=checksum)
        captures[name] = inspect(files[name], field, rows, checksum)

    good = files["utc_nanos"]
    (_, first), (_, raw), (dictionary, compressed) = captures["utc_nanos"]
    assert compressed[1][8][1][5][1] > 0
    files["mutated_raw_level_crc"], crc = GZIP["corrupt_frame_crc"](good, compressed)
    files["mutated_member"] = corrupt_member_suffix(good, compressed)
    files["mutated_dictionary"] = GZIP["corrupt_member_crc"](good, dictionary)
    files["mutated_raw_references"] = corrupt_raw_suffix(good, raw)
    files["mutated_two_groups"] = corrupt_raw_suffix(files["mutated_member"], raw)
    check_bad(files["mutated_raw_level_crc"], 2, "CRC")
    check_bad(files["mutated_member"], 2, "gzip")
    check_bad(files["mutated_dictionary"], 2, "gzip")
    for name in ("mutated_raw_references", "mutated_two_groups"):
        check_bad(files[name], 1, "bit_width 33")

    field = admitted["utc_nanos"][0]
    files["v1"] = produce(field, GROUPS, page_version="1.0")
    v1 = pq.ParquetFile(pa.BufferReader(files["v1"]))
    v1_offset = v1.metadata.row_group(0).column(1).data_page_offset
    files["snappy"] = produce(field, GROUPS, codec="SNAPPY")
    fallback = runpy.run_path(str(HERE.parent / "parquet-timestamp-gzip-fallback-v1-oracle/check.py"))
    files["v2_fallback"] = fallback["produce"](field, fallback["GROUPS"], page_version="2.0")
    v2 = pq.ParquetFile(pa.BufferReader(files["v2_fallback"]))
    _, *data = ORACLE["raw_frames"](files["v2_fallback"], v2.metadata.row_group(0).column(1))
    tags = [frame[1][8][1][4][1] for frame in data]
    assert tags == [8, 0, 0]
    return files, admitted, [*crc, dictionary[0], raw[0], first[0], v1_offset, data[1][0]]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, admitted, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-gzip-dictionary-v2-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / (name + ".parquet")).write_bytes(wire)
        for index, group in enumerate(GROUPS[:2]):
            (output / f"rows-{index}.txt").write_text("\n".join("null" if v is None else str(v) for v in group))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(admitted)
        for name, (field, groups, _) in admitted.items():
            GZIP["verify_ipc"]((output / (name + ".arrows")).read_bytes(), field, groups)


if __name__ == "__main__":
    main()
