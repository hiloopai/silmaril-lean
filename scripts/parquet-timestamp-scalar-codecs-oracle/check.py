"""Check original GZIP members and Zstandard frames across the TIMESTAMP scalar tags."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile
import zlib

import pyarrow as pa

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SCALAR = runpy.run_path(str(HERE.parent / "parquet-timestamp-scalar-dispatch-oracle/check.py"))
GZIP = runpy.run_path(str(HERE.parent / "parquet-timestamp-gzip-dictionary-v1-oracle/check.py"))
DATE_ZSTD = runpy.run_path(str(HERE.parent / "parquet-date-zstd-v1-oracle/check.py"))
FLAT_ZSTD = runpy.run_path(str(HERE.parent / "parquet-flat-zstd/check.py"))
TAGS, BASE_CODECS, BAD, CRC, THRIFT, VERIFY_IPC, produce, inspect = (
    SCALAR[name] for name in ("TAGS", "BASE_CODECS", "BAD", "CRC", "THRIFT", "VERIFY_IPC", "produce", "inspect"))
TType = SCALAR["TType"]


def gzip_body(stored, size):
    member = zlib.decompressobj(wbits=31)
    body = member.decompress(stored) + member.flush()
    assert member.eof and not member.unused_data and not member.unconsumed_tail
    assert len(body) == size
    return body


def zstd_body(extent, stored, size):
    assert extent(stored) == len(stored)
    assert FLAT_ZSTD["first_block"](stored)["dictionary_field_bytes"] == 0
    result = pa.Codec("zstd").decompress(stored, size).to_pybytes()
    assert len(result) == size
    return result


def fixtures():
    extent = DATE_ZSTD["frame_extent"]()
    codecs = {**BASE_CODECS, 2: gzip_body, 6: lambda body, size: zstd_body(extent, body, size)}
    utc = pa.field("ticks", pa.timestamp("ns", "UTC"))
    local = pa.field("ticks", pa.timestamp("us"), nullable=False)
    rows = SCALAR["BSS"]["timestamp_groups"]()
    required = [[0 if tick is None else tick for tick in group] for group in rows]
    wires, positives = {}, {}

    def add(name, codec, pages, tag, encoding, field, groups):
        print(name)
        wire = produce(field, groups, pages, codec, checksum=True, encoding=encoding)
        observed = inspect(wire, field, groups, [{tag}] * len(groups), codecs=codecs)
        assert all(4 in header for frames in observed for _, header, _, _ in frames)
        if pages == "2.0":
            flags = [header[8][1][7][1] for frames in observed for _, header, _, _ in frames]
            assert set(flags) == {False, True}, (name, flags)
            print(f"V2 value flags {flags}")
        wires[name], positives[name] = wire, (field, groups)

    for codec in ("GZIP", "ZSTD"):
        for pages in ("1.0", "2.0"):
            for name, (tag, encoding) in TAGS.items():
                add(f"native_{codec.lower()}_{name}_v{pages[0]}", codec, pages, tag, encoding, utc, rows)
    add("native_local_gzip_split_v1", "GZIP", "1.0", 9, "BYTE_STREAM_SPLIT", local, required)
    add("native_local_zstd_plain_v2", "ZSTD", "2.0", 0, "PLAIN", local, required)

    segments = [rows[0][:96], rows[2][:20], rows[0][:96]]
    for codec in ("GZIP", "ZSTD"):
        name = f"assembled_chunk_{codec.lower()}"
        wire, groups = SCALAR["make_mixed_chunk"](utc, codec, ("1.0", "2.0", "2.0"), segments)
        print(name)
        frames, = inspect(wire, utc, groups, [{0, 5, 9}], codecs=codecs)
        assert [SCALAR["frame_tag"](header) for _, header, _, _ in frames] == [5, 0, 9]
        assert [header[1][1] for _, header, _, _ in frames] == [0, 3, 3]
        assert all(4 in header for _, header, _, _ in frames)
        wires[name], positives[name] = wire, (utc, groups)

    seeds = [produce(utc, [rows[0]], "2.0", "NONE", checksum=True, encoding="PLAIN"),
             produce(utc, [rows[1]], "2.0", "SNAPPY", checksum=True, encoding="BYTE_STREAM_SPLIT")]
    parts = [(seeds[0], 0), (seeds[1], 0), (wires["native_gzip_plain_v1"], 0),
             (wires["native_zstd_delta_v2"], 0), (wires["native_gzip_split_v2"], 2),
             (wires["native_zstd_plain_v2"], 2)]
    mixed_rows = [rows[0], rows[1], rows[0], rows[0], rows[2], rows[2]]
    mixed = SCALAR["ASSEMBLE_GROUPS"](parts)
    captures = inspect(mixed, utc, mixed_rows, [{0}, {9}, {0}, {5}, {9}, {0}], codecs=codecs)
    for index, (source, original) in enumerate(parts):
        assert SCALAR["chunk_bytes"](mixed, index) == SCALAR["chunk_bytes"](source, original)
    wires["assembled_mixed_codecs"], positives["assembled_mixed_codecs"] = mixed, (utc, mixed_rows)
    gzip, zstd = captures[2][0], captures[3][0]
    wires["mutated_gzip_outer_crc"], crc = CRC(mixed, gzip)
    BAD(wires["mutated_gzip_outer_crc"], mixed_rows, 2, "CRC")
    wires["mutated_gzip_member_crc"] = GZIP["corrupt_member_crc"](mixed, gzip)
    BAD(wires["mutated_gzip_member_crc"], mixed_rows, 2, "gzip")

    _, zheader, _, stored = zstd
    info = zheader[8][1]
    assert info[7][1]
    definitions = info[5][1]
    suffix = stored[definitions:]
    malformed = stored[:definitions] + bytes([suffix[0] ^ 0x19]) + suffix[1:]
    assert extent(malformed[definitions:]) is None
    wires["mutated_zstd_magic"], _ = DATE_ZSTD["replace_stored"](mixed, zstd, malformed, THRIFT)
    BAD(wires["mutated_zstd_magic"], mixed_rows, 3, "zstd")
    assert info[2][1] < info[1][1]
    wires["mutated_zstd_null_count"] = SCALAR["GZIP"]["rewrite_header"](
        mixed, zstd, lambda header: header[8][1].update({2: (TType.I32, info[2][1] + 1)}))
    return wires, positives, [*crc, zstd[0]]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-scalar-codecs-") as temporary:
        output = Path(temporary)
        for name, wire in wires.items():
            (output / f"{name}.parquet").write_bytes(wire)
        for name, (_, rows) in cases.items():
            lines = [",".join("null" if tick is None else str(tick) for tick in group) for group in rows]
            (output / f"{name}.txt").write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(cases)
        for name, (field, rows) in cases.items():
            VERIFY_IPC((output / f"{name}.arrows").read_bytes(), field, rows)


if __name__ == "__main__":
    main()
