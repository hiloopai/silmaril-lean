"""Pin PyArrow no-frame TIMESTAMP groups and verify the actual emitted IPC."""

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

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MIXED = runpy.run_path(str(HERE.parent / "parquet-timestamp-mixed-groups-oracle/check.py"))
THRIFT = MIXED["THRIFT"]
VERIFY_IPC = MIXED["FALLBACK"]["verify_ipc"]
MIN, MAX = MIXED["MIN"], MIXED["MAX"]

NATIVE = {
    "utc": ("ns", "UTC", "NONE", "1.0", [[MIN, None, MAX], [], [], [-3, 0]]),
    "local": ("us", None, "SNAPPY", "2.0", [[], [-123, None], [], [MAX, -1]]),
    "all_empty": ("us", None, "NONE", "2.0", [[], []]),
    "schema_only": ("us", None, "NONE", "2.0", []),
}


def assert_page_less(group, codec):
    assert list(group) == [1, 2, 3, 5, 6]
    assert all(group[i] == (TType.I64, 0) for i in (2, 3, 5, 6))
    chunks = THRIFT["list_field"](group, 1)
    for i, (chunk, name) in enumerate(zip(chunks, (b"decoy", b"ticks"), strict=True)):
        assert list(chunk) == [2, 3] and chunk[2] == (TType.I64, 0)
        assert chunk[3][1] == {
            1: (TType.I32, i + 1), 2: (TType.LIST, (TType.I32, [3])),
            3: (TType.LIST, (TType.STRING, [name])), 4: (TType.I32, codec),
            5: (TType.I64, 0), 6: (TType.I64, 0), 7: (TType.I64, 0),
            9: (TType.I64, 0), 13: (TType.LIST, (TType.STRUCT, [])),
        }


def source_rows(wire, rows):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.metadata.num_row_groups == len(rows)
    assert [MIXED["DICTIONARY"]["read_group"](parquet, i) for i in range(len(rows))] == rows


def fixtures():
    files = {}
    for name, (unit, zone, codec, version, rows) in NATIVE.items():
        wire = MIXED["produce_plain"](unit, zone, codec, version, rows)
        source_rows(wire, rows)
        footer = MIXED["metadata"](wire)
        for group, expected in zip(THRIFT["list_field"](footer, 4), rows, strict=True):
            if not expected:
                assert_page_less(group, 1 if codec == "SNAPPY" else 0)
        files[name] = wire

    native = MIXED["metadata"](files["local"])
    empty = THRIFT["list_field"](native, 4)[0]

    def insert_empty(footer):
        assert footer[2] == native[2]
        groups = THRIFT["list_field"](footer, 4)
        groups.insert(1, empty)
        assert all(7 not in group for group in groups)

    mixed, (_, crc_offset, crc, actual) = MIXED["fixtures"]()
    files["assembled"] = THRIFT["rewrite_footer"](mixed["local"], insert_empty)
    files["late_crc"] = THRIFT["rewrite_footer"](mixed["checksum_failure"], insert_empty)
    original = MIXED["groups"]()
    rows = [original[0], [], *original[1:]]
    footer_size, = struct.unpack_from("<I", mixed["local"], len(mixed["local"]) - 8)
    data_stop = len(mixed["local"]) - 8 - footer_size
    assert files["assembled"][:data_stop] == mixed["local"][:data_stop]
    assert files["late_crc"][:data_stop] == mixed["checksum_failure"][:data_stop]
    source_rows(files["assembled"], rows)
    broken = pq.ParquetFile(pa.BufferReader(files["late_crc"]), page_checksum_verification=True)
    assert [MIXED["DICTIONARY"]["read_group"](broken, i) for i in range(6)] == rows[:6]
    try:
        MIXED["DICTIONARY"]["read_group"](broken, 6)
    except (pa.ArrowException, OSError) as error:
        assert "CRC" in str(error)
    else:
        raise AssertionError("PyArrow accepted the corrupted final group")

    def positive_missing(footer):
        typ, row_count = footer[3]
        footer[3] = typ, row_count + 1
        group = THRIFT["list_field"](footer, 4)[0]
        group[3] = TType.I64, 1
        for chunk in THRIFT["list_field"](group, 1):
            chunk[3][1][5] = TType.I64, 1

    def nonzero_values(footer):
        THRIFT["column_metadata"](footer, 0, 1)[5] = TType.I64, 1

    def wrong_empty_path(footer):
        THRIFT["column_metadata"](footer, 0, 1)[3] = TType.LIST, (TType.STRING, [b"other"])

    def nonempty_stats(footer):
        THRIFT["column_metadata"](footer, 0, 1)[13] = TType.LIST, (TType.STRUCT, [
            {1: (TType.I32, 0), 2: (TType.I32, 0), 3: (TType.I32, 1)}
        ])

    for name, change in (("positive_missing", positive_missing), ("nonzero_values", nonzero_values),
                         ("wrong_empty_path", wrong_empty_path), ("nonempty_stats", nonempty_stats)):
        files[name] = THRIFT["rewrite_footer"](files["local"], change)
    files["unclaimed_byte"] = files["schema_only"][:4] + b"x" + files["schema_only"][4:]
    dict_only = MIXED["DICTIONARY"]["produce"]("us", None, "2.0", groups=[[]])
    chunk = THRIFT["column_metadata"](MIXED["metadata"](dict_only))
    assert chunk[5][1] == chunk[9][1] == 0 < chunk[7][1] and chunk[11][1] >= 4
    files["empty_dictionary_frame"] = dict_only
    return files, rows, [crc_offset, crc, actual]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, rows, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    positive = {name: (unit, zone, groups) for name, (unit, zone, _, _, groups) in NATIVE.items()}
    positive["assembled"] = ("us", None, rows)
    with tempfile.TemporaryDirectory(prefix="timestamp-page-less-") as temporary:
        directory = Path(temporary)
        for name, wire in files.items():
            (directory / (name + ".parquet")).write_bytes(wire)
        for index, group in enumerate(rows[:6]):
            (directory / f"rows-{index}.txt").write_text(
                "\n".join("null" if v is None else str(v) for v in group))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(directory),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in directory.glob("*.arrows")} == set(positive)
        for name, (unit, zone, expected) in positive.items():
            VERIFY_IPC(name, files[name], (directory / (name + ".arrows")).read_bytes(), unit, zone, expected)


if __name__ == "__main__":
    main()
