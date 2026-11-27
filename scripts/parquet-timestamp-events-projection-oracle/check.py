"""Check the actual Lean Events projection against genuine PyArrow row groups."""

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
import pyarrow.parquet as pq
from thrift.Thrift import TType

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SCALAR = runpy.run_path(str(HERE.parent / "parquet-timestamp-scalar-dispatch-oracle/check.py"))
THRIFT, MIXED, FRAMES, CRC = (SCALAR[key] for key in ("THRIFT", "MIXED", "FRAMES", "CRC"))
FIELDS = [
    pa.field("decoy", pa.int32(), nullable=False),
    pa.field("utc_ns", pa.timestamp("ns", "UTC")),
    pa.field("local_us", pa.timestamp("us"), nullable=False),
    pa.field("utc_ms", pa.timestamp("ms", "UTC")),
]
CODECS = {1: 1, 2: 6, 3: 0}


def produce(page, groups):
    schema = pa.schema(FIELDS)
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(
        sink, schema, version="2.6", data_page_version=page,
        compression={"decoy": "NONE", "utc_ns": "SNAPPY", "local_us": "ZSTD", "utc_ms": "NONE"},
        use_dictionary=["local_us", "utc_ms"], write_statistics=False, store_schema=False,
        write_page_checksum=True, dictionary_pagesize_limit=16, write_batch_size=128, data_page_size=24,
    ) as writer:
        for group in groups:
            decoy = pa.array(range(len(group[0])), type=pa.int32())
            ticks = [pa.array(values, type=pa.int64()).view(field.type)
                     for field, values in zip(FIELDS[1:], group, strict=True)]
            writer.write_table(pa.Table.from_arrays([decoy, *ticks], schema=schema))
    return sink.getvalue().to_pybytes()


def open_parquet(wire):
    return pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)


def observe(parquet, ordinals, count=None):
    fields = [parquet.schema_arrow.field(i - 1) for i in ordinals]
    lines = ["schema|" + "|".join(
        f"{field.name},{field.type.unit},{field.type.tz or ''},{str(field.nullable).lower()}" for field in fields)]
    for group in range(parquet.num_row_groups if count is None else count):
        rows = parquet.metadata.row_group(group).num_rows
        columns = []
        for field in fields:
            values = parquet.read_row_group(group, columns=[field.name]).column(0).cast(pa.int64()).to_pylist()
            assert len(values) == rows
            columns.append(",".join("null" if value is None else str(value) for value in values))
        lines.append("|".join([str(rows), *columns]))
    return "\n".join(lines)


def inspect(wire, data, page):
    parquet = open_parquet(wire)
    footer = MIXED["metadata"](wire)
    leaves = THRIFT["list_field"](footer, 2)[1:]
    assert len(leaves) == len(FIELDS) and parquet.schema_arrow == pa.schema(FIELDS)
    for ordinal, (field, leaf) in enumerate(zip(FIELDS[1:], leaves[1:], strict=True), 2):
        annotation = leaf[10][1][8][1]
        assert leaf[1] == (TType.I32, 2) and leaf[4] == (TType.STRING, field.name.encode())
        assert leaf[3] == (TType.I32, int(field.nullable))
        assert annotation[1] == (TType.BOOL, field.type.tz == "UTC")
        assert annotation[2][1] == {{"ms": 1, "us": 2, "ns": 3}[field.type.unit]: (TType.STRUCT, {})}
    captures = []
    for index, inputs in enumerate(data):
        group_frames = []
        for col, (field, values) in enumerate(zip(FIELDS[1:], inputs, strict=True), 1):
            meta = THRIFT["column_metadata"](footer, index, col)
            start, stop = MIXED["column_extent"](meta)
            frames = list(FRAMES(wire, start, stop))
            assert frames[-1][2] + len(frames[-1][3]) == stop and frames[0][0] == start
            assert meta[4][1] == CODECS[col] and meta[5][1] == len(values)
            assert meta[9][1] == frames[int(col != 1)][0]
            assert (11 in meta) == (col != 1)
            if col != 1:
                assert meta[11][1] == start and frames[0][1][1][1] == 2
            for _, header, _, body in frames:
                assert header[3][1] == len(body) and zlib.crc32(body) == header[4][1] % 2**32
            data_frames = frames[int(col != 1):]
            assert all(frame[1][1][1] == (0 if page == "1.0" else 3) for frame in data_frames)
            tags = [SCALAR["frame_tag"](frame[1]) for frame in data_frames]
            assert tags == ([0] * len(tags) if col == 1 else [8, 0, 0, 0])
            assert parquet.read_row_group(index, columns=[field.name]).column(0).cast(pa.int64()).to_pylist() == values
            group_frames.append(frames)
            print(f"{page} group {index} ordinal {col + 1}, codec {CODECS[col]}, tags {tags}")
        captures.append(group_frames)
    return captures


def fixtures():
    original = SCALAR["BSS"]["timestamp_groups"]()
    # Three original groups with distinct signed/null patterns at each selected ordinal.
    data = []
    for row in (original[0], original[2], original[0]):
        local = [0 if value is None else value for value in reversed(row)]
        millis = [None if value is None else -value - 1 for value in row]
        data.append([row, local, millis])
    v1, v2 = [produce(page, data) for page in ("1.0", "2.0")]
    frames = inspect(v1, data, "1.0")
    inspect(v2, data, "2.0")
    corrupt, evidence = CRC(v1, frames[1][1][0])
    clean = open_parquet(v1)
    damaged = open_parquet(corrupt)
    assert observe(damaged, [4, 2]) == observe(clean, [4, 2])
    assert observe(damaged, [], None) == observe(clean, [])
    assert observe(damaged, [4, 3, 2], 1) == observe(clean, [4, 3, 2], 1)
    try:
        damaged.read_row_group(1, columns=["local_us"])
    except OSError as exc:
        assert "CRC" in str(exc)
    else:
        raise AssertionError("PyArrow admitted the mutated selected chunk")

    schema_only = produce("2.0", [])
    assert open_parquet(schema_only).num_row_groups == 0
    wires = {"native_v1": v1, "native_v2": v2, "native_schema_only": schema_only,
             "mutated_late_local_dictionary_crc": corrupt}
    observations = {}
    for key in ("native_v1", "native_v2", "native_schema_only"):
        parquet = open_parquet(wires[key])
        observations[key] = observe(parquet, [4, 2, 3, 2])
    observations["v1_subset"] = observe(clean, [3, 4])
    observations["v1_empty"] = observe(clean, [])
    observations["late_wide"] = observe(damaged, [4, 3, 2], 1)
    observations["late_reordered"] = observe(damaged, [3, 4, 2], 1)
    observations["late_filtered"] = observe(damaged, [4, 2], 1)
    observations["late_direct"] = observe(damaged, [4, 2])
    return wires, observations, evidence


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires, observations, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-events-projection-") as folder:
        output = Path(folder)
        for name, wire in wires.items():
            (output / f"{name}.parquet").write_bytes(wire)
        for name, expected in observations.items():
            (output / f"{name}.txt").write_text(expected)
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Compare.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
