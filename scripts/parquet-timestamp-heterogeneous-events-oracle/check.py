"""Compare Lean's heterogeneous typed Events with native PyArrow and original Thrift frames."""

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
HELPERS = runpy.run_path(str(HERE.parent / "parquet-timestamp-scalar-dispatch-oracle/check.py"))
THRIFT, MIXED, FRAMES = (HELPERS[key] for key in ("THRIFT", "MIXED", "FRAMES"))
MIN, MAX = -(2**63), 2**63 - 1
FIELDS = [
    pa.field("code", pa.int32(), nullable=False),
    pa.field("label", pa.string()),
    pa.field("utc_ns", pa.timestamp("ns", "UTC")),
    pa.field("local_us", pa.timestamp("us"), nullable=False),
]
GROUPS = [
    [[-2**31, 0, 2**31 - 1, -1, 7], ["λ", None, "", "中文", "null"],
     [MIN, None, MAX, -1, 0], [MAX, -1000, MIN, 1, 0]],
    [[23, -10, 0], ["café", "", None], [MAX, None, MIN], [-999, 99, 0]],
    [[0, 12], ["🙂", "end"], [None, -59], [0, -1]],
]


def produce(page, groups, fields=FIELDS, *, checksum=False):
    schema = pa.schema(fields)
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(
        sink, schema, version="2.6", data_page_version=page,
        compression={"code": "NONE", "label": "NONE", "utc_ns": "ZSTD", "local_us": "SNAPPY"},
        use_dictionary=["utc_ns"], write_statistics=False, store_schema=False, write_page_checksum=checksum,
    ) as writer:
        for group in groups:
            columns = [
                pa.array(values, type=pa.int64()).view(field.type)
                if pa.types.is_timestamp(field.type) else pa.array(values, type=field.type)
                for field, values in zip(fields, group, strict=True)
            ]
            writer.write_table(pa.Table.from_arrays(columns, schema=schema))
    return sink.getvalue().to_pybytes()


def open_parquet(wire):
    return pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)


def observe(parquet, ordinals, count=None):
    fields = [parquet.schema_arrow.field(i) for i in ordinals]
    labels = []
    for field in fields:
        if pa.types.is_timestamp(field.type):
            label = f"{field.type.unit},{field.type.tz or ''}"
        else:
            label = "utf8" if pa.types.is_string(field.type) else "int32"
        labels.append(f"{field.name},{label},{str(field.nullable).lower()}")
    lines = ["schema|" + "|".join(labels)]
    for group in range(parquet.num_row_groups if count is None else count):
        rows = parquet.metadata.row_group(group).num_rows
        columns = []
        for field in fields:
            values = parquet.read_row_group(group, columns=[field.name]).column(0)
            if pa.types.is_timestamp(field.type):
                values = values.cast(pa.int64())
            assert len(values) == rows
            columns.append(",".join(
                "null" if value is None else "text:" + value if isinstance(value, str) else str(value)
                for value in values.to_pylist()))
        lines.append("|".join([str(rows), *columns]))
    return "\n".join(lines)


def inspect(wire, page, *, checksum=False):
    parquet = open_parquet(wire)
    assert parquet.schema_arrow == pa.schema(FIELDS) and parquet.num_row_groups == len(GROUPS)
    footer = MIXED["metadata"](wire)
    _, *leaves = THRIFT["list_field"](footer, 2)
    for leaf, field, physical in zip(leaves, FIELDS, (1, 6, 2, 2), strict=True):
        assert leaf[1] == (TType.I32, physical) and leaf[4] == (TType.STRING, field.name.encode())
        assert leaf[3] == (TType.I32, int(field.nullable))
        if pa.types.is_string(field.type):
            assert leaf[10][1] == {1: (TType.STRUCT, {})} and leaf[6] == (TType.I32, 0)
        if pa.types.is_timestamp(field.type):
            annotation = leaf[10][1][8][1]
            assert annotation[1] == (TType.BOOL, field.type.tz == "UTC")
            assert annotation[2][1] == {{"us": 2, "ns": 3}[field.type.unit]: (TType.STRUCT, {})}
    target = None
    for group, expected in enumerate(GROUPS):
        observed = parquet.read_row_group(group)
        for col, (field, values, codec) in enumerate(zip(FIELDS, expected, (0, 0, 6, 1), strict=True)):
            column = observed.column(col)
            if pa.types.is_timestamp(field.type):
                column = column.cast(pa.int64())
            assert column.to_pylist() == values
            meta = THRIFT["column_metadata"](footer, group, col)
            start, stop = MIXED["column_extent"](meta)
            frames = list(FRAMES(wire, start, stop))
            assert frames[0][0] == start and frames[-1][2] + len(frames[-1][3]) == stop
            assert meta[4][1] == codec and meta[5][1] == len(values)
            dictionary = col == 2
            assert (11 in meta) == dictionary and meta[9][1] == frames[int(dictionary)][0]
            if dictionary:
                assert meta[11][1] == start and frames[0][1][1][1] == 2
            for _, header, _, body in frames:
                assert header[3][1] == len(body) and (4 in header) == checksum
                if checksum:
                    assert zlib.crc32(body) == header[4][1] % 2**32
            assert all(frame[1][1][1] == (0 if page == "1.0" else 3)
                       for frame in frames[int(dictionary):])
            assert all(HELPERS["frame_tag"](frame[1]) == (8 if dictionary else 0)
                       for frame in frames[int(dictionary):])
            if group == 1 and dictionary:
                target = frames[0]
    assert target is not None
    return target


def fixtures():
    v1, v2 = (produce(page, GROUPS) for page in ("1.0", "2.0"))
    target = inspect(v1, "1.0")
    inspect(v2, "2.0")
    offset, _, body_start, stored = target
    assert stored.startswith(b"\x28\xb5\x2f\xfd")
    corrupt = v1[:body_start] + b"\0" + v1[body_start + 1:]
    damaged, clean = open_parquet(corrupt), open_parquet(v1)
    try:
        damaged.read_row_group(1, columns=["utc_ns"])
    except OSError as cause:
        assert "ZSTD" in str(cause).upper(), str(cause)
    else:
        raise AssertionError("PyArrow admitted the mutated selected dictionary")
    assert observe(damaged, [1, 3, 0]) == observe(clean, [1, 3, 0])
    schema_only = produce("2.0", [])
    unannotated = produce("2.0", [], [FIELDS[0], FIELDS[1].with_type(pa.binary()), *FIELDS[2:]])
    assert pa.types.is_binary(open_parquet(unannotated).schema_arrow.field(1).type)
    checksummed = produce("1.0", GROUPS, checksum=True)
    inspect(checksummed, "1.0", checksum=True)
    wires = {
        "native_v1": v1,
        "native_v2": v2,
        "native_schema_only": schema_only,
        "native_unannotated_binary": unannotated,
        "native_checksummed_v1": checksummed,
        "mutated_late_timestamp_dictionary_magic": corrupt,
    }
    selected = [3, 0, 1, 2, 1]
    observations = {
        name: observe(open_parquet(wires[name]), selected)
        for name in ("native_v1", "native_v2", "native_schema_only")
    }
    observations.update(
        reordered=observe(clean, [1, 3, 0]),
        empty=observe(clean, []),
        late_wide=observe(damaged, selected, 1),
        late_reordered=observe(damaged, [2, 1, 0], 1),
        late_logical=observe(damaged, [1, 3, 0], 1),
    )
    return wires, observations, offset


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires, observations, offset = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-heterogeneous-") as folder:
        output = Path(folder)
        for name, wire in wires.items():
            (output / f"{name}.parquet").write_bytes(wire)
        for name, expected in observations.items():
            (output / f"{name}.txt").write_text(expected, encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Compare.lean"), str(output),
                        str(offset)], cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
