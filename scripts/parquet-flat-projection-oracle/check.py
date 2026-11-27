"""Independently check ordinal-selected flat Parquet and native IPC carriers."""

import argparse
from hashlib import sha256
from importlib.metadata import version
import os
from pathlib import Path
from runpy import run_path
import struct
import subprocess

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
THRIFT = run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
SCHEMA = pa.schema([
    pa.field("id", pa.int32(), nullable=False),
    pa.field("short", pa.binary()),
    pa.field("delta", pa.int32()),
    pa.field("long", pa.binary(), nullable=False),
    pa.field("keep", pa.bool_()),
])
PROJECTION = [3, 0, 1, 2]
REORDERED = [2, 1, 0]
PINS = {
    "wide.parquet": "4a63a28bda9dda61a334eca989d152cc96bc4c405f7b940f42bac3d819a84c6a",
    "wide-late.parquet": "1555bbf83c8d720d87e26b7d8926bd4684dffd83b6b4a8062c8a6c9b1737925a",
    "producer-empty.parquet": "4107cfef1b0f180ee812ba987dcac720e9ed3c43b1c4cbac987433ed38e9883d",
    "empty-middle.parquet": "d1a64588b88f9c84497283218e25b1c8a0a1f7cf353980323433a996d3e65c3c",
    "schema-only.parquet": "3fbbf7d60350faec15ac0303ab71a2b0ea9245714b27dacc3b0ca43f29ced089",
    "wide.arrows": "81beac932bab1dab6e314cbcd01217962363932dc4b86d86f2296c761820a742",
    "reordered.arrows": "3da37cc030c5cc533b6401205ba7226979cb155d573b5782590d23e003cb05f5",
    "repeated.arrows": "a8d95bf5888c5597dfec18734682ba544e687dddc5f3d4db24edab82207aeb6c",
    "zero-width.arrows": "aca5c892442de9b76bc0b9524801e1bf5454ec1cb36be1393d04bd885310e2b9",
    "empty-middle.arrows": "1a7b8642ae37d12e52284ec80e88517355eec7ce7bd9be10fc12a6dfedcd6c9a",
    "schema-only.arrows": "0e046b48109a437501e2826b28d7136acfaef91180ce34cca312e313606b39aa",
    "unselected-damage.arrows": "3da37cc030c5cc533b6401205ba7226979cb155d573b5782590d23e003cb05f5",
}
OPTIONS = dict(
    version="2.6", data_page_version="2.0", compression="NONE", use_dictionary=False,
    column_encoding="PLAIN", write_statistics=False, write_page_checksum=False,
    store_schema=False, write_batch_size=2, data_page_size=38,
)


def values(count, offset):
    integers = [offset + j for j in range(count)]
    integers[0] = -2**31 if offset == 0 else 2**31 - 1
    return [
        integers,
        [None if j % 3 == 0 else b"" if j % 3 == 1 else b"\xff\x00\x80" for j in range(count)],
        [None if j % 4 == 0 else -j - offset for j in range(count)],
        [bytes([128 + j, 0, 255]) + bytes([j + offset]) * (31 + j) for j in range(count)],
        [j % 2 == 0 for j in range(count)],
    ]


def produce(group_sizes):
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, SCHEMA, **OPTIONS) as writer:
        for ordinal, size in enumerate(group_sizes):
            columns = values(size, ordinal * 30) if size else [[] for _ in SCHEMA]
            writer.write_table(pa.Table.from_arrays(columns, schema=SCHEMA))
    return sink.getvalue().to_pybytes()


def footer(wire):
    size, = struct.unpack_from("<I", wire, len(wire) - 8)
    start = len(wire) - 8 - size
    view = TMemoryBuffer(wire[start:-8])
    metadata = THRIFT["read_struct"](TCompactProtocol(view))
    assert view.cstringio_buf.tell() == size
    return start, metadata


def frames(wire, column):
    start = column[9][1]
    stop = start + column[7][1]
    result = []
    while start < stop:
        buf = TMemoryBuffer(wire[start:stop])
        header = THRIFT["read_struct"](TCompactProtocol(buf))
        payload = start + buf.cstringio_buf.tell()
        end = payload + header[3][1]
        assert payload <= end <= stop and header[1][1] == 3 and header[2] == header[3]
        result.append((start, payload, end, header[8][1]))
        start = end
    assert start == stop
    return result


def check_parquet(wire, counts):
    start, metadata = footer(wire)
    assert wire[:4] == wire[-4:] == b"PAR1"
    assert metadata[3][1] == sum(counts)
    leaf_types = [1, 6, 1, 6, 0]
    for ordinal, (leaf, field) in enumerate(zip(THRIFT["list_field"](metadata, 2)[1:], SCHEMA, strict=True)):
        assert leaf[1][1] == leaf_types[ordinal]
        assert leaf[3][1] == int(field.nullable) and leaf[4][1] == field.name.encode()
        assert 6 not in leaf and 10 not in leaf
    shapes = []
    for index, (row_group, count) in enumerate(zip(THRIFT["list_field"](metadata, 4), counts, strict=True)):
        assert row_group[3][1] == count
        pages = []
        for ordinal, field in enumerate(SCHEMA):
            column = THRIFT["column_metadata"](metadata, index, ordinal)
            assert column[1][1] == leaf_types[ordinal] and column[3][1][1] == [field.name.encode()]
            assert column[4][1] == 0 and column[5][1] == count
            assert 4 <= column[9][1] < start and column[9][1] + column[7][1] <= start
            parts = frames(wire, column)
            assert parts and all(page[3][4][1] == 0 for page in parts)
            slots = [page[3][1][1] for page in parts]
            assert sum(slots) == count
            pages.append(slots)
        shapes.append(pages)
    return shapes


def frame_empty(wire):
    """Attach a real zero-slot V2 page to each PyArrow omitted chunk."""
    start, _ = footer(wire)
    zero = TType.I32, 0
    page = THRIFT["encode"]({
        1: (TType.I32, 3), 2: zero, 3: zero,
        8: (TType.STRUCT, {**dict.fromkeys(range(1, 7), zero), 7: (TType.BOOL, False)}),
    })

    def attach(metadata):
        group = THRIFT["list_field"](metadata, 4)[1]
        assert group[3] == (TType.I64, 0)
        group[2] = group[6] = TType.I64, len(SCHEMA) * len(page)
        for ordinal in range(len(SCHEMA)):
            column = THRIFT["column_metadata"](metadata, 1, ordinal)
            assert column[5] == column[7] == column[9] == (TType.I64, 0)
            column[2] = TType.LIST, (TType.I32, [3, 0])
            column[6] = column[7] = TType.I64, len(page)
            column[9] = TType.I64, start + ordinal * len(page)

    return THRIFT["rewrite_footer"](wire[:start] + page * len(SCHEMA) + wire[start:], attach)


def damage(wire, ordinal):
    _, metadata = footer(wire)
    column = THRIFT["column_metadata"](metadata, 1, ordinal)
    start, payload, _, header = frames(wire, column)[0]
    length_word = payload + header[5][1] + header[6][1]
    assert wire[length_word:length_word + 4] != b"\xff\xff\x00\x00"
    corrupted = wire[:length_word] + struct.pack("<I", 65535) + wire[length_word + 4:]
    return corrupted, start


def produce_fixtures(out):
    regular = produce([12, 6])
    unframed = produce([12, 0, 6])
    with_empty = frame_empty(unframed)
    (out / "producer-empty.parquet").write_bytes(unframed)
    with pq.ParquetFile(pa.BufferReader(unframed)) as original, pq.ParquetFile(pa.BufferReader(with_empty)) as framed:
        assert original.schema_arrow.equals(framed.schema_arrow) and original.num_row_groups == framed.num_row_groups
        for index in range(original.num_row_groups):
            assert original.read_row_group(index).equals(framed.read_row_group(index))
    schema_only = produce([])
    inputs = {"wide": regular, "empty-middle": with_empty, "schema-only": schema_only}
    for name, wire in inputs.items():
        (out / f"{name}.parquet").write_bytes(wire)
    for name, counts in (("wide", [12, 6]), ("empty-middle", [12, 0, 6]), ("schema-only", [])):
        shapes = check_parquet(inputs[name], counts)
        print(f"{name}: physical page slot counts {shapes}", flush=True)
        if counts:
            assert shapes[0][0] != shapes[0][3]
    damaged, start = damage(regular, 3)
    (out / "wide-late.parquet").write_bytes(damaged)
    return start


def check_ipc(file, wire, ordinals):
    with pq.ParquetFile(file) as parquet, pa.BufferReader(wire) as carrier, pa.ipc.open_stream(carrier) as ipc:
        schema = parquet.schema_arrow
        expected = pa.schema([
            pa.field(schema[i].name, pa.binary_view() if schema[i].type == pa.binary() else schema[i].type,
                     nullable=schema[i].nullable)
            for i in ordinals
        ])
        assert ipc.schema.equals(expected)
        batches = list(ipc)
        assert len(batches) == parquet.num_row_groups
        for index, batch in enumerate(batches):
            selected = list(dict.fromkeys(schema[i].name for i in ordinals))
            group = parquet.read_row_group(index, columns=selected, use_threads=False)
            batch.validate(full=True)
            assert batch.num_rows == parquet.metadata.row_group(index).num_rows
            assert [column.to_pylist() for column in batch.columns] == [
                group[schema[i].name].to_pylist() for i in ordinals
            ]
        assert carrier.tell() == len(wire) and wire.endswith(bytes.fromhex("ffffffff00000000"))
    with pa.BufferReader(wire) as carrier:
        messages = list(pa.ipc.MessageReader.open_stream(carrier))
        assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
        assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(batches)
        assert carrier.tell() == len(wire)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert version("thrift") == "0.25.0"
    failed_header = produce_fixtures(out)
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Convert.lean"), str(out), str(failed_header)],
        cwd=ROOT, check=True,
    )
    cases = [
        ("wide", "wide", PROJECTION),
        ("reordered", "wide", REORDERED),
        ("repeated", "wide", [3, 0, 3, 2]),
        ("zero-width", "wide", []),
        ("empty-middle", "empty-middle", PROJECTION),
        ("schema-only", "schema-only", PROJECTION),
        ("unselected-damage", "wide-late", REORDERED),
    ]
    for result, source, ordinals in cases:
        check_ipc(out / f"{source}.parquet", (out / f"{result}.arrows").read_bytes(), ordinals)
    for name in ("wide.parquet", "wide-late.parquet", "producer-empty.parquet", "empty-middle.parquet", "schema-only.parquet",
                 *(name + ".arrows" for name, _, _ in cases)):
        digest = sha256((out / name).read_bytes()).hexdigest()
        print(f"{digest}  {name}")
        assert digest == PINS[name], f"{name}: carrier hash changed"
    print("PyArrow and Thrift verified exact rows, field order, independent page cuts and native IPC EOS.")


if __name__ == "__main__":
    main()
