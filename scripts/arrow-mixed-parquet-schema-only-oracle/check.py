"""Compare both ordered IPC adapters at zero, one empty, and alternating batch counts."""

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
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PINS = {
    "int-first.arrows": "320df01ae11ad5a7c1a6d87d661d3114a4a6c7b99d66aa326a1acb8ca82ebba5",
    "int-first-lean.parquet": "9b72edff8c8254ba669fcddf2d469c0dfa8ab7baa7c1d2ef2c85552741d67bd5",
    "int-first-lean-returned.arrows": "3883baade0a4022add9a5f3ff9eb3e14f81ec737e574e27f5b7c47f77eb80256",
    "int-first-pyarrow.parquet": "dedbc9dd5781fa1241e443f2118ddf8c54b8c9745bc64d5637f4576c40d6a7ae",
    "int-first-pyarrow-returned.arrows": "3883baade0a4022add9a5f3ff9eb3e14f81ec737e574e27f5b7c47f77eb80256",
    "int-first-empty.arrows": "fec7b0afba6c440d6a1b0e7a0098067d3073973e01ebc2fd75b89ccf3e3217ec",
    "int-first-empty.parquet": "f8cfbc081584fb74585e404395f937174352b66c940f88e0da79d9cd98031416",
    "int-first-empty-returned.arrows": "ff3f05fcd2c425d4cf432b3ecb71f53f538d120ba938361b1a356df4ba0557e2",
    "byte-first.arrows": "d177a80b8a239cab0ee459f90c9eda9bb84a258bf6b808fe7349e997d9ef45d6",
    "byte-first-lean.parquet": "5bb9aeeb49bedf4f05dfd190b1f86b69a5a73a3514b71008c4a4a32428d7da0f",
    "byte-first-lean-returned.arrows": "767731ebaa9e4fc487ce17b8a9e1d3eca3ccb30b7240ce5de0f13ffc3ba5ee6e",
    "byte-first-pyarrow.parquet": "f3c18b7ed015b2c8b531d070c156cbfec3ca695653ff905508328afa06a8b34f",
    "byte-first-pyarrow-returned.arrows": "767731ebaa9e4fc487ce17b8a9e1d3eca3ccb30b7240ce5de0f13ffc3ba5ee6e",
    "byte-first-empty.arrows": "a77f0cd32a450a0d87d7099872d0f3c5c8f33f6f1639e8cfb5a68bb22f72b34f",
    "byte-first-empty.parquet": "d6e41f0ce9992a6d80ce72085667d1bc85e38c7045c12fd3f766e68766699597",
    "byte-first-empty-returned.arrows": "69e2f0d9437ba88f091882b07ead54fdecd1f16253d18c5ebcaaa3ed0d96a6d4",
    "int-first-alternating.arrows": "ce2f0585bb130e2eb33c5ac85d29c5056591ac0ce43d3f893787e9f45168c102",
    "int-first-alternating.parquet": "35ba8ca5ae6486332005d05cbd6441d65329e048e6962754db608e99a6e043b2",
    "int-first-alternating-returned.arrows": "8be566370b0204a76bf59f94466c0cbc4c1ad4dfc3ba89dbf1261be8444ea194",
    "int-first-alternating-late-body.arrows": "1d7bb019de6f58b2ffb92ea12e28c945a903895ace5a843ef9cfff51e548c030",
    "int-first-alternating-late-eos.arrows": "0ea3375dccaacc18f845f4316e5a586ffb31e0d4478e936acea9ab6ebabd096c",
    "byte-first-alternating.arrows": "98db48383ac9dc8fdcd34bb42f3edede3764a10a4e40f8292f393b23eef538e0",
    "byte-first-alternating.parquet": "74b3a2664cd641de0387c74b5fb7a3ac5c33a38d32c7ec56cba04c2b9a7a348f",
    "byte-first-alternating-returned.arrows": "25f6ab88a555c3ea8b3665155e048f25aad0f210f1b05dc2ce5336075e734f53",
    "byte-first-alternating-late-body.arrows": "0f0952aab87b175fae6985ecb4c252fd53f728a01fd5754b768b9166c2bdf9ef",
    "byte-first-alternating-late-eos.arrows": "6f1b206c5e80cf49d95f2e1de6abd14f6bdcafa15a3de78ae5ba0099a941bb91",
}


def parquet_schema(schema):
    return pa.schema([
        pa.field(field.name, pa.binary() if field.type == pa.binary_view() else field.type, field.nullable)
        for field in schema
    ])


def produce(out, schemas):
    stream = run_path(str(ROOT / "scripts/arrow-mixed-named-oracle/check.py"))["stream"]
    for name, schema in schemas.items():
        (out / f"{name}.arrows").write_bytes(stream(schema, []))
        (out / f"{name}-empty.arrows").write_bytes(stream(schema, [([], [])]))
        with pq.ParquetWriter(out / f"{name}-pyarrow.parquet", parquet_schema(schema),
                              compression=None, use_dictionary=False, store_schema=False):
            pass


def alternating_schema(schema):
    return pa.schema([field.with_nullable(True) for field in schema])


def produce_alternating(out, schemas):
    stream = run_path(str(ROOT / "scripts/arrow-mixed-named-oracle/check.py"))["stream"]
    records = [
        ([], []),
        ([-2**31, None], [None, b""]),
        ([], []),
        ([2**31 - 1], [b"\xff\x00abcdefghijklmno\x80"]),
        ([], []),
    ]
    for name, schema in schemas.items():
        ordered = records if name == "int-first" else [pair[::-1] for pair in records]
        wire = stream(alternating_schema(schema), ordered)
        fixture = name + "-alternating"
        (out / f"{fixture}.arrows").write_bytes(wire)
        with pa.BufferReader(wire) as carrier:
            reader = pa.ipc.MessageReader.open_stream(carrier)
            for _ in range(5):  # Schema and records 0 through 3.
                reader.read_next_message()
            body_end = carrier.tell()
        (out / f"{fixture}-late-body.arrows").write_bytes(wire[:body_end - 1])
        (out / f"{fixture}-late-eos.arrows").write_bytes(wire[:-8])


def check_zero_groups(wire, schema, thrift, physical_order):
    assert wire[:4] == wire[-4:] == b"PAR1"
    extent, = struct.unpack_from("<I", wire, len(wire) - 8)
    start = len(wire) - extent - 8
    assert start == 4
    reader = TMemoryBuffer(wire[start:-8])
    footer = thrift["read_struct"](TCompactProtocol(reader))
    assert reader.cstringio_buf.tell() == extent
    assert footer[3][1] == 0 and thrift["list_field"](footer, 4) == []
    root, *leaves = thrift["list_field"](footer, 2)
    assert root[5][1] == 2
    for leaf, field, physical in zip(leaves, schema, physical_order, strict=True):
        assert leaf[1][1] == physical and leaf[3][1] == int(field.nullable)
        assert leaf[4][1] == field.name.encode() and 6 not in leaf and 10 not in leaf
    with pq.ParquetFile(pa.BufferReader(wire)) as source:
        assert source.num_row_groups == 0
        assert source.schema_arrow.equals(schema)
        assert source.read().num_rows == 0


def check_ipc(path, schema, sizes, messages):
    wire = path.read_bytes()
    messages(wire, len(sizes))
    with pa.BufferReader(wire) as carrier, pa.ipc.open_stream(carrier) as source:
        assert source.schema.equals(schema)
        batches = list(source)
        assert [batch.num_rows for batch in batches] == sizes
        for batch in batches:
            batch.validate(full=True)
        assert wire.endswith(bytes.fromhex("ffffffff00000000")) and carrier.tell() == len(wire)
        return [[column.to_pylist() for column in batch.columns] for batch in batches]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert version("thrift") == "0.25.0"
    schemas = {
        "int-first": pa.schema([pa.field("count", pa.int32(), False), pa.field("raw", pa.binary_view(), True)]),
        "byte-first": pa.schema([pa.field("raw", pa.binary_view(), False), pa.field("count", pa.int32(), True)]),
    }
    produce(out, schemas)
    produce_alternating(out, schemas)
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "RoundTrip.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    thrift = run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
    parquet = run_path(str(ROOT / "scripts/parquet-mixed-v1-writer-oracle/check.py"))
    messages = run_path(str(ROOT / "scripts/arrow-mixed-parquet-roundtrip-oracle/check.py"))["messages"]
    fixtures = []
    for name, schema in schemas.items():
        physical_order = (1, 6) if name == "int-first" else (6, 1)
        source = out / f"{name}.arrows"
        check_ipc(source, schema, [], messages)
        fixtures.append(source)
        for producer in ("lean", "pyarrow"):
            file = out / f"{name}-{producer}.parquet"
            output = out / f"{name}-{producer}-returned.arrows"
            check_zero_groups(file.read_bytes(), parquet_schema(schema), thrift, physical_order)
            check_ipc(output, schema, [], messages)
            fixtures.extend((file, output))
        empty = out / f"{name}-empty.arrows"
        file = out / f"{name}-empty.parquet"
        output = out / f"{name}-empty-returned.arrows"
        check_ipc(empty, schema, [0], messages)
        check_ipc(output, schema, [0], messages)
        fields = [(field.name, field.nullable) for field in schema]
        parquet["check_wire_groups"](thrift, file.read_bytes(), fields, [[[], []]], physical_order)
        parquet["check_arrow_groups"](file.read_bytes(), fields, [[[], []]], physical_order)
        fixtures.extend((empty, file, output))
    for name, schema in schemas.items():
        physical_order = (1, 6) if name == "int-first" else (6, 1)
        schema = alternating_schema(schema)
        fixture = name + "-alternating"
        source = out / f"{fixture}.arrows"
        file = out / f"{fixture}.parquet"
        output = out / f"{fixture}-returned.arrows"
        counts = [0, 2, 0, 1, 0]
        groups = check_ipc(source, schema, counts, messages)
        assert check_ipc(output, schema, counts, messages) == groups
        fields = [(field.name, field.nullable) for field in schema]
        parquet["check_wire_groups"](thrift, file.read_bytes(), fields, groups, physical_order)
        parquet["check_arrow_groups"](file.read_bytes(), fields, groups, physical_order)
        fixtures.extend((source, file, output, out / f"{fixture}-late-body.arrows", out / f"{fixture}-late-eos.arrows"))
    assert {path.name for path in fixtures} == PINS.keys()
    for path in fixtures:
        digest = sha256(path.read_bytes()).hexdigest()
        print(f"{digest}  {path.name}")
        assert digest == PINS[path.name], f"{path.name}: fixture hash changed"
    print("PyArrow and Thrift verified both field orders across eight Parquet files and exact IPC EOS.")


if __name__ == "__main__":
    main()
