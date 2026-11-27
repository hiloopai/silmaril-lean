"""Read actual Lean-emitted IPC against independently written typed CSV."""

import argparse
import csv
from hashlib import sha256
import os
from pathlib import Path
from runpy import run_path
import subprocess
import sys

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PINS = {
    "mixed.csv": "ab2fcef292cee3b0eb6d89417cb4dff3b1cb143c18be45cf9098d6e696eea3b4",
    "mixed.arrows": "468e5559734466bc3035987012768aec39e628b314e2ac7f8110afa77d9e1655",
    "header-only.csv": "c0be2a9c1248506b8f51b1fdf08298befd7cd90c5220cc533917f482db80b897",
    "header-only.arrows": "83b364a1182ede28603b272e346514640b06b84548d218578626c08cb05719dd",
    "zero-width.csv": "a4ac417d5aea856b02ffcc1e240cfe3c55ef44073e5d893673dbb9fe6e741bc4",
    "zero-width.arrows": "16dec45a3f6d8aa85cbbb3db132455649a07fb31c0e517a3605398e776403d97",
    "zero-width-header-only.csv": "91a4e2f100227487a802ac040b85700f03520b347fbfe4c23b7bf2d97b43d9fa",
    "zero-width-header-only.arrows": "69868f5c54d9cf74502bedb0107d302583ac102ba3ae47c18606d38dd336f2fc",
}
MIXED = ("mixed", "header-only")
ZERO = ("zero-width", "zero-width-header-only")


def tagged(field, token):
    if token == "N":
        assert field.nullable
        return None
    assert token.startswith("T")
    value = token[1:]
    return int(value) if pa.types.is_int32(field.type) else value


def compare(out, name, schema):
    with (out / f"{name}.csv").open(encoding="utf-8", newline="") as stream:
        header, *rows = list(csv.reader(stream, strict=True))
    assert header == (schema.names or [""])
    if len(schema) == 0:
        assert all(row == [""] for row in rows)
    columns = [[tagged(field, row[i]) for row in rows] for i, field in enumerate(schema)]
    wire = (out / f"{name}.arrows").read_bytes()
    assert wire.endswith(bytes.fromhex("ffffffff00000000"))
    with pa.BufferReader(wire) as carrier, pa.ipc.open_stream(carrier) as stream:
        assert stream.schema.equals(schema)
        (batch,) = list(stream)
        batch.validate(full=True)
        assert batch.num_rows == len(rows)
        assert [column.to_pylist() for column in batch.columns] == columns
        assert carrier.tell() == len(wire)
    with pa.BufferReader(wire) as carrier:
        messages = list(pa.ipc.MessageReader.open_stream(carrier))
        assert [message.type for message in messages] == ["schema", "record batch"]
        assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
        assert carrier.tell() == len(wire)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert sys.version_info[:2] == (3, 13)
    source = run_path(str(ROOT / "scripts/arrow-mixed-scan-csv-oracle/check.py"))
    producer_dir = out / "producer"
    producer_dir.mkdir(exist_ok=True)
    source["write_ipc"](producer_dir)
    producer = producer_dir / "mixed.arrows"
    with pa.ipc.open_stream(producer.read_bytes()) as stream:
        schema = stream.schema
    records = source["expected_csv"](producer)
    write_csv = source["write_csv"]
    write_csv(out / "mixed.csv", records)
    write_csv(out / "header-only.csv", records[:1])
    write_csv(out / "zero-width.csv", [[""], [""], [""]])
    write_csv(out / "zero-width-header-only.csv", [[""]])
    for name, row, column, value in [
        ("wrong-header", 0, 1, "wrong"),
        ("bad-integer", 1, 1, "T01"),
        ("required-null", 2, 3, "N"),
    ]:
        malformed = [row.copy() for row in records]
        malformed[row][column] = value
        write_csv(out / f"{name}.csv", malformed)

    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    for name in MIXED:
        compare(out, name, schema)
    for name in ZERO:
        compare(out, name, pa.schema([]))
    for name, expected_hash in PINS.items():
        digest = sha256((out / name).read_bytes()).hexdigest()
        print(f"{digest}  {name}")
        assert digest == expected_hash, f"{name}: fixture hash changed"
    print("PyArrow verified four Lean streams with exact descriptors, ordered slots, one batch, and EOS.")


if __name__ == "__main__":
    main()
