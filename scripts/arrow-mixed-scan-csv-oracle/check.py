"""Check native mixed Arrow IPC and typed UTF-8 CSV with PyArrow and CPython."""

import argparse
import csv
from hashlib import sha256
import io
import os
from pathlib import Path
import subprocess
import sys

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PINS = {
    "mixed.arrows": "00dbda52bd8196ef42269c29a285a74f500870ea437d0767879859695a8ec523",
    "schema-only.arrows": "4eb2c8b25f324545fefe6ca4aab21fd474c4f4d52ec7480cb850f1e2d166c6e5",
    "zero-width.arrows": "1e31d71e6ad5132110f1fc3f7cef27e9a51e6c7fc6631cef8f4469c1e60ba149",
    "opaque.arrows": "0ac8141c92264850e8b4ed7dbf580560bb868c3f8e44c7f6fe88b0eedcb837be",
    "invalid-text.arrows": "5271b93716378d3cc106f69acb977f2d14e52fbc962e4bd9f0ffa31708488002",
    "mixed.lean.csv": "4e8710e43f56e102eff78b44b35639d9665ebcb8e9d7124b4fb9cf0e3cc47d1d",
    "schema-only.lean.csv": "92bd7e747f469b51e113d04cc7db3aa71723977125a0cb051a3ba83750837d54",
    "zero-width.lean.csv": "a4ac417d5aea856b02ffcc1e240cfe3c55ef44073e5d893673dbb9fe6e741bc4",
}
SUCCESS = ("mixed", "schema-only", "zero-width")


def write_stream(path, schema, batches):
    with pa.OSFile(str(path), "wb") as sink, pa.ipc.new_stream(sink, schema) as stream:
        for batch in batches:
            stream.write_batch(batch)


def make_batch(schema, columns):
    return pa.RecordBatch.from_arrays(
        [pa.array(values, type=field.type) for field, values in zip(schema, columns, strict=True)],
        schema=schema,
    )


def write_ipc(out):
    schema = pa.schema([
        pa.field("téxt", pa.string_view()),
        pa.field("amount", pa.int32()),
        pa.field("téxt", pa.string()),
        pa.field("required", pa.int32(), nullable=False),
    ])
    values = [
        ["", "N", None, 'été,\r\n"🌿" longer than twelve bytes'],
        [-2147483648, None, 0, 2147483647],
        ["T", None, "N", "東京"],
        [1, 2, 3, 4],
    ]
    batches = [
        make_batch(schema, [column[start:stop] for column in values])
        for start, stop in [(0, 2), (2, 2), (2, 4)]
    ]
    write_stream(out / "mixed.arrows", schema, batches)
    write_stream(out / "schema-only.arrows", schema, [])
    zero = pa.RecordBatch.from_struct_array(pa.array([{}, {}], type=pa.struct([])))
    write_stream(out / "zero-width.arrows", zero.schema, [zero])
    opaque = pa.schema([pa.field("raw", pa.binary_view())])
    write_stream(out / "opaque.arrows", opaque, [make_batch(opaque, [[b"\xff\x00"]])])
    text = pa.schema([pa.field("text", pa.string())])
    write_stream(out / "invalid-text.arrows", text, [make_batch(text, [["a\x00b"]])])


def expected_csv(path):
    wire = path.read_bytes()
    assert wire.endswith(bytes.fromhex("ffffffff00000000"))
    with pa.ipc.open_stream(wire) as reader:
        rows = [reader.schema.names or [""]]
        for batch in reader:
            columns = [column.to_pylist() for column in batch.columns]
            rows.extend([
                ["N" if column[i] is None else f"T{column[i]}" for column in columns] or [""]
                for i in range(batch.num_rows)
            ])
    return rows


def write_csv(path, rows):
    with path.open("w", encoding="utf-8", newline="") as stream:
        csv.writer(stream, lineterminator="\r\n").writerows(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert sys.version_info[:2] == (3, 13)
    write_ipc(out)
    expected = {name: expected_csv(out / f"{name}.arrows") for name in SUCCESS}
    for name, rows in expected.items():
        write_csv(out / f"{name}.python.csv", rows)
    assert expected["mixed"][0] == ["téxt", "amount", "téxt", "required"]
    assert expected["zero-width"] == [[""], [""], [""]]
    for name, row, column, value in [
        ("wrong-header", 0, 1, "wrong"),
        ("bad-integer", 1, 1, "T01"),
        ("required-null", 2, 3, "N"),
    ]:
        rows = [row.copy() for row in expected["mixed"]]
        rows[row][column] = value
        write_csv(out / f"{name}.csv", rows)
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    for name, rows in expected.items():
        encoded = (out / f"{name}.lean.csv").read_bytes().decode("utf-8")
        assert list(csv.reader(io.StringIO(encoded, newline=""), strict=True)) == rows, name
    for name, expected_hash in PINS.items():
        digest = sha256((out / name).read_bytes()).hexdigest()
        print(f"{digest}  {name}")
        assert digest == expected_hash, f"{name}: fixture hash changed"
    print("PyArrow and CPython agree with Lean on positional headers, nullable text and integers, and empty data.")


if __name__ == "__main__":
    main()
