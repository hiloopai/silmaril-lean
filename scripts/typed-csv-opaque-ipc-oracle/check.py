"""Check actual IPC and canonical tagged opaque CSV against PyArrow and CPython."""

import argparse
import csv
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OPAQUE = [[None, b""], [], [b"\x00\xff\x80\t\r\n", bytes(range(256)), b"a\x00z"]]
CASES = [
    ("view", pa.field("octets, café", pa.binary_view()), OPAQUE),
    ("binary", pa.field("octets, café", pa.binary()), OPAQUE),
    ("schema-only", pa.field("empty", pa.binary_view()), []),
    ("required", pa.field("required", pa.binary(), nullable=False), [[b"", b"\xfe\x00"], []]),
]


def write_ipc(path, field, batches):
    schema = pa.schema([field])
    with pa.OSFile(str(path), "wb") as sink, pa.ipc.new_stream(sink, schema) as stream:
        for values in batches:
            stream.write_batch(pa.RecordBatch.from_arrays([pa.array(values, type=field.type)], schema=schema))


def read_ipc(path, field):
    wire = path.read_bytes()
    assert wire.endswith(bytes.fromhex("ffffffff00000000"))
    with pa.BufferReader(wire) as carrier, pa.ipc.open_stream(carrier) as stream:
        assert stream.schema.equals(pa.schema([field]))
        values = []
        for batch in stream:
            batch.validate(full=True)
            values.append(batch.column(0).to_pylist())
        assert carrier.tell() == len(wire)
    with pa.BufferReader(wire) as carrier:
        messages = list(pa.ipc.MessageReader.open_stream(carrier))
        assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(values)
        assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
        assert carrier.tell() == len(wire)
    return values


def typed_rows(field, values):
    return [[field.name]] + [["N" if value is None else "T" + value.hex().upper()] for value in values]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    producer = out / "producer"
    producer.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert sys.version_info[:2] == (3, 13)

    expected = {}
    for name, field, batches in CASES:
        input_wire = producer / f"{name}.arrows"
        write_ipc(input_wire, field, batches)
        observed = read_ipc(input_wire, field)
        assert observed == batches
        values = [value for batch in observed for value in batch]
        expected[name] = (values, typed_rows(field, values))
        with (producer / f"{name}.csv").open("w", encoding="utf-8", newline="") as stream:
            csv.writer(stream, lineterminator="\r\n").writerows(expected[name][1])
    write_ipc(producer / "text.arrows", pa.field("text", pa.string_view()), [["é"]])

    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    for name, field, _ in CASES:
        values, rows = expected[name]
        with (out / f"{name}.csv").open(encoding="utf-8", newline="") as stream:
            assert list(csv.reader(stream, strict=True)) == rows
        assert read_ipc(out / f"{name}.arrows", field) == [values]

    pins = json.loads((HERE / "sha256.json").read_text())
    assert set(pins) == {"producer/text.arrows"} | {
        f"{prefix}{name}.{suffix}"
        for name, _, _ in CASES for prefix in ("", "producer/") for suffix in ("arrows", "csv")
    }
    for name, digest in pins.items():
        actual = sha256((out / name).read_bytes()).hexdigest()
        assert actual == digest, f"{name}: fixture hash changed"
        print(f"{actual}  {name}")
    print("PyArrow and CPython agree on both opaque layouts, canonical hex, ordered rows and exact EOS.")


if __name__ == "__main__":
    main()
