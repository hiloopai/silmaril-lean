"""Verify Arrow IPC file fixture hashes or reproduce them with pinned PyArrow."""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
STREAM = json.loads((HERE / "fixture.json").read_text(encoding="utf-8"))
MANIFEST = json.loads((HERE / "file-fixtures.json").read_text(encoding="utf-8"))


def generate():
    import numpy as np
    import pyarrow as pa

    producer = STREAM["producer"]
    assert np.__version__ == producer["numpy_version"]
    assert pa.__version__ == pa.cpp_build_info.version == producer["version"]
    schema = pa.schema([pa.field("n", pa.int32()), pa.field("téxt", pa.string())])
    options = pa.ipc.IpcWriteOptions(
        metadata_version=pa.ipc.MetadataVersion.V5, use_legacy_format=False, compression=None
    )
    flat = [
        pa.RecordBatch.from_arrays(
            [pa.array([row[field.name] for row in rows], type=field.type) for field in schema],
            schema=schema,
        )
        for rows in STREAM["batches"]
    ]
    zero_columns = [
        pa.RecordBatch.from_struct_array(pa.array([{}] * count, type=pa.struct([])))
        for count in [3, 0]
    ]
    dictionary = pa.record_batch([pa.array(["é", None, "é"]).dictionary_encode()], names=["d"])
    wide = pa.record_batch([pa.array([1], type=pa.int64())], names=["wide"])
    specimens = {
        "file-mixed.arrow": (schema, flat, STREAM["batches"]),
        "file-schema-only.arrow": (schema, [], []),
        "file-zero-columns.arrow": (pa.schema([]), zero_columns, [[{}, {}, {}], []]),
        "file-dictionary.arrow": (dictionary.schema, [dictionary], [[{"d": "é"}, {"d": None}, {"d": "é"}]]),
        "file-int64.arrow": (wide.schema, [wide], [[{"wide": 1}]]),
    }
    for name, (fields, batches, expected) in specimens.items():
        sink = pa.BufferOutputStream()
        with pa.ipc.new_file(sink, fields, options=options) as output:
            for batch in batches:
                output.write_batch(batch)
        data = sink.getvalue().to_pybytes()
        with pa.ipc.open_file(data) as reader:
            assert reader.schema == fields
            observed = [reader.get_batch(i) for i in range(reader.num_record_batches)]
            assert [batch.num_rows for batch in observed] == [len(rows) for rows in expected]
            assert [batch.to_pylist() for batch in observed] == expected
        yield name, data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--regenerate", action="store_true")
    args = parser.parse_args()
    fixtures = MANIFEST["sha256"]
    sources = generate() if args.regenerate else ((name, (HERE / name).read_bytes()) for name in fixtures)
    for name, data in sources:
        digest = hashlib.sha256(data).hexdigest()
        if digest != fixtures[name]:
            raise SystemExit(f"{name}: unexpected SHA-256 {digest}")
        if args.regenerate:
            (HERE / name).write_bytes(data)
        print(f"{name}: SHA-256 {digest}")


if __name__ == "__main__":
    main()
