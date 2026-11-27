"""Pinned PyArrow streams for native LIST profile boundaries and refusal."""

from pathlib import Path
import sys

import pyarrow as pa

FIELD = "résultats"


def write(path, child, batches):
    list_type = pa.list_(pa.field(child, pa.int32(), nullable=True))
    schema = pa.schema([pa.field(FIELD, list_type, nullable=True)])
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5,
                                     use_legacy_format=False, compression=None)
    with pa.OSFile(str(path), "wb") as sink, pa.ipc.new_stream(sink, schema, options=options) as stream:
        for rows in batches:
            stream.write_batch(pa.record_batch([pa.array(rows, type=list_type)], schema=schema))
    with pa.ipc.open_stream(path) as stream:
        assert stream.schema == schema
        assert [batch.column(0).to_pylist() for batch in stream] == batches


def main(output):
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    output.mkdir(exist_ok=True, parents=True)
    write(output / "schema-only.arrows", "element", [])
    write(output / "empty-batch.arrows", "element", [[]])
    write(output / "noncanonical-child.arrows", "item", [[None, [], [None]], [[-7, None, 9]]])


if __name__ == "__main__":
    main(Path(sys.argv[1]))
