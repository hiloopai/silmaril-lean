"""Pin actual Lean seconds-writer images and independent PyArrow millisecond files."""

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
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SECONDS = runpy.run_path(str(HERE.parent / "arrow-seconds-to-parquet-oracle/check.py"))
THRIFT = SECONDS["WRITER"]["THRIFT"]
LOW, HIGH = SECONDS["LOW"], SECONDS["HIGH"]
EOS = struct.pack("<II", 0xFFFFFFFF, 0)
INDEPENDENT = {
    "utc_v1": ("UTC", True, "1.0", [[LOW * 1000, None, -1000, 0], [HIGH * 1000, 4000]]),
    "local_v2": (None, False, "2.0", [[-1000, 0], [LOW * 1000], [HIGH * 1000, 173000]]),
}


def produce(unit, zone, nullable, page_version, groups, *, extra_field=False):
    fields = [pa.field("time", pa.timestamp(unit, zone), nullable=nullable)]
    if extra_field:
        fields.append(pa.field("decoy", pa.int32(), nullable=False))
    schema = pa.schema(fields)
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version,
                          compression="NONE", use_dictionary=False,
                          store_schema=False, write_statistics=False) as writer:
        for slots in groups:
            columns = [pa.array(slots, type=pa.int64()).view(fields[0].type)]
            if extra_field:
                columns.append(pa.array(range(len(slots)), type=pa.int32()))
            writer.write_table(pa.Table.from_arrays(columns, schema=schema))
    wire = sink.getvalue().to_pybytes()
    reader = pq.ParquetFile(pa.BufferReader(wire))
    assert reader.metadata.num_row_groups == len(groups)
    assert [reader.read_row_group(i).column(0).cast(pa.int64()).to_pylist()
            for i in range(len(groups))] == groups
    return wire


def retag_last_page(wire, group):
    """Keep layout and body bytes, then give the last PLAIN page an unsupported encoding tag."""
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    column = parquet.metadata.row_group(group).column(0)
    start = column.data_page_offset
    cursor = TMemoryBuffer(wire[start:start + column.total_compressed_size])
    header = THRIFT["read_struct"](TCompactProtocol(cursor))
    size = cursor.cstringio_buf.tell()
    assert header[1][1] == 0 and header[5][1][2] == (TType.I32, 0)
    header[5][1][2] = TType.I32, 5
    retagged = THRIFT["encode"](header)
    assert len(retagged) == size
    return wire[:start] + retagged + wire[start + size:]


def fixtures():
    inputs = {name: produce("ms", zone, nullable, version, rows)
              for name, (zone, nullable, version, rows) in INDEPENDENT.items()}
    inputs["offgrid_negative"] = produce("ms", "UTC", True, "1.0",
                                        [[0], [-1000], [-1000, None, -1001, 1]])
    inputs["offgrid_positive"] = produce("ms", None, True, "2.0", [[0], [None, 0, 1001, -1]])
    native = produce("ms", None, True, "1.0", [[-1001, None], [0], [1000]])
    inputs["late_bad_source"] = retag_last_page(native, 2)
    inputs["wrong_unit"] = produce("us", None, False, "1.0", [[1000]])
    inputs["multi_field"] = produce("ms", None, False, "1.0", [[0]], extra_field=True)
    inputs["page_less"] = produce("ms", "UTC", False, "2.0", [[0], [], [-1000]])
    return inputs


def seconds_counts(values):
    assert all(value % 1000 == 0 for batch in values for value in batch if value is not None)
    return [[None if value is None else value // 1000 for value in batch] for batch in values]


def verify_source(wire, zone, nullable, millis):
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    assert parquet.schema_arrow.field(0).equals(pa.field("time", pa.timestamp("ms", zone), nullable=nullable))
    assert parquet.metadata.num_row_groups == len(millis)
    assert [parquet.read_row_group(i).column(0).cast(pa.int64()).to_pylist()
            for i in range(len(millis))] == millis
    assert parquet.schema.column(0).physical_type == "INT64"
    footer = SECONDS["WRITER"]["footer"](wire)
    leaf = THRIFT["list_field"](footer, 2)[1]
    timestamp = leaf[10][1][8][1]
    assert timestamp[1] == (TType.BOOL, zone == "UTC") and list(timestamp[2][1]) == [1]
    assert [group[3][1] for group in THRIFT["list_field"](footer, 4)] == list(map(len, millis))


def verify_ipc(wire, zone, nullable, seconds):
    source = pa.BufferReader(wire)
    schema = pa.schema([pa.field("time", pa.timestamp("s", zone), nullable=nullable)])
    with pa.ipc.open_stream(source) as reader:
        assert reader.schema.equals(schema, check_metadata=True)
        assert [batch.column(0).cast(pa.int64()).to_pylist() for batch in reader] == seconds
    assert source.tell() == len(wire) and wire.endswith(EOS)
    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(seconds)
    assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
    print(f"{schema.field(0).type}: batches {list(map(len, seconds))}, SHA-256 {sha256(wire).hexdigest()}")


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    pins = json.loads((HERE / "fixtures.json").read_text())
    sources = fixtures()
    assert {name: sha256(wire).hexdigest() for name, wire in sources.items()} == pins["independent"]
    seconds_streams = {name: SECONDS["ARROW"]["timestamp_stream"]("s", zone, groups, nullable)
                       for name, (zone, nullable, groups) in SECONDS["POSITIVE"].items()}
    assert {name: sha256(wire).hexdigest() for name, wire in seconds_streams.items()} == pins["original_seconds"]
    with tempfile.TemporaryDirectory(prefix="parquet-millis-to-arrow-seconds-") as temporary:
        directory = Path(temporary)
        for name, wire in sources.items():
            (directory / (name + ".parquet")).write_bytes(wire)
        for name, wire in seconds_streams.items():
            (directory / (name + "-input.arrows")).write_bytes(wire)
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(directory)],
                       cwd=ROOT, check=True)
        assert {file.stem for file in directory.glob("*.arrows") if not file.stem.endswith("-input")} == {
            *INDEPENDENT, *("image_" + name for name in SECONDS["POSITIVE"])}
        for name, (zone, nullable, _, millis) in INDEPENDENT.items():
            verify_source(sources[name], zone, nullable, millis)
            verify_ipc((directory / (name + ".arrows")).read_bytes(), zone, nullable, seconds_counts(millis))
        for name, (zone, nullable, original) in SECONDS["POSITIVE"].items():
            image = "image_" + name
            parquet = (directory / (image + ".parquet")).read_bytes()
            assert sha256(parquet).hexdigest() == pins["lean_parquet"][name]
            millis = [[None if slot is None else slot * 1000 for slot in row] for row in original]
            verify_source(parquet, zone, nullable, millis)
            verify_ipc((directory / (image + ".arrows")).read_bytes(), zone, nullable, original)


if __name__ == "__main__":
    main()
