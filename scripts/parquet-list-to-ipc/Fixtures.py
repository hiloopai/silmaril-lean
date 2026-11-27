"""Generate empty-boundary controls for the existing Parquet LIST profile."""

from io import BytesIO
from pathlib import Path
import runpy
import struct
import sys

from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

o = runpy.run_path(str(Path(__file__).resolve().parents[1] / "parquet-list-file" / "Oracle.py"))
pa, pq = o["pa"], o["pq"]
parse, record, items = o["parse"], o["record"], o["items"]
i32, i64, binary = o["i32"], o["i64"], o["binary"]

column_metadata = record({1: i32, 2: items(i32), 3: items(binary), 4: i32, 5: i64, 6: i64, 7: i64, 9: i64})
chunk = record({2: i64, 3: column_metadata})
group = record({1: items(chunk), 2: i64, 3: i64})
footer = {**o["footer"], 1: i32, 4: items(group)}
page = o["page"]
ROOT = Path(__file__).resolve().parents[2]
NATIVE = ROOT / "data/parquet-list-file/nullable-int32-v1.parquet"


def write_value(protocol, spec, value):
    kind, shape = spec
    if kind == TType.STRUCT:
        protocol.writeStructBegin("")
        for tag, item in sorted(value.items()):
            protocol.writeFieldBegin("", shape[tag][0], tag)
            write_value(protocol, shape[tag], item)
            protocol.writeFieldEnd()
        protocol.writeFieldStop()
        protocol.writeStructEnd()
    elif kind == TType.LIST:
        element, detail = shape
        protocol.writeListBegin(element, len(value))
        for item in value:
            write_value(protocol, (element, detail), item)
        protocol.writeListEnd()
    else:
        {TType.I32: protocol.writeI32, TType.I64: protocol.writeI64,
         TType.STRING: protocol.writeBinary}[kind](value)


def compact(schema, value):
    buffer = TMemoryBuffer()
    write_value(TCompactProtocol(buffer), record(schema), value)
    return buffer.getvalue()


def metadata(data):
    size = struct.unpack_from("<I", data, len(data) - 8)[0]
    start = len(data) - 8 - size
    result, consumed = parse(data[start:-8], footer)
    assert consumed == size
    return start, result


def make_empty_group(native):
    footer_start, meta = metadata(native)
    assert len(meta[4]) == 2
    columns = [entry[1][0][3] for entry in meta[4]]
    frames = [native[column[9]:column[9] + column[7]] for column in columns]
    assert native[:footer_start] == b"PAR1" + b"".join(frames)

    # Both length-prefixed V1 Hybrid sections are empty, as is the INT32 suffix.
    body = bytes(8)
    header = compact(page, {1: 0, 2: 8, 3: 8, 5: {1: 0, 2: 0, 3: 3, 4: 3}})
    empty = header + body
    empty_offset = 4 + len(frames[0])
    empty_column = {**columns[0], 5: 0, 6: len(empty), 7: len(empty), 9: empty_offset}
    meta[4].insert(1, {1: [{2: 0, 3: empty_column}], 2: len(empty), 3: 0})
    columns[1][9] += len(empty)
    file_footer = compact(footer, meta)
    source = b"PAR1" + frames[0] + empty + frames[1] + file_footer + struct.pack("<I", len(file_footer)) + b"PAR1"
    start, observed = metadata(source)
    assert observed == meta
    assert start == footer_start + len(empty)
    parquet = pq.ParquetFile(BytesIO(source))
    assert parquet.num_row_groups == 3
    assert parquet.read_row_group(1, use_threads=False).num_rows == 0
    assert parquet.read(use_threads=False).equals(pq.ParquetFile(BytesIO(native)).read(use_threads=False))
    return source


def main(output):
    assert pa.__version__ == "26.0.1"
    output.mkdir(exist_ok=True, parents=True)
    schema = pa.schema([pa.field("samples", pa.list_(pa.field("element", pa.int32(), nullable=True)))])
    writer_options = {"use_dictionary": False, "compression": "NONE", "data_page_version": "1.0",
                      "write_statistics": False}
    path = output / "no-groups.parquet"
    with pq.ParquetWriter(path, schema, **writer_options):
        pass
    _, meta = metadata(path.read_bytes())
    assert meta[3] == 0 and meta[4] == []
    assert pq.ParquetFile(path).num_row_groups == 0

    # A native empty WriteTable has an empty chunk. Keep it as a refusal control.
    pathless = output / "unframed-empty.parquet"
    pq.write_table(pa.Table.from_batches([], schema), pathless, **writer_options)
    _, meta = metadata(pathless.read_bytes())
    assert len(meta[4]) == 1 and meta[4][0][1][0][3][7] == 0

    (output / "empty-framed-group.parquet").write_bytes(make_empty_group(NATIVE.read_bytes()))


if __name__ == "__main__":
    main(Path(sys.argv[1]))
