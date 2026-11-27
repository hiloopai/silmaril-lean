"""Pin PyArrow GZIP dictionaries and compare Lean BinaryView with PyArrow rows."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
from runpy import run_path
from struct import pack, unpack_from
import subprocess
import sys
from typing import NamedTuple
from zlib import crc32, decompressobj

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


assert (version("pyarrow"), version("thrift")) == ("26.0.1", "0.25.0")
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
THRIFT = run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
DICTIONARIES = [[b"", b"\xff\x00", b"\xed\xa0\x80", bytes([0xfe, group]) * 8, b"\xfe\x80unused"]
                for group in range(2)]
INDICES = [0, None, 1, 0, 3, 2, 0, 1, 0]
EXPECTED = [[entries[i] if i is not None else None for i in INDICES] for entries in DICTIONARIES]


class Frame(NamedTuple):
    header: int
    body: int
    stop: int
    fields: dict


def produce(page_version, crc):
    schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False),
                        pa.field("blob", pa.dictionary(pa.int8(), pa.binary()))])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", compression="GZIP", data_page_version=page_version,
                          use_dictionary=["blob"], write_batch_size=8, data_page_size=1,
                          write_statistics=False, store_schema=False, write_page_checksum=crc) as writer:
        for entries in DICTIONARIES:
            array = pa.DictionaryArray.from_arrays(pa.array(INDICES, pa.int8()), pa.array(entries, pa.binary()))
            writer.write_table(pa.Table.from_arrays([pa.array(range(len(INDICES)), pa.int32()), array], schema=schema))
    return sink.getvalue().to_pybytes()


def read_footer(wire):
    size, = unpack_from("<I", wire, len(wire) - 8)
    start = len(wire) - 8 - size
    transport = TMemoryBuffer(wire[start:-8])
    fields = THRIFT["read_struct"](TCompactProtocol(transport))
    assert transport.cstringio_buf.tell() == size
    return start, fields


def frames(wire, chunk, has_crc):
    start = chunk.dictionary_page_offset
    stop = start + chunk.total_compressed_size
    transport = TMemoryBuffer(wire[start:stop])
    protocol = TCompactProtocol(transport)
    result = []
    while transport.cstringio_buf.tell() < chunk.total_compressed_size:
        offset = start + transport.cstringio_buf.tell()
        header = THRIFT["read_struct"](protocol)
        body = start + transport.cstringio_buf.tell()
        payload = transport.readAll(header[3][1])
        assert (4 in header) == has_crc
        if has_crc:
            assert header[4][1] % 2**32 == crc32(payload)
        result.append(Frame(offset, body, body + len(payload), header))
    assert result[-1].stop == stop
    assert result[0].stop == chunk.data_page_offset
    assert sum(frame.body - frame.header + frame.fields[2][1] for frame in result) == chunk.total_uncompressed_size
    return result


def expand(body):
    member = decompressobj(wbits=31)
    expanded = member.decompress(body) + member.flush()
    assert member.eof and not member.unused_data and not member.unconsumed_tail
    return expanded


def inspect(wire, version, crc):
    footer_start, footer = read_footer(wire)
    leaf = THRIFT["list_field"](footer, 2)[2]
    assert leaf[1] == (TType.I32, 6) and leaf[3] == (TType.I32, 1)
    assert 6 not in leaf and 10 not in leaf
    geometry = []
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        assert file.schema_arrow.field("blob") == pa.field("blob", pa.binary())
        assert file.num_row_groups == len(EXPECTED)
        for group, values in enumerate(EXPECTED):
            assert file.read_row_group(group, columns=["blob"]).column(0).to_pylist() == values
            chunk = file.metadata.row_group(group).column(1)
            assert chunk.compression == "GZIP" and chunk.path_in_schema == "blob"
            assert set(chunk.encodings) == {"PLAIN", "RLE", "RLE_DICTIONARY"}
            dictionary, *data = frames(wire, chunk, crc)
            assert data[-1].stop <= footer_start
            assert dictionary.fields[1][1] == 2
            dictionary_header = dictionary.fields[7][1]
            assert (dictionary_header[1][1], dictionary_header[2][1]) == (5, 0)
            dictionary_bytes = expand(wire[dictionary.body:dictionary.stop])
            assert len(dictionary_bytes) == dictionary.fields[2][1]
            assert dictionary_bytes == b"".join(pack("<I", len(entry)) + entry for entry in DICTIONARIES[group])
            if version == "1.0":
                for frame, count in zip(data, (8, 1), strict=True):
                    assert frame.fields[1][1] == 0
                    assert [frame.fields[5][1][i][1] for i in (1, 2, 3, 4)] == [count, 8, 3, 3]
                    assert len(expand(wire[frame.body:frame.stop])) == frame.fields[2][1]
            else:
                assert all(frame.fields[1][1] == 3 and frame.fields[8][1][4][1] == 8 for frame in data)
            geometry.append([dictionary, *data])
    return geometry


def add_member(wire, frame):
    footer_start, footer = read_footer(wire)
    assert frame.stop == footer_start
    # An independent RFC 1952 empty member, after the original complete member.
    suffix = bytes.fromhex("1f8b080000000000000303000000000000000000")
    assert expand(suffix) == b""
    fields = {**frame.fields, 3: (TType.I32, frame.fields[3][1] + len(suffix))}
    header = THRIFT["encode"](fields)
    header_delta = len(header) - (frame.body - frame.header)
    row_group = THRIFT["list_field"](footer, 4)[1]
    column = THRIFT["column_metadata"](footer, 1, 1)
    for record, key, delta in [(column, 6, header_delta), (column, 7, header_delta + len(suffix)),
                               (row_group, 2, header_delta), (row_group, 6, header_delta + len(suffix))]:
        kind, size = record[key]
        record[key] = (kind, size + delta)
    new_footer = THRIFT["encode"](footer)
    return (wire[:frame.header] + header + wire[frame.body:frame.stop] + suffix
            + new_footer + pack("<I", len(new_footer)) + b"PAR1")


def produce_fallback():
    values = [[b"a", b"\xff", None, b""] * 16,
              [b"a", b"\xff", None, b""] * 8 + [b"\x80" + bytes([i]) + b"long" * 5 for i in range(32)]]
    sink = pa.BufferOutputStream()
    pq.write_table(pa.table({"ordinal": pa.array(range(128), pa.int32()), "blob": sum(values, [])}), sink,
                   version="2.6", compression="GZIP", data_page_version="1.0", use_dictionary=["blob"],
                   data_page_size=16, dictionary_pagesize_limit=64, write_batch_size=8, row_group_size=64,
                   write_statistics=False, store_schema=False, write_page_checksum=True)
    wire = sink.getvalue().to_pybytes()
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        assert [file.read_row_group(i, columns=["blob"]).column(0).to_pylist() for i in range(2)] == values
        groups = [frames(wire, file.metadata.row_group(i).column(1), True) for i in range(2)]
        tags = [[frame.fields[5][1][2][1] for frame in group[1:]] for group in groups]
        assert tags == [[8] * 8, [8] * 5 + [0] * 3]
        print(f"genuine fallback data tags {tags}", flush=True)
        return wire, groups[1][6].header



def main(out):
    out.mkdir(parents=True, exist_ok=True)
    cases = {}
    geometry = {}
    for name, version_number, crc in [("v1-absent", "1.0", False), ("v1-crc", "1.0", True), ("v2", "2.0", True)]:
        cases[name] = produce(version_number, crc)
        geometry[name] = inspect(cases[name], version_number, crc)
        print(f"{name}: original headers {[[frame.header for frame in group] for group in geometry[name]]}", flush=True)

    crc_frame = geometry["v1-crc"][1][-1]
    crc_wire = cases["v1-crc"]
    cases["bad-crc"] = crc_wire[:crc_frame.body] + bytes([crc_wire[crc_frame.body] ^ 1]) + crc_wire[crc_frame.body + 1:]
    member_frame = geometry["v1-absent"][1][-1]
    cases["extra-member"] = add_member(cases["v1-absent"], member_frame)
    cases["fallback"], fallback_offset = produce_fallback()
    sink = pa.BufferOutputStream()
    pq.write_table(pa.table({"blob": ["雪", None, ""]}), sink, compression="GZIP", data_page_version="1.0",
                   use_dictionary=["blob"], write_statistics=False, store_schema=False)
    cases["string"] = sink.getvalue().to_pybytes()
    _, string_footer = read_footer(cases["string"])
    assert 10 in THRIFT["list_field"](string_footer, 2)[1]
    for name in ("bad-crc", "extra-member"):
        with pq.ParquetFile(pa.BufferReader(cases[name]), page_checksum_verification=True) as file:
            assert file.read_row_group(0, columns=["blob"]).column(0).to_pylist() == EXPECTED[0]
    bad_crc = crc32(cases["bad-crc"][crc_frame.body:crc_frame.stop])
    assert bad_crc != crc_frame.fields[4][1] % 2**32
    for name, wire in cases.items():
        (out / f"{name}.parquet").write_bytes(wire)

    subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                    "--run", str(HERE / "Emit.lean"), str(out), str(crc_frame.header), str(member_frame.header),
                    str(geometry["v2"][0][1].header), str(geometry["v1-absent"][0][0].header), str(fallback_offset),
                    str(crc_frame.fields[4][1] % 2**32), str(bad_crc)],
                   cwd=ROOT, check=True)
    outputs = ["v1-absent", "v1-crc"]
    for name in outputs:
        with pq.ParquetFile(out / f"{name}.parquet", page_checksum_verification=True) as source, \
                pa.ipc.open_stream(out / f"{name}.arrows") as reader:
            assert reader.schema == pa.schema([pa.field("blob", pa.binary_view())])
            assert [batch.column(0).to_pylist() for batch in reader] == [
                source.read_row_group(i, columns=["blob"]).column(0).to_pylist() for i in range(source.num_row_groups)]

    artifacts = [out / f"{name}.parquet" for name in cases] + [out / f"{name}.arrows" for name in outputs]
    pins = {path.name: sha256(path.read_bytes()).hexdigest() for path in artifacts}
    print(json.dumps(pins, indent=2), flush=True)
    assert pins == json.loads((HERE / "fixtures.json").read_text())
    print("PyArrow/Thrift: exact dictionary octets, single GZIP members, [9, 9] BinaryView rows and pin replay")


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve())
