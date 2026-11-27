#!/usr/bin/env python3
"""Replay exact CRC-bearing Parquet BROTLI pages against pinned native tools."""
import argparse
from hashlib import sha256
from importlib.metadata import version
import io
import json
from pathlib import Path
import runpy
from struct import pack
import subprocess
from tempfile import TemporaryDirectory
from zlib import crc32

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
RAW = runpy.run_path(str(SCRIPTS / "parquet-brotli-raw/check.py"))
MAPS = runpy.run_path(str(SCRIPTS / "brotli-context-maps/check.py"))
PIN, check, run, fields = (RAW[name] for name in ("PIN", "check", "run", "fields"))


def producer(rows, kind, page_version, quality):
    result = io.BytesIO()
    table = pa.table({"x": pa.array(rows, type=kind)})
    pq.write_table(table, result, compression="brotli", compression_level=quality, version="2.6",
                   data_page_version=page_version, use_dictionary=False, column_encoding="PLAIN",
                   write_statistics=False, write_page_checksum=True, row_group_size=len(rows))
    return result.getvalue()


def read_frame(data, start):
    protocol = TCompactProtocol(TMemoryBuffer(data[start:]))
    header, _ = fields(protocol, {5: fields, 8: fields})
    body_start = start + protocol.trans.cstringio_buf.tell()
    end = body_start + header[3]
    check(end <= len(data), "Thrift body extent")
    kind = header[1]
    if kind == 3:
        v2 = header[8][0]
        check(v2[4] == 0 and v2[6] == 0, "flat PLAIN V2")
        prefix = v2[5]
        flag = v2.get(7)
    else:
        v1 = header[5][0]
        check(kind == 0 and [v1[k] for k in (2, 3, 4)] == [0, 3, 3], "flat PLAIN V1")
        prefix, flag = 0, None
    checksum = header[4] % (1 << 32) if 4 in header else None
    return {"header": header, "header_span": [start, body_start], "body_span": [body_start, end],
            "stored": data[body_start:end], "expanded": header[2], "kind": kind,
            "prefix": prefix, "flag": flag, "crc": checksum}


def native_plain(frame, reference, traced, expected_values):
    body = frame["stored"]
    check(frame["crc"] == crc32(body), "independent CRC over the original on-disk body")
    size = frame["prefix"]
    encoded = body[size:]
    hits = []
    if frame["flag"] is not False:
        values = run(reference, "-d", "-c", data=encoded)
        trace = MAPS["native_trace"](encoded, reference, traced)
        hits = [list(map(int, row.split()[1:])) for row in trace if row.startswith("dictionary_emit ")]
        check(len(hits) > 0, "native dictionary dependency")
        first = next(row for row in trace if row.startswith("payload "))
        first_command = 8 * len(encoded) - int(first.split()[1])
    else:
        values = encoded
        first_command = None
    if frame["kind"] == 0:
        levels = values[:-len(expected_values)]
        check(len(levels) >= 4 and int.from_bytes(levels[:4], "little") == len(levels) - 4
              and values.endswith(expected_values), "V1 level extent and independent PLAIN byte array")
    else:
        check(values == expected_values, "V2 exact independent PLAIN values")
    plain = body[:size] + values
    check(len(plain) == frame["expanded"], "native expanded extent")
    return plain, hits, first_command


def lean(work, data, frame, mode="file", **overrides):
    path = work / "input"
    path.write_bytes(data)
    caps = {"compressed": len(frame["stored"]), "uncompressed": frame["expanded"], "window": (1 << 24) - 16,
            "bits": 8 * len(frame["stored"]), "blocks": 8, "commands": 4096, "codec": -1}
    caps.update(overrides)
    args = [str(value) for value in caps.values()]
    return json.loads(run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                          "--run", HERE / "Interop.lean", path, mode, *args))


def expect_match(work, data, frame, plain, mode="file", **caps):
    actual = lean(work, data, frame, mode, **caps)
    expected = {"header": frame["header_span"], "payload": frame["body_span"], "crc": frame["crc"],
                "expanded": list(plain), "legacyRefused": True}
    check(actual == expected, f"Lean exact frame and bytes: {str(actual)[:350]}")


def author(frame, stored, expanded=None, flag=None, crc=True):
    """Encode a standalone Compact Thrift page and an exact body, without a footer."""
    buffer = TMemoryBuffer()
    protocol = TCompactProtocol(buffer)

    def integer(number, value):
        protocol.writeFieldBegin("", TType.I32, number)
        protocol.writeI32(value)
        protocol.writeFieldEnd()

    protocol.writeStructBegin("PageHeader")
    integer(1, frame["kind"])
    integer(2, frame["expanded"] if expanded is None else expanded)
    integer(3, len(stored))
    if crc:
        checksum = crc32(stored)
        integer(4, checksum if checksum < 1 << 31 else checksum - (1 << 32))
    number = 5 if frame["kind"] == 0 else 8
    protocol.writeFieldBegin("", TType.STRUCT, number)
    protocol.writeStructBegin("DataPageHeader")
    for key, value in sorted(frame["header"][number][0].items()):
        if number == 8 and key == 7:
            continue
        integer(key, value)
    if number == 8 and flag is not None:
        protocol.writeFieldBegin("", TType.BOOL, 7)
        protocol.writeBool(flag)
        protocol.writeFieldEnd()
    protocol.writeFieldStop()
    protocol.writeStructEnd()
    protocol.writeFieldEnd()
    protocol.writeFieldStop()
    protocol.writeStructEnd()
    return buffer.getvalue() + stored


def summarize(data, frame, plain, provenance, dictionary=None):
    return {"provenance": provenance, "input_sha256": sha256(data).hexdigest(), "header": frame["header_span"],
            "body": frame["body_span"], "crc": frame["crc"], "v2_flag": frame["flag"],
            "level_bytes": frame["prefix"], "expanded_bytes": len(plain),
            "stored_sha256": sha256(frame["stored"]).hexdigest(), "expanded_sha256": sha256(plain).hexdigest(),
            "dictionary_transforms": dictionary or []}


def collect(work, reference, traced):
    rows = [None if i % 17 == 0 else f"Reader {i % 23} checks compressed page {i} with a fixed output budget."
            for i in range(99)]
    strings = b"".join(pack("<I", len(value)) + value for row in rows if row is not None
                       for value in [row.encode()])
    integers = [None if i % 8 == 1 else int.from_bytes(sha256(i.to_bytes(4, "little")).digest()[:4],
                                                      "little", signed=True) for i in range(128)]
    int_bytes = b"".join(pack("<i", n) for n in integers if n is not None)
    profiles, originals, controls = {}, {}, {}

    def reject(name, data, frame, expected, mode="file", **overrides):
        found = lean(work, data, frame, mode, **overrides)
        check(found == expected, f"{name}: {found}")
        controls[name] = expected

    for name, page_version, quality, values, kind, encoded in (
        ("native-v1-dictionary", "1.0", 7, rows, pa.string(), strings),
        ("native-v2-dictionary", "2.0", 7, rows, pa.string(), strings),
        ("native-v2-raw", "2.0", 0, integers, pa.int32(), int_bytes),
    ):
        data = producer(values, kind, page_version, quality)
        file = pq.ParquetFile(pa.BufferReader(data), page_checksum_verification=True)
        check(file.read().column("x").to_pylist() == values, "PyArrow CRC-checked readback")
        col = file.metadata.row_group(0).column(0)
        check(col.compression == "BROTLI" and col.dictionary_page_offset is None, "codec 4 without Parquet dictionary")
        frame = read_frame(data, col.data_page_offset)
        check(frame["body_span"][1] == col.data_page_offset + col.total_compressed_size, "exact native one-page chunk")
        check(frame["flag"] == (None if page_version == "1.0" else quality != 0), "native compression flag")
        plain, hits, first_command = native_plain(frame, reference, traced, encoded)
        caps = {"window": 0, "bits": 0, "blocks": 0, "commands": 0} if frame["flag"] is False else {}
        expect_match(work, data, frame, plain, **caps)
        profiles[name] = summarize(data, frame, plain, "PyArrow native page with CRC", hits)
        originals[name] = data, frame, plain
        print(f"{name}: {len(frame['stored'])} CRC-checked stored bytes, {len(plain)} expanded, {len(hits)} dictionary references")
        if frame["kind"] == 0:
            reject("command-cap", data, frame, {"error": "commandCap", "block": 0, "command": 0, "bit": first_command},
                   commands=0)
            reject("window-cap", data, frame, {"error": "windowCap", "bit": 0}, window=0)
            reject("wrong-codec", data, frame, {"error": "codec", "actual": 6}, codec=6)
            reject("stored-cap", data, frame, {"error": "storedCap"}, compressed=len(frame["stored"]) - 1)
            reject("caller-output-cap", data, frame, {"error": "outputCap"}, uncompressed=len(plain) - 1)
        if frame["prefix"] > 0:
            mutated = bytearray(data)
            start, stop = frame["body_span"]
            mutated[start] ^= 1
            reject(f"{name}-bad-level-crc", bytes(mutated), frame,
                   {"error": "checksum", "declared": frame["crc"], "computed": crc32(mutated[start:stop])},
                   commands=0)
        if frame["flag"] is not False:
            mutated = bytearray(data)
            start, stop = frame["body_span"]
            mutated[start + frame["prefix"]] ^= 1
            reject(f"{name}-bad-stream-crc", bytes(mutated), frame,
                   {"error": "checksum", "declared": frame["crc"], "computed": crc32(mutated[start:stop])},
                   commands=0)

    _, v1, plain1 = originals["native-v1-dictionary"]
    _, v2, plain2 = originals["native-v2-dictionary"]
    for name, frame, plain, crc in [
        ("assembled-v1-absent-crc", v1, plain1, False),
        ("assembled-v2-absent-flag", v2, plain2, True),
    ]:
        data = author(frame, frame["stored"], crc=crc)
        parsed = read_frame(data, 0)
        expect_match(work, data, parsed, plain, "page")
        profiles[name] = summarize(data, parsed, plain, "assembled header, original native body")

    for key, size in [("declared-expanded-small", len(plain1) - 1), ("declared-expanded-large", len(plain1) + 1)]:
        data = author(v1, v1["stored"], expanded=size)
        reject(key, data, read_frame(data, 0), {"error": "expandedSize"}, "page")

    rows = MAPS["native_trace"](v1["stored"], reference, traced)
    bit_extent = 8 * len(v1["stored"])
    end = bit_extent - int(next(row.split()[1] for row in reversed(rows) if row.startswith("envelope_end ")))
    concatenated = author(v1, v1["stored"] * 2)
    reject("concatenated-stream", concatenated, read_frame(concatenated, 0),
           {"error": "trailingStream", "bit": end}, "page")
    truncated_stream = v1["stored"][:-1]
    check(subprocess.run([reference, "-d", "-c"], input=truncated_stream, capture_output=True).returncode != 0,
          "native library rejects the truncated payload")
    truncated = author(v1, truncated_stream)
    last_distance = next(row for row in reversed(rows) if row.startswith("distance_begin "))
    bit = bit_extent - int(last_distance.split()[1])
    index = sum(row.startswith("command ") for row in rows) - 1
    reject("truncated-stream", truncated, read_frame(truncated, 0),
           {"error": "truncatedDistance", "block": 0, "command": index, "bit": bit}, "page", bits=bit_extent)
    for key, data in [
        ("false-flag-with-compressed-sizes", author(v2, v2["stored"], flag=False)),
        ("levels-over-expanded", author(v2, v2["stored"], expanded=v2["prefix"] - 1, flag=True)),
        ("levels-over-stored", author(v2, v2["stored"][:v2["prefix"] - 1], flag=True)),
    ]:
        reject(key, data, read_frame(data, 0), {"error": "v2Lengths"}, "page")
    print(f"Matched {len(profiles)} complete expanded page bodies and {len(controls)} rejection controls")
    return {"libbrotli": PIN, "pyarrow": pa.__version__, "thrift": version("thrift"),
            "profiles": profiles, "controls": controls}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    check((pa.__version__, version("thrift")) == ("26.0.1", "0.25.0"), "producer version pins")
    with TemporaryDirectory(prefix="silmaril-parquet-brotli-page-") as directory:
        work = Path(directory)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = RAW["build_reference"](source, clean)
        traced = MAPS["setup_trace"](source or clean / "brotli", work,
                                     SCRIPTS / "brotli-dictionary-command/trace-reference.py")
        actual = collect(work, reference, traced)
        check(actual == json.loads((HERE / "fixtures.json").read_text()), "pinned Parquet/Brotli replay")
        print(f"Fixture manifest matched libbrotli {PIN}, PyArrow {pa.__version__}, Thrift {version('thrift')}")


if __name__ == "__main__":
    main()
