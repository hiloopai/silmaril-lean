"""Compare genuine GZIP PLAIN V1 DATE from PyArrow with native Date32 IPC."""

import argparse
from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import runpy
import struct
import subprocess
import sys
import tempfile
import zlib


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Gzip/Tests.lean"
ORDINAL = 1
MIN_DAY, MAX_DAY = -(2**31), 2**31 - 1
CASES = {
    "optional_crc": ("日付", True, True, [
        [MIN_DAY, None, -1, MAX_DAY, 0, 11016, -1, None] * 3,
        [0, None, -51, 4, 11016, -19, 1, 17] * 3,
    ]),
    "required_no_crc": ("époque", False, False, [
        [MIN_DAY, 0, -1, MAX_DAY, 0, 11016, -1, 1] * 3,
        [0, 4, -51, 4, 11016, -19, 1, 17] * 3,
    ]),
}


def fingerprint(data):
    return {"bytes": len(data), "sha256": sha256(data).hexdigest()}


def produce(pa, pq, name, nullable, checksum, groups, page_version="1.0", dictionary=False):
    schema = pa.schema([pa.field("plain_int32", pa.int32(), nullable=False), pa.field(name, pa.date32(), nullable)])
    with pa.BufferOutputStream() as sink:
        with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version,
                              compression="GZIP", use_dictionary=[name] if dictionary else False,
                              write_page_checksum=checksum, write_statistics=False, store_schema=False,
                              write_batch_size=8, data_page_size=24) as writer:
            for days in groups:
                columns = [pa.array([index % 4 for index in range(len(days))], type=pa.int32()),
                           pa.array(days, type=pa.int32()).view(pa.date32())]
                writer.write_table(pa.Table.from_arrays(columns, schema=schema))
        return sink.getvalue().to_pybytes()


def read_group(pa, parquet, name, index):
    return parquet.read_row_group(index, columns=[name], use_threads=False).column(0).combine_chunks().view(
        pa.int32()).to_pylist()


def frames(wire, column, thrift):
    begin = column.data_page_offset
    source = thrift["TMemoryBuffer"](wire[begin:begin + column.total_compressed_size])
    reader = thrift["TCompactProtocol"](source)
    while source.cstringio_buf.tell() < column.total_compressed_size:
        offset = begin + source.cstringio_buf.tell()
        header = thrift["read_struct"](reader)
        start = begin + source.cstringio_buf.tell()
        yield offset, header, start, source.readAll(header[3][1])
    assert source.cstringio_buf.tell() == column.total_compressed_size


def gzip_member(stored):
    member = zlib.decompressobj(wbits=31)
    body = member.decompress(stored) + member.flush()
    assert member.eof and member.unused_data == member.unconsumed_tail == b""
    crc, length = struct.unpack_from("<II", stored, len(stored) - 8)
    assert crc == zlib.crc32(body) and length == len(body)
    return body, crc


def inspect(pa, pq, wire, name, nullable, checksum, groups, support):
    thrift, hybrid = support["THRIFT"], support["hybrid"]
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow[ORDINAL] == pa.field(name, pa.date32(), nullable=nullable)
    assert str(parquet.schema.column(0).logical_type) == "None"
    assert [read_group(pa, parquet, name, index) for index in range(parquet.num_row_groups)] == groups
    footer_size = struct.unpack_from("<I", wire, len(wire) - 8)[0]
    memory = thrift["TMemoryBuffer"](wire[-8 - footer_size:-8])
    meta = thrift["read_struct"](thrift["TCompactProtocol"](memory))
    kind = thrift["TType"]
    leaf = thrift["list_field"](meta, 2)[ORDINAL + 1]
    assert leaf[1] == (kind.I32, 1) and leaf[3] == (kind.I32, int(nullable))
    assert leaf[6] == (kind.I32, 6) and leaf[10] == (kind.STRUCT, {6: (kind.STRUCT, {})})

    observations, originals = [], []
    for index, expected in enumerate(groups):
        column = parquet.metadata.row_group(index).column(ORDINAL)
        assert column.compression == "GZIP" and column.dictionary_page_offset is None
        assert set(column.encodings) == {"PLAIN", "RLE"} and column.num_values == len(expected)
        page_frames = list(frames(wire, column, thrift))
        assert len(page_frames) == 3 and page_frames[0][0] == column.data_page_offset
        cursor, pages = 0, []
        for offset, header, start, stored in page_frames:
            assert header[1][1] == 0, header
            count, encoding, definitions, repetitions = [header[5][1][field][1] for field in (1, 2, 3, 4)]
            assert (count, encoding, definitions, repetitions) == (8, 0, 3, 3)
            slots = expected[cursor:cursor + count]
            cursor += count
            assert (4 in header) == checksum
            outer_crc = header[4][1] % 2**32 if checksum else None
            if checksum:
                assert outer_crc == zlib.crc32(stored)
            expanded, member_crc = gzip_member(stored)
            assert len(expanded) == header[2][1] and len(stored) == header[3][1]
            if nullable:
                level_bytes = struct.unpack_from("<I", expanded)[0]
                begin = 4 + level_bytes
                assert hybrid(expanded[4:begin], 1, count) == [int(day is not None) for day in slots]
            else:
                level_bytes, begin = 0, 0
            words = [value for value, in struct.iter_unpack("<i", expanded[begin:])]
            assert words == [day for day in slots if day is not None]
            pages.append({"frame": offset, "stored_start": start, "parquet_crc": outer_crc,
                          "member_crc": member_crc, "stored": fingerprint(stored),
                          "expanded": fingerprint(expanded), "encoded_levels": level_bytes, "signed_slots": slots})
        assert cursor == len(expected)
        stop = column.data_page_offset + column.total_compressed_size
        assert pages[-1]["stored_start"] + pages[-1]["stored"]["bytes"] == stop
        observations.append({"span": [column.data_page_offset, stop],
                             "expanded_total": sum(page["expanded"]["bytes"] for page in pages), "data": pages})
        originals.append(page_frames)
    return observations, originals


def damaged_outer(wire, frame):
    offset, header, start, stored = frame
    edited = bytes([stored[0] ^ 1]) + stored[1:]
    declared, computed = header[4][1] % 2**32, zlib.crc32(edited)
    assert declared != computed
    return wire[:start] + edited + wire[start + len(stored):], (offset, declared, computed)


def damaged_member_crc(wire, frame, thrift, *, level_bytes=0):
    offset, header, start, stored = frame
    # Corrupt the RFC 1952 trailer and keep a correct outer page CRC.
    kind = thrift["TType"]
    for mask in (1, 2, 4, 8):
        edited = stored[:-8] + bytes([stored[-8] ^ mask]) + stored[-7:]
        crc = zlib.crc32(edited)
        signed = crc if crc < 2**31 else crc - 2**32
        replacement = thrift["encode"]({**header, 4: (kind.I32, signed)})
        if len(replacement) == start - offset:
            break
    else:
        raise AssertionError("The edited CRC changed the Compact header extent")
    try:
        gzip_member(edited[level_bytes:])
    except zlib.error:
        pass
    else:
        raise AssertionError("zlib accepted the corrupted GZIP member CRC")
    return wire[:offset] + replacement + edited + wire[start + len(stored):], crc


def observe_refusal(pa, pq, wire, name, earlier, crc):
    opened = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert read_group(pa, opened, name, 0) == earlier
    try:
        read_group(pa, opened, name, 1)
    except (pa.ArrowException, OSError) as error:
        if crc:
            assert "CRC" in str(error)
    else:
        raise AssertionError("PyArrow admitted the damaged GZIP DATE group")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path)
    parser.add_argument("--thrift-path", type=Path)
    parser.add_argument("--regenerate", action="store_true")
    args = parser.parse_args()
    for path in (args.pyarrow_path, args.thrift_path):
        if path is not None:
            sys.path.insert(0, str(path.resolve()))
    import pyarrow as pa
    import pyarrow.parquet as pq

    support = runpy.run_path(str(ROOT / "scripts/parquet-timestamp-snappy-dictionary-oracle/check.py"))
    thrift = support["THRIFT"]
    format_groups = runpy.run_path(str(ROOT / "scripts/parquet-date-selected-leaf-oracle/check.py"))["lean_groups"]
    lean_bytes = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))["lean_bytes"]
    ipc = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    pins = json.loads((ROOT / "scripts/parquet-date-snappy-fallback-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]

    files = {label: produce(pa, pq, *settings) for label, settings in CASES.items()}
    checked = {label: inspect(pa, pq, files[label], *settings, support) for label, settings in CASES.items()}
    source = files["optional_crc"]
    name, _, _, expected = CASES["optional_crc"]
    observed, original = checked["optional_crc"]
    last = original[1][-1]
    bad_outer, (offset, declared, computed) = damaged_outer(source, last)
    bad_member, new_crc = damaged_member_crc(source, last, thrift)
    observe_refusal(pa, pq, bad_outer, name, expected[0], crc=True)
    observe_refusal(pa, pq, bad_member, name, expected[0], crc=False)
    outer = f"(.page 2 {offset} (.checksum (.mismatch {declared} {computed})))"
    member = f"(.page 2 {offset} (.scalar (.payload (.malformed .gzip))))"
    zero_writer = "{ ipc := { batches := 0 } }"
    first = observed[0]["data"][0]
    first_offset = first["frame"]
    smaller_stored = first["stored"]["bytes"] - 1
    smaller_expanded = first["expanded"]["bytes"] - 1
    v2 = produce(pa, pq, *CASES["optional_crc"], page_version="2.0")
    v2_file = pq.ParquetFile(pa.BufferReader(v2), page_checksum_verification=True)
    assert read_group(pa, v2_file, name, 0) == expected[0]
    v2_offset = v2_file.metadata.row_group(0).column(ORDINAL).data_page_offset
    dictionary = produce(pa, pq, *CASES["optional_crc"], dictionary=True)
    dictionary_file = pq.ParquetFile(pa.BufferReader(dictionary), page_checksum_verification=True)
    assert dictionary_file.metadata.row_group(0).column(ORDINAL).dictionary_page_offset is not None
    assert read_group(pa, dictionary_file, name, 0) == expected[0]
    controls = {
        "malformed_outer_crc": (bad_outer, f"(.source (.groupFailure 1 {outer}))", "{}", zero_writer),
        "malformed_member_crc_valid_outer": (bad_member, f"(.source (.groupFailure 1 {member}))", "{}", zero_writer),
        "low_stored_page_cap": (source, f"(.source (.groupFailure 0 (.page 0 {first_offset} (.checksum .byteLimit))))",
                                f"{{ scalar := ⟨{smaller_stored}, 16777216, ⟨1048576, 16777216⟩, 1048576⟩ }}", "{}"),
        "low_expanded_page_cap": (source,
                                  f"(.source (.groupFailure 0 (.page 0 {first_offset} (.scalar (.payload .outputLimit)))))",
                                  f"{{ scalar := ⟨16777216, {smaller_expanded}, ⟨1048576, 16777216⟩, 1048576⟩ }}", "{}"),
        "zero_gzip_calls": (source,
                            f"(.source (.groupFailure 0 (.page 0 {first_offset} (.scalar (.payload .gzipIncomplete)))))",
                            "{ scalar := ⟨16777216, 16777216, ⟨1048576, 16777216⟩, 0⟩ }", "{}"),
        "low_stored_chunk_cap": (source, "(.source (.groupFailure 0 .storedChunkLimit))",
                                 f"{{ maxStoredChunkBytes := {observed[0]['span'][1] - observed[0]['span'][0] - 1} }}", "{}"),
        "low_expanded_chunk_cap": (source, "(.source (.groupFailure 0 .expandedChunkLimit))",
                                   f"{{ maxExpandedChunkBytes := {observed[0]['expanded_total'] - 1} }}", "{}"),
        "genuine_gzip_v2": (v2, f"(.source (.groupFailure 0 (.page 0 {v2_offset} .expectedV1)))", "{}", "{}"),
        "genuine_gzip_dictionary": (dictionary, "(.source (.groupFailure 0 .unsupportedOffsets))", "{}", "{}"),
    }

    seen["cases"], seen["controls"] = {}, {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-gzip-v1-") as temporary:
        folder = Path(temporary)
        outputs, commands = {}, []
        for label, wire in files.items():
            name, nullable, _, groups = CASES[label]
            groups_meta = checked[label][0]
            bounds = [tuple(group["span"]) for group in groups_meta]
            offsets = [[p["frame"] for p in group["data"]] for group in groups_meta]
            crcs = format_groups([[p["parquet_crc"] for p in group["data"]] for group in groups_meta])
            stored_cap = max(stop - start for start, stop in bounds)
            expanded_cap = max(group["expanded_total"] for group in groups_meta)
            path = folder / (label + ".arrows")
            label_text = json.dumps(name, ensure_ascii=False)
            commands += [f"#eval readBack {lean_bytes(wire)} {ORDINAL} {label_text} {str(nullable).lower()} "
                         f"{format_groups(groups)} {bounds} {offsets} {crcs} {stored_cap} {expanded_cap} "
                         f"{json.dumps(str(path))}",
                         f"#guard plainRefuses {lean_bytes(wire)} {ORDINAL} {label_text}"]
            seen["cases"][label] = {"parquet": fingerprint(wire), "field": name, "selected_ordinal": ORDINAL,
                                    "nullable": nullable, "stored_chunk_cap": stored_cap,
                                    "expanded_chunk_cap": expanded_cap, "groups": groups_meta}
            outputs[label] = (path, pa.schema([pa.field(name, pa.date32(), nullable=nullable)]), groups)

        for label, (wire, error, limits, output) in controls.items():
            commands.append(f"#guard rejects {lean_bytes(wire)} {ORDINAL} {error} {limits} {output}")
            seen["controls"][label] = {"parquet": fingerprint(wire), "error": error,
                                       "source_limits": limits, "output_limits": output}
        seen["controls"]["malformed_member_crc_valid_outer"]["recomputed_parquet_crc"] = new_crc
        for damaged, cause in ((bad_outer, outer), (bad_member, member)):
            commands.append(f"#guard keepsPrefix {lean_bytes(damaged)} {ORDINAL} 1 "
                            f"{format_groups(expected[:1])} {cause}")

        driver = folder / "Oracle.lean"
        driver.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
        for label, (path, schema, groups) in outputs.items():
            wire = path.read_bytes()
            ipc["observe"](pa, wire, schema, groups)
            seen["cases"][label]["lean_ipc"] = fingerprint(wire)

    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(seen, indent=2)
    print(f"PASS {len(files)} genuine GZIP DATE IPC readbacks, "
          f"{sum(len(group['data']) for case in seen['cases'].values() for group in case['groups'])} original pages, "
          f"and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
