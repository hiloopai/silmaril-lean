"""Compare genuine PLAIN V1 ZSTD DATE pages and Lean Date32 IPC."""

import argparse
import ctypes
from ctypes.util import find_library
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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Zstd/Tests.lean"
ORDINAL = 1


def produce(pa, pq, field, nullable, checksum, groups, batch, *, version="1.0", dictionary=False):
    schema = pa.schema([pa.field("plain_int32", pa.int32(), False), pa.field(field, pa.date32(), nullable)])
    with pa.BufferOutputStream() as sink:
        with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=version,
                              compression={field: "ZSTD"}, compression_level={field: 3},
                              use_dictionary=[field] if dictionary else False,
                              write_page_checksum=checksum, write_statistics=False, store_schema=False,
                              write_batch_size=batch, data_page_size=24) as writer:
            for days in groups:
                columns = [pa.array(range(len(days)), type=pa.int32()),
                           pa.array(days, type=pa.int32()).view(pa.date32())]
                writer.write_table(pa.Table.from_arrays(columns, schema=schema))
        return sink.getvalue().to_pybytes()


def frame_extent():
    """Read exact frame lengths with independent libzstd."""
    lib = ctypes.CDLL(find_library("zstd"))
    lib.ZSTD_versionNumber.restype = ctypes.c_uint
    assert lib.ZSTD_versionNumber() == 10507
    lib.ZSTD_findFrameCompressedSize.argtypes = [ctypes.c_char_p, ctypes.c_size_t]
    lib.ZSTD_findFrameCompressedSize.restype = ctypes.c_size_t
    lib.ZSTD_isError.argtypes = [ctypes.c_size_t]
    lib.ZSTD_isError.restype = ctypes.c_uint

    def extent(data):
        size = lib.ZSTD_findFrameCompressedSize(data, len(data))
        return None if lib.ZSTD_isError(size) else size

    return extent


def inspect(pa, pq, source, field, nullable, checksum, groups, batch, prior, support, flat, extent):
    thrift = support["THRIFT"]
    type_tag = thrift["TType"]
    fingerprint = prior["fingerprint"]
    codec = pa.Codec("zstd")
    parquet = pq.ParquetFile(pa.BufferReader(source), page_checksum_verification=True)
    assert parquet.schema_arrow[ORDINAL] == pa.field(field, pa.date32(), nullable=nullable)
    assert str(parquet.schema.column(0).logical_type) == "None"
    assert [prior["read_group"](pa, parquet, field, i) for i in range(parquet.num_row_groups)] == groups
    footer_start, numeric_codecs = flat["numeric_codecs"](source)
    assert numeric_codecs == [[0, 6] for _ in groups]
    mem = thrift["TMemoryBuffer"](source[footer_start:-8])
    footer = thrift["read_struct"](thrift["TCompactProtocol"](mem))
    leaf = thrift["list_field"](footer, 2)[ORDINAL + 1]
    assert leaf[1] == (type_tag.I32, 1) and leaf[3] == (type_tag.I32, int(nullable))
    assert leaf[6] == (type_tag.I32, 6) and leaf[10] == (type_tag.STRUCT, {6: (type_tag.STRUCT, {})})

    observed, original = [], []
    for index, expected in enumerate(groups):
        column = parquet.metadata.row_group(index).column(ORDINAL)
        assert column.compression == "ZSTD" and column.dictionary_page_offset is None
        assert set(column.encodings) == {"PLAIN", "RLE"} and column.num_values == len(expected)
        begin = column.data_page_offset
        stop = begin + column.total_compressed_size
        frames = list(prior["frames"](source, column, thrift))
        assert frames[0][0] == begin and 4 <= begin < stop <= footer_start
        cursor, pages = 0, []
        for offset, header, start, stored in frames:
            assert header[1][1] == 0 and (4 in header) == checksum
            count, encoding, definitions, repetitions = [header[5][1][key][1] for key in (1, 2, 3, 4)]
            assert (count, encoding, definitions, repetitions) == (batch, 0, 3, 3)
            assert extent(stored) == len(stored) == header[3][1]
            layout = flat["first_block"](stored)
            assert layout["dictionary_field_bytes"] == 0
            crc = header[4][1] % 2**32 if checksum else None
            if checksum:
                assert crc == zlib.crc32(stored)
            expanded = codec.decompress(stored, header[2][1]).to_pybytes()
            assert len(expanded) == header[2][1]
            slots = expected[cursor:cursor + count]
            assert len(slots) == count
            cursor += count
            scalars = expanded
            if nullable:
                level_bytes = struct.unpack_from("<I", expanded)[0]
                values_start = 4 + level_bytes
                assert support["hybrid"](expanded[4:values_start], 1, count) == [int(x is not None) for x in slots]
                scalars = expanded[values_start:]
            assert [word for word, in struct.iter_unpack("<i", scalars)] == [day for day in slots if day is not None]
            slot_serialization = json.dumps(slots, separators=(",", ":")).encode()
            pages.append({"frame": offset, "stored_start": start, "rows": count, "parquet_crc": crc,
                          "stored": fingerprint(stored), "expanded": fingerprint(expanded),
                          "slots_sha256": sha256(slot_serialization).hexdigest(), **layout})
        assert cursor == len(expected)
        assert pages[-1]["stored_start"] + pages[-1]["stored"]["bytes"] == stop
        observed.append({"span": [begin, stop], "expanded_total": sum(p["expanded"]["bytes"] for p in pages),
                         "data": pages})
        original.append(frames)
    return observed, original


def replace_stored(source, frame, encoded, thrift):
    offset, header, start, stored = frame
    crc = zlib.crc32(encoded)
    signed = crc if crc < 2**31 else crc - 2**32
    replacement = thrift["encode"]({**header, 4: (thrift["TType"].I32, signed)})
    assert len(encoded) == len(stored) and len(replacement) == start - offset
    return source[:offset] + replacement + encoded + source[start + len(stored):], crc


def launch_driver(folder, files, controls, readbacks, prior, format_groups, pa, ipc):
    fingerprint = prior["fingerprint"]
    outputs, commands = {}, []

    def input_path(label, wire):
        path = folder / (label + ".parquet")
        path.write_bytes(wire)
        return json.dumps(str(path))

    for label, wire in files.items():
        field, nullable, groups, observed = readbacks[label]
        bounds = [tuple(group["span"]) for group in observed]
        offsets = [[page["frame"] for page in group["data"]] for group in observed]
        crcs = format_groups([[page["parquet_crc"] for page in group["data"]] for group in observed])
        stored_cap = max(stop - start for start, stop in bounds)
        expanded_cap = max(group["expanded_total"] for group in observed)
        output = folder / (label + ".arrows")
        source = input_path(label, wire)
        field_literal = json.dumps(field, ensure_ascii=False)
        commands.append(f"#eval (show IO Unit from do\n"
                        f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                        f"  unless plainRefuses input {ORDINAL} {field_literal} do\n"
                        f"    throw (IO.userError \"strict codec-0 DATE admission changed\")\n"
                        f"  readBack input {ORDINAL} {field_literal} {str(nullable).lower()} "
                        f"{format_groups(groups)} {bounds} {offsets} {crcs} {stored_cap} {expanded_cap} "
                        f"{json.dumps(str(output))})")
        outputs[label] = (output, pa.schema([pa.field(field, pa.date32(), nullable=nullable)]), groups)

    for label, (wire, index, cause, limits, output, prefix) in controls.items():
        source = input_path(label, wire)
        commands.append(f"#eval (show IO Unit from do\n"
                        f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                        f"  assertRejects {json.dumps(label)} input {ORDINAL} "
                        f"(.source (.groupFailure {index} {cause})) {limits} {output}\n"
                        + (f"  unless keepsPrefix input {ORDINAL} {index} {format_groups(prefix)} {cause} do\n"
                           f"    throw (IO.userError \"source prefix differed\")\n" if prefix is not None else "")
                        + ")")
    driver = folder / "Oracle.lean"
    driver.write_text(TESTS.read_text(encoding="utf-8") + "\nset_option maxRecDepth 10000\n"
                      + "\n".join(commands) + "\n", encoding="utf-8")
    subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                    "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
    result = {}
    for label, (path, schema, groups) in outputs.items():
        wire = path.read_bytes()
        ipc["observe"](pa, wire, schema, groups)
        result[label] = fingerprint(wire)
    return result


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

    def load(name):
        return runpy.run_path(str(ROOT / "scripts" / name / "check.py"))

    prior = load("parquet-date-gzip-v1-oracle")
    support = load("parquet-timestamp-snappy-dictionary-oracle")
    flat = load("parquet-flat-zstd")
    format_groups = load("parquet-date-selected-leaf-oracle")["lean_groups"]
    ipc = load("arrow-date32-writer-oracle")
    manifest = HERE / "fixtures.json"
    pins = json.loads((ROOT / "scripts/parquet-date-gzip-v1-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    seen["frame_extent_libzstd"] = "1.5.7"
    seen["producer_compression_level"] = 3
    extent = frame_extent()
    fingerprint = prior["fingerprint"]

    cases = {label: (*args, 8) for label, args in prior["CASES"].items()}
    entropy = bytes(byte % 5 for i in range(64) for byte in sha256(i.to_bytes(4, "little")).digest())
    cases["nullable_huffman"] = ("日付", True, True, [[value for value, in struct.iter_unpack("<i", entropy)]], 512)
    files = {label: produce(pa, pq, *settings) for label, settings in cases.items()}
    inspected = {label: inspect(pa, pq, files[label], *settings, prior, support, flat, extent)
                 for label, settings in cases.items()}
    assert any(p["first_block_kind"] == 0 for group in inspected["optional_crc"][0] for p in group["data"])
    assert any(p["first_block_kind"] == 2 for group in inspected["required_no_crc"][0] for p in group["data"])
    assert inspected["nullable_huffman"][0][0]["data"][0]["first_literal_kind"] == 2

    source = files["optional_crc"]
    name, _, _, groups, _ = cases["optional_crc"]
    observed, frames = inspected["optional_crc"]
    last = frames[1][-1]
    bad_crc, (offset, declared, computed) = prior["damaged_outer"](source, last)
    prior["observe_refusal"](pa, pq, bad_crc, name, groups[0], crc=True)
    _, _, _, stored = last
    bad_magic = bytes([stored[0] ^ 1]) + stored[1:]
    assert extent(bad_magic) is None
    invalid_frame, new_crc = replace_stored(source, last, bad_magic, support["THRIFT"])
    prior["observe_refusal"](pa, pq, invalid_frame, name, groups[0], crc=False)

    # Shorten the native single-segment raw block and content size by one byte.
    # The Parquet extent stays fixed, with one trailing byte after the valid frame.
    assert stored[4] == 0x20
    block = int.from_bytes(stored[6:9], "little")
    assert block & 7 == 1 and block >> 3 == stored[5] == len(stored) - 9
    trailing = stored[:5] + bytes([stored[5] - 1]) + (block - 8).to_bytes(3, "little") + stored[9:]
    assert extent(trailing) == len(stored) - 1
    assert len(pa.Codec("zstd").decompress(trailing[:-1], stored[5] - 1)) == stored[5] - 1
    trailing_file, trailing_crc = replace_stored(source, last, trailing, support["THRIFT"])

    before = groups[:1]
    writer = "{ ipc := { batches := 0 } }"
    first = observed[0]["data"][0]
    first_offset = first["frame"]

    def genuine_control(**options):
        wire = produce(pa, pq, *cases["optional_crc"], **options)
        file = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
        assert prior["read_group"](pa, file, name, 0) == groups[0]
        return wire, file.metadata.row_group(0).column(ORDINAL)

    v2, v2_column = genuine_control(version="2.0")
    dictionary, dictionary_column = genuine_control(dictionary=True)
    assert dictionary_column.dictionary_page_offset is not None
    controls = {
        "malformed_outer_crc_before_codec": (bad_crc, 1,
            f"(.checksum 2 {offset} (.mismatch {declared} {computed}))", "{}", writer, before),
        "malformed_magic_valid_crc": (invalid_frame, 1, f"(.decode 2 {offset} (.frame (.frame .badMagic)))",
                                      "{}", writer, before),
        "malformed_trailing_byte_valid_crc": (trailing_file, 1, f"(.decode 2 {offset} (.frame (.frame .trailingInput)))",
                                              "{}", writer, before),
        "low_stored_page_cap": (source, 0, f"(.checksum 0 {first_offset} .byteLimit)",
            f"{{ pages := {{ scalar := ⟨{first['stored']['bytes'] - 1}, 16777216, ⟨1048576, 16777216⟩, 1048576⟩ }} }}", "{}", None),
        "low_expanded_page_cap": (source, 0, f"(.decode 0 {first_offset} (.scalar (.payload .outputLimit)))",
            f"{{ pages := {{ scalar := ⟨16777216, {first['expanded']['bytes'] - 1}, ⟨1048576, 16777216⟩, 1048576⟩ }} }}", "{}", None),
        "low_stored_chunk_cap": (source, 0, "(.plan .storedChunkLimit)",
            f"{{ pages := {{ maxStoredChunkBytes := {observed[0]['span'][1] - observed[0]['span'][0] - 1} }} }}", "{}", None),
        "low_expanded_chunk_cap": (source, 0, "(.plan .expandedChunkLimit)",
            f"{{ pages := {{ maxExpandedChunkBytes := {observed[0]['expanded_total'] - 1} }} }}", "{}", None),
        "zero_zstd_window": (source, 0, f"(.decode 0 {first_offset} (.frame (.frame .windowLimit)))",
                              "{ compression := ⟨0, 43690⟩ }", "{}", None),
        "genuine_zstd_v2": (v2, 0, f"(.plan (.page 0 {v2_column.data_page_offset} .expectedV1))", "{}", "{}", None),
        "genuine_zstd_dictionary": (dictionary, 0, "(.plan .unsupportedOffsets)", "{}", "{}", None),
    }

    readbacks = {label: (field, nullable, days, inspected[label][0])
                 for label, (field, nullable, _, days, _) in cases.items()}
    with tempfile.TemporaryDirectory(prefix="parquet-date-zstd-v1-") as temporary:
        emitted = launch_driver(Path(temporary), files, controls, readbacks, prior, format_groups, pa, ipc)
    seen["cases"] = {
        label: {"parquet": fingerprint(files[label]), "field": field, "ordinal": ORDINAL, "nullable": nullable,
                "batch": cases[label][-1], "groups": original, "lean_ipc": emitted[label]}
        for label, (field, nullable, _, original) in readbacks.items()
    }
    seen["controls"] = {
        label: {"parquet": fingerprint(wire), "group": index, "cause": cause, "source_limits": limits,
                "output_limits": output}
        for label, (wire, index, cause, limits, output, _) in controls.items()
    }
    seen["controls"]["malformed_magic_valid_crc"]["recomputed_parquet_crc"] = new_crc
    seen["controls"]["malformed_trailing_byte_valid_crc"]["recomputed_parquet_crc"] = trailing_crc
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(seen, indent=2)
    total_pages = sum(len(group["data"]) for case in seen["cases"].values() for group in case["groups"])
    print(f"PASS {len(files)} genuine ZSTD V1 DATE IPC readbacks, {total_pages} original pages, "
          f"and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
