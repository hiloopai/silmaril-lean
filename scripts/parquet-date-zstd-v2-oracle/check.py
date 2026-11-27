"""Compare genuine PLAIN V2 ZSTD DATE pages and Lean-emitted Date32 IPC."""

import argparse
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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Zstd/V2/Tests.lean"
ORDINAL = 1


def inspect(pa, pq, wire, field, nullable, checksum, groups, batch, prior, support, flat, extent):
    thrift, hybrid = support["THRIFT"], support["hybrid"]
    fingerprint = prior["fingerprint"]
    codec = pa.Codec("zstd")
    file = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert file.schema_arrow[ORDINAL] == pa.field(field, pa.date32(), nullable)
    assert str(file.schema.column(0).logical_type) == "None"
    assert [prior["read_group"](pa, file, field, index) for index in range(file.num_row_groups)] == groups
    footer_start, numeric_codecs = flat["numeric_codecs"](wire)
    assert numeric_codecs == [[0, 6] for _ in groups]
    reader = thrift["TCompactProtocol"](thrift["TMemoryBuffer"](wire[footer_start:-8]))
    metadata = thrift["read_struct"](reader)
    leaf = thrift["list_field"](metadata, 2)[ORDINAL + 1]
    kind = thrift["TType"]
    assert leaf[1] == (kind.I32, 1) and leaf[3] == (kind.I32, int(nullable))
    assert leaf[6] == (kind.I32, 6) and leaf[10] == (kind.STRUCT, {6: (kind.STRUCT, {})})

    original, observations = [], []
    for index, expected in enumerate(groups):
        column = file.metadata.row_group(index).column(ORDINAL)
        assert column.compression == "ZSTD" and column.dictionary_page_offset is None
        assert set(column.encodings) == {"PLAIN", "RLE"} and column.num_values == len(expected)
        begin = column.data_page_offset
        stop = begin + column.total_compressed_size
        frames = list(prior["frames"](wire, column, thrift))
        assert frames[0][0] == begin and 4 <= begin < stop <= footer_start
        cursor, pages = 0, []
        for offset, header, start, stored in frames:
            assert header[1][1] == 3 and (4 in header) == checksum
            info = header[8][1]
            count, nulls, rows, encoding, definitions, repetitions, flag = [info[k][1] for k in range(1, 8)]
            slots = expected[cursor:cursor + count]
            cursor += count
            assert (count, rows, nulls, encoding, repetitions) == (batch, batch, slots.count(None), 0, 0)
            assert len(slots) == count and definitions <= min(header[2][1], header[3][1])
            crc = header[4][1] % 2**32 if checksum else None
            if checksum:
                assert zlib.crc32(stored) == crc
            levels, suffix = stored[:definitions], stored[definitions:]
            assert len(stored) == header[3][1] and len(levels) == definitions
            assert len(suffix) == header[3][1] - definitions
            if nullable:
                assert hybrid(levels, 1, count) == [int(day is not None) for day in slots]
            else:
                assert levels == b"" and nulls == 0
            expected_bytes = header[2][1] - definitions
            if flag:
                assert extent(suffix) == len(suffix)
                frame_shape = flat["first_block"](suffix)
                assert frame_shape["dictionary_field_bytes"] == 0
                scalars = codec.decompress(suffix, expected_bytes).to_pybytes()
            else:
                assert header[3][1] == header[2][1]
                frame_shape = None
                scalars = suffix
            assert len(scalars) == expected_bytes
            assert [word for word, in struct.iter_unpack("<i", scalars)] == [day for day in slots if day is not None]
            pages.append({"frame": offset, "stored_start": start, "parquet_crc": crc, "is_compressed": flag,
                          "num_values": count, "num_rows": rows, "num_nulls": nulls, "stored": fingerprint(stored),
                          "declared_expanded_bytes": header[2][1], "raw_levels": fingerprint(levels),
                          "stored_suffix": fingerprint(suffix), "plain_suffix": fingerprint(scalars),
                          "zstd_frame": frame_shape, "signed_slots": slots})
        assert cursor == len(expected)
        assert pages[-1]["stored_start"] + pages[-1]["stored"]["bytes"] == stop
        observations.append({"span": [begin, stop],
                             "expanded_total": sum(p["declared_expanded_bytes"] for p in pages), "data": pages})
        original.append(frames)
    return observations, original


def change_flag(wire, frame, flag, thrift):
    offset, header, start, _ = frame
    kind, fields = header[8]
    assert fields[7] == (thrift["TType"].BOOL, not flag)
    altered = {**header, 8: (kind, {**fields, 7: (thrift["TType"].BOOL, flag)})}
    edited = thrift["encode"](altered)
    assert len(edited) == start - offset
    return wire[:offset] + edited + wire[start:]


def launch_driver(folder, files, readbacks, controls, format_groups, pa, ipc):
    outputs, commands = {}, []

    def input_path(label, wire):
        path = folder / (label + ".parquet")
        path.write_bytes(wire)
        return json.dumps(str(path))

    for label, wire in files.items():
        field, nullable, groups, observed, window = readbacks[label]
        bounds = [tuple(group["span"]) for group in observed]
        offsets = [[p["frame"] for p in group["data"]] for group in observed]
        crcs = format_groups([[p["parquet_crc"] for p in group["data"]] for group in observed])
        flags = json.dumps([[p["is_compressed"] for p in group["data"]] for group in observed])
        levels = [[p["raw_levels"]["bytes"] for p in group["data"]] for group in observed]
        stored_cap = max(stop - start for start, stop in bounds)
        expanded_cap = max(group["expanded_total"] for group in observed)
        out = folder / (label + ".arrows")
        source = input_path(label, wire)
        field_literal = json.dumps(field, ensure_ascii=False)
        commands.append(f"#eval (show IO Unit from do\n"
                        f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                        f"  unless plainRefuses input {ORDINAL} {field_literal} && "
                        f"v1Refuses input {ORDINAL} {offsets[0][0]} && gzipRefuses input {ORDINAL} do\n"
                        f"    throw (IO.userError \"existing DATE admission changed\")\n"
                        f"  readBack input {ORDINAL} {field_literal} {str(nullable).lower()} "
                        f"{format_groups(groups)} {bounds} {offsets} {crcs} {flags} {levels} "
                        f"{stored_cap} {expanded_cap} {window} {json.dumps(str(out))})")
        outputs[label] = (out, pa.schema([pa.field(field, pa.date32(), nullable)]), groups)

    for label, (wire, index, reason, limits, output, prefix) in controls.items():
        source = input_path(label, wire)
        commands.append(f"#eval (show IO Unit from do\n"
                        f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                        f"  assertRejects {json.dumps(label)} input {ORDINAL} "
                        f"(.source (.groupFailure {index} {reason})) {limits} {output}\n"
                        + (f"  unless keepsPrefix input {ORDINAL} {index} {format_groups(prefix)} {reason} do\n"
                           f"    throw (IO.userError \"source prefix differed\")\n" if prefix is not None else "")
                        + ")")

    driver = folder / "Oracle.lean"
    driver.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n", encoding="utf-8")
    subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                    "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
    emitted = {}
    for label, (path, schema, groups) in outputs.items():
        wire = path.read_bytes()
        ipc["observe"](pa, wire, schema, groups)
        emitted[label] = wire
    return emitted


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
    gzip = load("parquet-date-gzip-v2-oracle")
    zstd = load("parquet-date-zstd-v1-oracle")
    support = load("parquet-timestamp-snappy-dictionary-oracle")
    thrift = support["THRIFT"]
    flat = load("parquet-flat-zstd")
    format_groups = load("parquet-date-selected-leaf-oracle")["lean_groups"]
    ipc = load("arrow-date32-writer-oracle")
    pins = json.loads((ROOT / "scripts/parquet-date-zstd-v1-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain", "frame_extent_libzstd",
                                      "producer_compression_level")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    extent = zstd["frame_extent"]()
    fingerprint = prior["fingerprint"]
    batch = gzip["BATCH"]
    seen["producer"] = {"write_batch_size": batch, "mixed_seed": gzip["SEED"], "data_page_size": 24}

    optional = gzip["mixed_groups"](True)
    cases = {
        "optional_mixed_crc": ("日付", True, True, optional, 8388608),
        "required_mixed_no_crc": ("époque", False, False, gzip["mixed_groups"](False), 8388608),
        "optional_raw_only_crc": ("jour", True, True, [optional[0][batch:2 * batch] + [None] * batch,
                                                       optional[1][:batch]], 0),
    }
    files = {label: zstd["produce"](pa, pq, *settings[:4], batch, version="2.0")
             for label, settings in cases.items()}
    inspected = {label: inspect(pa, pq, files[label], *settings[:4], batch, prior, support, flat, extent)
                 for label, settings in cases.items()}
    for label, (groups, _) in inspected.items():
        flags = {p["is_compressed"] for group in groups for p in group["data"]}
        assert flags == ({False} if label == "optional_raw_only_crc" else {False, True})
    empty_values = inspected["optional_raw_only_crc"][0][0]["data"][1]
    assert empty_values["num_nulls"] == batch and empty_values["stored_suffix"]["bytes"] == 0

    source = files["optional_mixed_crc"]
    name, _, _, expected, _ = cases["optional_mixed_crc"]
    _, frames = inspected["optional_mixed_crc"]
    last = frames[1][-1]
    last_offset, last_header, _, stored = last
    definition_bytes = last_header[8][1][5][1]
    assert last_header[8][1][7][1] is True and definition_bytes > 0
    bad_crc, (_, declared, computed) = prior["damaged_outer"](source, last)
    altered = stored[:definition_bytes] + bytes([stored[definition_bytes] ^ 1]) + stored[definition_bytes + 1:]
    assert altered[:definition_bytes] == stored[:definition_bytes] and extent(altered[definition_bytes:]) is None
    bad_magic, recomputed = zstd["replace_stored"](source, last, altered, thrift)
    prior["observe_refusal"](pa, pq, bad_crc, name, expected[0], crc=True)
    prior["observe_refusal"](pa, pq, bad_magic, name, expected[0], crc=False)

    raw = frames[1][0]
    assert extent(raw[3][raw[1][8][1][5][1]:]) is None
    wrong_true = change_flag(source, raw, True, thrift)
    wrong_false = change_flag(source, last, False, thrift)
    wrong_levels = gzip["changed_header"](source, last, thrift, v2_fields={5: len(stored) + 1})
    wrong_nulls = gzip["changed_header"](source, last, thrift, v2_fields={2: last_header[8][1][2][1] + 1})
    first = frames[0][0]
    first_offset, first_header, _, _ = first
    early_crc, (_, early_declared, early_computed) = prior["damaged_outer"](source, first)
    small_stored = first_header[3][1] - 1
    small_expanded = first_header[2][1] - 1
    stored_limit = f"{{ pages := {{ scalar := ⟨{small_stored}, 16777216, ⟨1048576, 16777216⟩, 1048576⟩ }} }}"
    expanded_limit = f"{{ pages := {{ scalar := ⟨16777216, {small_expanded}, ⟨1048576, 16777216⟩, 1048576⟩ }} }}"
    writer_limit = "{ ipc := { batches := 0 } }"

    def genuine_control(**options):
        wire = zstd["produce"](pa, pq, *cases["optional_mixed_crc"][:4], batch, **options)
        opened = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
        assert prior["read_group"](pa, opened, name, 0) == expected[0]
        return wire, opened.metadata.row_group(0).column(ORDINAL)

    v1, v1_column = genuine_control(version="1.0")
    dictionaries, dict_column = genuine_control(version="2.0", dictionary=True)
    assert dict_column.dictionary_page_offset is not None
    framing = "(.zstd (.plan (.framing (.header .invalidV2Lengths))))"
    magic = "(.frame (.frame .badMagic))"
    late = {
        "malformed_stored_level_crc": (bad_crc, f"(.zstd (.checksum 2 {last_offset} (.mismatch {declared} {computed})))"),
        "malformed_zstd_magic_valid_crc": (bad_magic, f"(.zstd (.decode 2 {last_offset} {magic}))"),
        "malformed_raw_suffix_flag_true": (wrong_true, f"(.zstd (.decode 0 {raw[0]} {magic}))"),
        "malformed_zstd_suffix_flag_false": (wrong_false, framing),
        "malformed_raw_level_extent": (wrong_levels, framing),
        "malformed_null_count": (wrong_nulls,
            f"(.zstd (.decode 2 {last_offset} (.scalar (.levels .presentCountMismatch))))"),
    }
    controls = {label: (wire, 1, cause, "{}", writer_limit, expected[:1])
                for label, (wire, cause) in late.items()}
    controls.update({
        "stored_cap_before_crc": (early_crc, 0, f"(.zstd (.checksum 0 {first_offset} .byteLimit))",
                                  stored_limit, "{}", None),
        "crc_before_expansion_cap": (early_crc, 0,
            f"(.zstd (.checksum 0 {first_offset} (.mismatch {early_declared} {early_computed})))",
            expanded_limit, "{}", None),
        "low_expanded_page_cap": (source, 0, f"(.zstd (.decode 0 {first_offset} (.scalar (.payload .outputLimit))))",
                                  expanded_limit, "{}", None),
        "zero_zstd_window_compressed": (source, 0, f"(.zstd (.decode 0 {first_offset} (.frame (.frame .windowLimit))))",
                                        "{ compression := ⟨0, 43690⟩ }", "{}", None),
        "genuine_zstd_v1": (v1, 0, f"(.expectedV2 0 {v1_column.data_page_offset})", "{}", "{}", None),
        "genuine_zstd_dictionary": (dictionaries, 0, "(.zstd (.plan .unsupportedOffsets))", "{}", "{}", None),
    })

    readbacks = {label: (field, nullable, groups, inspected[label][0], window)
                 for label, (field, nullable, _, groups, window) in cases.items()}
    with tempfile.TemporaryDirectory(prefix="parquet-date-zstd-v2-") as temporary:
        emitted = launch_driver(Path(temporary), files, readbacks, controls, format_groups, pa, ipc)
    seen["cases"] = {
        label: {"parquet": fingerprint(files[label]), "field": field, "ordinal": ORDINAL, "nullable": nullable,
                "window_cap": window, "groups": observed, "lean_ipc": fingerprint(emitted[label])}
        for label, (field, nullable, _, observed, window) in readbacks.items()
    }
    seen["controls"] = {
        label: {"parquet": fingerprint(wire), "group": index, "cause": cause, "source_limits": limits,
                "output_limits": output}
        for label, (wire, index, cause, limits, output, _) in controls.items()
    }
    seen["controls"]["malformed_zstd_magic_valid_crc"]["recomputed_parquet_crc"] = recomputed
    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(seen, indent=2)
    total_pages = sum(len(group["data"]) for case in seen["cases"].values() for group in case["groups"])
    print(f"PASS {len(files)} genuine ZSTD V2 DATE IPC readbacks, {total_pages} original pages with both flags, "
          f"and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
