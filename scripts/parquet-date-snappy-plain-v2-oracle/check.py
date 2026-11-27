"""Check genuine Snappy PLAIN V2 Parquet DATE and native Date32 IPC."""

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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Snappy/V2/Tests.lean"
ORDINAL = 1


def produce(pa, pq, name, nullable, checksum, groups, batch, *, page_version="2.0", dictionary=False):
    schema = pa.schema([pa.field("plain_int32", pa.int32(), nullable=False), pa.field(name, pa.date32(), nullable)])
    with pa.BufferOutputStream() as sink:
        with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version,
                              compression="SNAPPY", use_dictionary=[name] if dictionary else False,
                              write_page_checksum=checksum, write_statistics=False, store_schema=False,
                              write_batch_size=batch, data_page_size=24) as writer:
            for days in groups:
                neighbor = pa.array([index % 4 for index in range(len(days))], type=pa.int32())
                dates = pa.array(days, type=pa.int32()).view(pa.date32())
                writer.write_table(pa.Table.from_arrays([neighbor, dates], schema=schema))
        return sink.getvalue().to_pybytes()


def inspect(pa, pq, wire, name, nullable, checksum, groups, prior, support):
    thrift, hybrid = support["THRIFT"], support["hybrid"]
    kind = thrift["TType"]
    fingerprint = prior["fingerprint"]
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    memory = thrift["TMemoryBuffer"](wire[-8 - footer_size:-8])
    footer = thrift["read_struct"](thrift["TCompactProtocol"](memory))
    assert memory.cstringio_buf.tell() == footer_size
    leaf = thrift["list_field"](footer, 2)[ORDINAL + 1]
    assert leaf[1] == (kind.I32, 1) and leaf[3] == (kind.I32, int(nullable))
    assert leaf[4] == (kind.STRING, name.encode())
    assert leaf[6] == (kind.I32, 6) and leaf[10] == (kind.STRUCT, {6: (kind.STRUCT, {})})
    opened = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert opened.schema_arrow[ORDINAL] == pa.field(name, pa.date32(), nullable=nullable)
    assert opened.schema_arrow[0] == pa.field("plain_int32", pa.int32(), nullable=False)
    assert str(opened.schema.column(0).logical_type) == "None"
    assert [prior["read_group"](pa, opened, name, idx) for idx in range(opened.num_row_groups)] == groups

    codec = pa.Codec("snappy")
    observations, originals, flags = [], [], set()
    for index, expected in enumerate(groups):
        column = opened.metadata.row_group(index).column(ORDINAL)
        metadata = thrift["column_metadata"](footer, index, ORDINAL)
        assert metadata[4] == (kind.I32, 1) and thrift["list_field"](metadata, 3) == [name.encode()]
        assert column.compression == "SNAPPY" and column.dictionary_page_offset is None
        assert set(column.encodings) == {"PLAIN", "RLE"} and column.num_values == len(expected)
        frames = list(prior["frames"](wire, column, thrift))
        assert frames and frames[0][0] == column.data_page_offset
        cursor, pages = 0, []
        for offset, header, start, stored in frames:
            assert header[1][1] == 3
            info = header[8][1]
            count, nulls, rows, tag, definitions, repetitions = [info[key][1] for key in range(1, 7)]
            flag = info.get(7, (kind.BOOL, True))[1]
            slots = expected[cursor:cursor + count]
            cursor += count
            assert (rows, nulls, tag, repetitions) == (count, slots.count(None), 0, 0)
            assert len(slots) == count and (4 in header) == checksum
            crc = header[4][1] % 2**32 if checksum else None
            if checksum:
                assert crc == zlib.crc32(stored)
            assert len(stored) == header[3][1] and definitions <= min(header[2][1], header[3][1])
            levels, suffix = stored[:definitions], stored[definitions:]
            if nullable:
                assert hybrid(levels, 1, count) == [int(day is not None) for day in slots]
            else:
                assert levels == b"" and nulls == 0
            expanded = header[2][1] - definitions
            plain = codec.decompress(suffix, expanded).to_pybytes() if flag else suffix
            flags.add(flag)
            assert len(plain) == expanded == 4 * (count - nulls)
            assert [value for value, in struct.iter_unpack("<i", plain)] == [day for day in slots if day is not None]
            pages.append({"frame": offset, "stored_start": start, "parquet_crc": crc, "is_compressed": flag,
                          "flag_explicit": 7 in info, "stored": fingerprint(stored), "raw_levels": fingerprint(levels),
                          "stored_suffix": fingerprint(suffix), "plain_suffix": fingerprint(plain),
                          "expanded_bytes": header[2][1], "signed_slots": slots})
        assert cursor == len(expected)
        stop = column.data_page_offset + column.total_compressed_size
        assert pages[-1]["stored_start"] + pages[-1]["stored"]["bytes"] == stop
        observations.append({"span": [column.data_page_offset, stop],
                             "expanded_total": sum(page["expanded_bytes"] for page in pages), "data": pages})
        originals.append(frames)
    assert flags == {False, True}
    return observations, originals


def bad_snappy_preamble(wire, frame, thrift):
    offset, header, start, stored = frame
    info = header[8][1]
    definitions = info[5][1]
    expected = header[2][1] - definitions
    assert info[7][1] and 0 < expected < 127 and stored[definitions] == expected
    payload = stored[:definitions] + bytes([expected + 1]) + stored[definitions + 1:]
    crc = zlib.crc32(payload)
    signed = (crc + 2**31) % 2**32 - 2**31
    raw = thrift["encode"]({**header, 4: (thrift["TType"].I32, signed)})
    assert len(raw) == start - offset
    return wire[:offset] + raw + payload + wire[start + len(stored):], crc


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
        return runpy.run_path(str(ROOT / "scripts" / f"{name}-oracle" / "check.py"))

    prior = load("parquet-date-gzip-v1")
    support = load("parquet-timestamp-snappy-dictionary")
    v2 = load("parquet-date-gzip-v2")
    thrift = support["THRIFT"]
    format_groups = load("parquet-date-selected-leaf")["lean_groups"]
    ipc = load("arrow-date32-writer")
    fingerprint = prior["fingerprint"]
    pins = json.loads((ROOT / "scripts/parquet-date-gzip-v2-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    batch = v2["BATCH"]
    seen["producer"] = {"write_batch_size": batch, "seed": v2["SEED"], "data_page_size": 24,
                        "zlib_runtime": zlib.ZLIB_RUNTIME_VERSION}
    nullable = ("日付", True, True, v2["mixed_groups"](True))
    required = ("époque", False, False, v2["mixed_groups"](False))
    cases = {"nullable_crc": nullable, "required_no_crc": required}
    files = {label: produce(pa, pq, *shape, batch) for label, shape in cases.items()}
    checked = {label: inspect(pa, pq, files[label], *shape, prior, support) for label, shape in cases.items()}
    source = files["nullable_crc"]
    name, _, _, rows = nullable
    observed, originals = checked["nullable_crc"]
    first, late = originals[0][0], originals[1][-1]
    assert late[1][8][1][5][1] > 0
    bad_outer, (_, declared, computed) = prior["damaged_outer"](source, late)
    bad_inner, crc = bad_snappy_preamble(source, late, thrift)
    prior["observe_refusal"](pa, pq, bad_outer, name, rows[0], crc=True)
    prior["observe_refusal"](pa, pq, bad_inner, name, rows[0], crc=False)
    early_crc, (_, first_declared, first_computed) = prior["damaged_outer"](source, first)
    raw = next(frame for frame in originals[1] if not frame[1][8][1][7][1])
    edit = v2["changed_header"]

    def page_error(index, frame, cause):
        return f"(.plain (.page {index} {frame[0]} {cause}))"

    def crc_error(index, frame, declared, computed):
        return page_error(index, frame, f"(.checksum (.mismatch {declared} {computed}))")

    no_output = "{ ipc := { batches := 0 } }"
    late_cases = {
        "mutated_stored_levels_crc": (bad_outer, crc_error(2, late, declared, computed)),
        "mutated_snappy_preamble_valid_crc": (
            bad_inner, page_error(2, late, "(.scalar (.payload .outputSizeMismatch))")),
        "mutated_raw_suffix_extent": (
            edit(source, raw, thrift, page_fields={2: raw[1][2][1] + 1}),
            "(.plain (.framing (.header .invalidV2Lengths)))"),
        "mutated_non_plain_tag": (
            edit(source, late, thrift, v2_fields={4: 8}), page_error(2, late, "(.encoding 8)")),
        "mutated_null_count": (
            edit(source, late, thrift, v2_fields={2: late[1][8][1][2][1] + 1}),
            page_error(2, late, "(.scalar (.levels .presentCountMismatch))")),
    }
    controls = {label: (wire, 1, cause, "{}", no_output) for label, (wire, cause) in late_cases.items()}
    stored = f"{{ scalar := {{ ({{}} : Limits).scalar with compressedBytes := {first[1][3][1] - 1} }} }}"
    expanded = f"{{ scalar := {{ ({{}} : Limits).scalar with uncompressedBytes := {first[1][2][1] - 1} }} }}"
    first_start, first_stop = observed[0]["span"]
    controls.update({
        "stored_page_cap_before_crc": (
            early_crc, 0, page_error(0, first, "(.checksum .byteLimit)"), stored, "{}"),
        "crc_before_expanded_page_cap": (
            early_crc, 0, crc_error(0, first, first_declared, first_computed), expanded, "{}"),
        "low_expanded_page_cap": (
            source, 0, page_error(0, first, "(.scalar (.payload .outputLimit))"), expanded, "{}"),
        "low_stored_chunk_cap": (
            source, 0, "(.plain .storedChunkLimit)", f"{{ maxStoredChunkBytes := {first_stop - first_start - 1} }}", "{}"),
        "low_expanded_chunk_cap": (
            source, 0, "(.plain .expandedChunkLimit)",
            f"{{ maxExpandedChunkBytes := {observed[0]['expanded_total'] - 1} }}", "{}"),
        "low_group_row_cap": (source, 0, "(.plain .rowLimit)", f"{{ maxRows := {len(rows[0]) - 1} }}", "{}"),
    })
    version1 = produce(pa, pq, *nullable, batch, page_version="1.0")
    dictionary = produce(pa, pq, *nullable, batch, dictionary=True)
    v1_offset = pq.ParquetFile(pa.BufferReader(version1)).metadata.row_group(0).column(ORDINAL).data_page_offset
    assert pq.ParquetFile(pa.BufferReader(dictionary)).metadata.row_group(0).column(ORDINAL).has_dictionary_page
    controls["genuine_snappy_v1"] = (version1, 0, f"(.expectedV2 0 {v1_offset})", "{}", "{}")
    controls["genuine_snappy_dictionary"] = (dictionary, 0, "(.plain .unsupportedOffsets)", "{}", "{}")
    controls["genuine_gzip_v2"] = (v2["produce_mixed"](pa, pq, *nullable), 0, "(.plain (.codec 2))", "{}", "{}")

    seen["cases"], seen["controls"] = {}, {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-snappy-plain-v2-") as temporary:
        folder = Path(temporary)
        commands, outputs = [], {}

        def save(label, wire):
            path = folder / (label + ".parquet")
            path.write_bytes(wire)
            return json.dumps(str(path))

        for label, wire in files.items():
            field, nullable_field, _, groups = cases[label]
            descriptions = checked[label][0]
            bounds = [tuple(group["span"]) for group in descriptions]
            offsets = [[page["frame"] for page in group["data"]] for group in descriptions]
            crcs = format_groups([[page["parquet_crc"] for page in group["data"]] for group in descriptions])
            flags = json.dumps([[page["is_compressed"] for page in group["data"]] for group in descriptions])
            path = folder / (label + ".arrows")
            stored_cap = max(stop - start for start, stop in bounds)
            expanded_cap = max(group["expanded_total"] for group in descriptions)
            row_cap = max(map(len, groups))
            field_text = json.dumps(field, ensure_ascii=False)
            commands.append(f"#eval (show IO Unit from do\n"
                            f"  let input := Bytes.mk (← IO.FS.readBinFile {save(label, wire)})\n"
                            f"  readBack input {ORDINAL} {field_text} {str(nullable_field).lower()} "
                            f"{format_groups(groups)} {bounds} {offsets} {crcs} {stored_cap} {expanded_cap} {row_cap} "
                            f"{flags} {json.dumps(str(path))})")
            seen["cases"][label] = {"parquet": fingerprint(wire), "field": field, "selected_ordinal": ORDINAL,
                                    "nullable": nullable_field, "stored_chunk_cap": stored_cap,
                                    "expanded_chunk_cap": expanded_cap, "group_row_cap": row_cap, "groups": descriptions}
            outputs[label] = (path, pa.schema([pa.field(field, pa.date32(), nullable=nullable_field)]), groups)

        for label, (wire, index, cause, limits, output) in controls.items():
            error = f"(.source (.groupFailure {index} {cause}))"
            cmd = (f"#eval (show IO Unit from do\n"
                   f"  let input := Bytes.mk (← IO.FS.readBinFile {save(label, wire)})\n"
                   f"  unless rejects input {ORDINAL} {error} {limits} {output} do\n"
                   f"    throw (IO.userError \"{label}: expected {error}\")")
            if label in late_cases:
                cmd += (f"\n  unless keepsPrefix input {ORDINAL} {index} {format_groups(rows[:index])} {cause} do\n"
                        f"    throw (IO.userError \"{label}: completed prefix differed\")")
            commands.append(cmd + ")")
            seen["controls"][label] = {"parquet": fingerprint(wire), "error": error,
                                       "source_limits": limits, "output_limits": output}
        seen["controls"]["mutated_snappy_preamble_valid_crc"]["recomputed_crc"] = crc
        driver = folder / "Oracle.lean"
        driver.write_text(TESTS.read_text() + "\n" + "\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
        for label, (path, schema, groups) in outputs.items():
            emitted = path.read_bytes()
            assert emitted.endswith(bytes.fromhex("ffffffff00000000"))
            ipc["observe"](pa, emitted, schema, groups)
            seen["cases"][label]["lean_ipc"] = fingerprint(emitted)

    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8"))
    pages = sum(len(group["data"]) for case in seen["cases"].values() for group in case["groups"])
    print(f"PASS {len(files)} genuine Snappy PLAIN V2 DATE files, {pages} original pages with both flags, "
          f"and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
