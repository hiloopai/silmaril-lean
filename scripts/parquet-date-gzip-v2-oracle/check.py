"""Inspect genuine GZIP-column PLAIN V2 DATE pages and native IPC readback."""

import argparse
from importlib.metadata import version
import json
import os
from pathlib import Path
import random
import runpy
import struct
import subprocess
import sys
import tempfile
import zlib


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Gzip/V2/Tests.lean"
ORDINAL = 1
BATCH = 16
SEED = 1952
MIN_DAY, MAX_DAY = -(2**31), 2**31 - 1


def mixed_groups(nullable):
    values = random.Random(SEED)

    def noise():
        return [None if nullable and i % 7 == 0 else values.getrandbits(32) + MIN_DAY for i in range(BATCH)]

    same = [MIN_DAY, None if nullable else 0, MAX_DAY, 0, -1, 11016, None if nullable else 1, -1] * (BATCH // 8)
    return [same + noise() + same, noise() + same + same]


def produce_mixed(pa, pq, name, nullable, checksum, groups):
    schema = pa.schema([pa.field("plain_int32", pa.int32(), nullable=False), pa.field(name, pa.date32(), nullable)])
    with pa.BufferOutputStream() as sink:
        with pq.ParquetWriter(sink, schema, version="2.6", data_page_version="2.0",
                              compression="GZIP", use_dictionary=False, write_page_checksum=checksum,
                              write_statistics=False, store_schema=False, write_batch_size=BATCH,
                              data_page_size=24) as writer:
            for days in groups:
                columns = [pa.array([index % 4 for index in range(len(days))], type=pa.int32()),
                           pa.array(days, type=pa.int32()).view(pa.date32())]
                writer.write_table(pa.Table.from_arrays(columns, schema=schema))
        return sink.getvalue().to_pybytes()


def inspect(pa, pq, wire, name, nullable, checksum, groups, expected_flags, prior, support):
    thrift, hybrid = support["THRIFT"], support["hybrid"]
    fingerprint = prior["fingerprint"]
    opened = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert opened.schema_arrow[ORDINAL] == pa.field(name, pa.date32(), nullable=nullable)
    assert str(opened.schema.column(0).logical_type) == "None"
    assert [prior["read_group"](pa, opened, name, index) for index in range(opened.num_row_groups)] == groups
    footer_size = struct.unpack_from("<I", wire, len(wire) - 8)[0]
    memory = thrift["TMemoryBuffer"](wire[-8 - footer_size:-8])
    metadata = thrift["read_struct"](thrift["TCompactProtocol"](memory))
    kind = thrift["TType"]
    leaf = thrift["list_field"](metadata, 2)[ORDINAL + 1]
    assert leaf[1] == (kind.I32, 1) and leaf[3] == (kind.I32, int(nullable))
    assert leaf[6] == (kind.I32, 6) and leaf[10] == (kind.STRUCT, {6: (kind.STRUCT, {})})

    observations, originals, flags = [], [], set()
    for index, expected in enumerate(groups):
        column = opened.metadata.row_group(index).column(ORDINAL)
        assert column.compression == "GZIP" and column.dictionary_page_offset is None
        assert set(column.encodings) == {"PLAIN", "RLE"} and column.num_values == len(expected)
        page_frames = list(prior["frames"](wire, column, thrift))
        assert len(page_frames) == 3 and page_frames[0][0] == column.data_page_offset
        cursor, pages = 0, []
        for offset, header, start, stored in page_frames:
            assert header[1][1] == 3
            info = header[8][1]
            count, nulls, rows, tag, definitions, repetitions, flag = [info[key][1] for key in range(1, 8)]
            slots = expected[cursor:cursor + count]
            cursor += count
            assert (rows, nulls, tag, repetitions) == (count, slots.count(None), 0, 0)
            assert (4 in header) == checksum
            crc = header[4][1] % 2**32 if checksum else None
            if checksum:
                assert crc == zlib.crc32(stored)
            assert definitions <= min(header[2][1], header[3][1])
            levels, suffix = stored[:definitions], stored[definitions:]
            if nullable:
                assert hybrid(levels, 1, count) == [int(day is not None) for day in slots]
            else:
                assert levels == b"" and nulls == 0
            if flag:
                scalars, inner_crc = prior["gzip_member"](suffix)
            else:
                scalars, inner_crc = suffix, None
            flags.add(flag)
            assert len(scalars) == header[2][1] - definitions
            assert len(suffix) == header[3][1] - definitions
            words = [value for value, in struct.iter_unpack("<i", scalars)]
            assert words == [day for day in slots if day is not None]
            pages.append({"frame": offset, "stored_start": start, "parquet_crc": crc, "inner_gzip_crc": inner_crc,
                          "is_compressed": flag, "stored": fingerprint(stored),
                          "raw_levels": fingerprint(levels), "stored_suffix": fingerprint(suffix),
                          "plain_suffix": fingerprint(scalars), "declared_expanded_bytes": header[2][1],
                          "num_values": count, "num_rows": rows, "num_nulls": nulls, "signed_slots": slots})
        assert cursor == len(expected)
        stop = column.data_page_offset + column.total_compressed_size
        assert pages[-1]["stored_start"] + pages[-1]["stored"]["bytes"] == stop
        observations.append({"span": [column.data_page_offset, stop],
                             "expanded_total": sum(page["declared_expanded_bytes"] for page in pages),
                             "data": pages})
        originals.append(page_frames)
    assert flags == expected_flags
    return observations, originals


def malformed_inner(wire, frame, prior, thrift):
    offset, header, start, stored = frame
    data = header[8][1]
    assert data[7][1] is True
    levels = data[5][1]
    kind = thrift["TType"]
    for mask in (1, 2, 4, 8):
        changed = stored[:-8] + bytes([stored[-8] ^ mask]) + stored[-7:]
        crc = zlib.crc32(changed)
        signed = crc if crc < 2**31 else crc - 2**32
        replacement = thrift["encode"]({**header, 4: (kind.I32, signed)})
        if len(replacement) == start - offset:
            break
    else:
        raise AssertionError("The edited CRC changed the Compact header width")
    assert changed[:levels] == stored[:levels]
    try:
        prior["gzip_member"](changed[levels:])
    except zlib.error:
        pass
    else:
        raise AssertionError("zlib admitted the corrupted V2 member CRC")
    return wire[:offset] + replacement + changed + wire[start + len(stored):], crc


def changed_header(wire, frame, thrift, *, page_fields=None, v2_fields=None):
    offset, header, start, _ = frame
    kind = thrift["TType"]
    struct_kind, v2 = header[8]
    edited = {**header, **{k: (kind.I32, v) for k, v in (page_fields or {}).items()}}
    edited[8] = (struct_kind, {**v2, **{k: (kind.I32, v) for k, v in (v2_fields or {}).items()}})
    raw = thrift["encode"](edited)
    assert len(raw) == start - offset
    return wire[:offset] + raw + wire[start:]


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

    prior = runpy.run_path(str(ROOT / "scripts/parquet-date-gzip-v1-oracle/check.py"))
    support = runpy.run_path(str(ROOT / "scripts/parquet-timestamp-snappy-dictionary-oracle/check.py"))
    thrift = support["THRIFT"]
    fingerprint = prior["fingerprint"]
    format_groups = runpy.run_path(str(ROOT / "scripts/parquet-date-selected-leaf-oracle/check.py"))["lean_groups"]
    lean_bytes = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))["lean_bytes"]
    ipc = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    pins = json.loads((ROOT / "scripts/parquet-date-gzip-v1-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    seen["producer"] = {"mixed_write_batch_size": BATCH, "mixed_seed": SEED, "data_page_size": 24}

    cases = {
        "optional_mixed_crc": ("日付", True, True, mixed_groups(True)),
        "required_mixed_no_crc": ("époque", False, False, mixed_groups(False)),
        "optional_all_raw_crc": prior["CASES"]["optional_crc"],
    }
    files = {label: produce_mixed(pa, pq, *shape) for label, shape in cases.items() if "mixed" in label}
    files["optional_all_raw_crc"] = prior["produce"](pa, pq, *cases["optional_all_raw_crc"], page_version="2.0")
    assert fingerprint(files["optional_all_raw_crc"]) == pins["controls"]["genuine_gzip_v2"]["parquet"]
    checked = {label: inspect(pa, pq, files[label], *shape, {True, False} if "mixed" in label else {False},
                              prior, support) for label, shape in cases.items()}

    label = "optional_mixed_crc"
    source = files[label]
    name, _, _, expected = cases[label]
    observed, originals = checked[label]
    last = originals[1][-1]
    last_offset = last[0]
    assert last[1][8][1][5][1] > 0
    bad_outer, (_, declared, computed) = prior["damaged_outer"](source, last)
    bad_inner, recomputed = malformed_inner(source, last, prior, thrift)
    prior["observe_refusal"](pa, pq, bad_outer, name, expected[0], crc=True)
    prior["observe_refusal"](pa, pq, bad_inner, name, expected[0], crc=False)

    raw = originals[1][0]
    assert raw[1][8][1][7][1] is False
    wrong_levels = changed_header(source, last, thrift, v2_fields={5: len(last[3]) + 1})
    wrong_suffix = changed_header(source, raw, thrift, page_fields={2: raw[1][2][1] + 1})
    wrong_expanded = changed_header(source, last, thrift, page_fields={2: last[1][2][1] - 1})
    wrong_rows = changed_header(source, last, thrift, v2_fields={3: BATCH + 1})
    wrong_values = changed_header(source, last, thrift, v2_fields={1: BATCH + 1})
    wrong_nulls = changed_header(source, last, thrift, v2_fields={2: last[1][8][1][2][1] + 1})
    first = originals[0][0]
    early_crc, (first_offset, first_declared, first_computed) = prior["damaged_outer"](source, first)
    cap_stored = first[1][3][1] - 1
    cap_expanded = first[1][2][1] - 1
    stored = f"{{ scalar := ⟨{cap_stored}, 16777216, ⟨1048576, 16777216⟩, 1048576⟩ }}"
    expanded = f"{{ scalar := ⟨16777216, {cap_expanded}, ⟨1048576, 16777216⟩, 1048576⟩ }}"
    no_calls = "{ scalar := ⟨16777216, 16777216, ⟨1048576, 16777216⟩, 0⟩ }"
    no_output = "{ ipc := { batches := 0 } }"

    def page_error(page, offset, cause):
        return f"(.gzip (.page {page} {offset} {cause}))"

    def group_error(group, cause):
        return f"(.source (.groupFailure {group} {cause}))"

    outer = page_error(2, last_offset, f"(.checksum (.mismatch {declared} {computed}))")
    inner = page_error(2, last_offset, "(.scalar (.payload (.malformed .gzip)))")
    lengths = "(.gzip (.framing (.header .invalidV2Lengths)))"
    compressed_extent = page_error(2, last_offset, "(.scalar (.payload .outputSizeMismatch))")
    late = {
        "malformed_stored_level_crc": (bad_outer, outer),
        "malformed_member_crc_valid_outer": (bad_inner, inner),
        "malformed_level_extent": (wrong_levels, lengths),
        "malformed_raw_suffix_extent": (wrong_suffix, lengths),
        "malformed_expanded_gzip_extent": (wrong_expanded, compressed_extent),
        "malformed_page_row_count": (wrong_rows, "(.gzip (.framing (.header .invalidV2Counts)))"),
        "malformed_slot_total": (wrong_values, "(.gzip (.rowCount 48 49))"),
        "malformed_null_count": (wrong_nulls, page_error(2, last_offset, "(.scalar (.levels .presentCountMismatch))")),
    }
    controls = {key: (wire, group_error(1, cause), "{}", no_output) for key, (wire, cause) in late.items()}
    controls.update({
        "stored_cap_before_crc": (early_crc, group_error(0, page_error(0, first_offset, "(.checksum .byteLimit)")),
                                  stored, "{}"),
        "crc_before_expansion_cap": (
            early_crc, group_error(0, page_error(0, first_offset,
                                   f"(.checksum (.mismatch {first_declared} {first_computed}))")), expanded, "{}"),
        "low_expanded_page_cap": (source, group_error(0, page_error(0, first_offset, "(.scalar (.payload .outputLimit))")),
                                  expanded, "{}"),
        "zero_gzip_calls_compressed": (
            source, group_error(0, page_error(0, first_offset, "(.scalar (.payload .gzipIncomplete))")), no_calls, "{}"),
    })
    v1 = prior["produce"](pa, pq, *prior["CASES"]["optional_crc"])
    assert fingerprint(v1) == pins["cases"]["optional_crc"]["parquet"]
    v1_file = pq.ParquetFile(pa.BufferReader(v1))
    v1_offset = v1_file.metadata.row_group(0).column(ORDINAL).data_page_offset
    controls["genuine_gzip_v1"] = (v1, group_error(0, f"(.expectedV2 0 {v1_offset})"), "{}", "{}")
    dictionary = prior["produce"](pa, pq, *prior["CASES"]["optional_crc"], page_version="2.0", dictionary=True)
    assert pq.ParquetFile(pa.BufferReader(dictionary)).metadata.row_group(0).column(ORDINAL).dictionary_page_offset
    controls["genuine_gzip_v2_dictionary"] = (dictionary, group_error(0, "(.gzip .unsupportedOffsets)"), "{}", "{}")

    seen["cases"], seen["controls"] = {}, {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-gzip-v2-") as temporary:
        folder = Path(temporary)
        outputs, commands = {}, []
        for label, wire in files.items():
            name, nullable, _, groups = cases[label]
            groups_meta = checked[label][0]
            bounds = [tuple(group["span"]) for group in groups_meta]
            offsets = [[p["frame"] for p in group["data"]] for group in groups_meta]
            crcs = format_groups([[p["parquet_crc"] for p in group["data"]] for group in groups_meta])
            flags = json.dumps([[p["is_compressed"] for p in group["data"]] for group in groups_meta])
            stored_cap = max(stop - start for start, stop in bounds)
            expanded_cap = max(group["expanded_total"] for group in groups_meta)
            calls = 0 if label == "optional_all_raw_crc" else 1048576
            path = folder / (label + ".arrows")
            label_text = json.dumps(name, ensure_ascii=False)
            commands += [f"#eval readBack {lean_bytes(wire)} {ORDINAL} {label_text} {str(nullable).lower()} "
                         f"{format_groups(groups)} {bounds} {offsets} {crcs} {stored_cap} {expanded_cap} "
                         f"{calls} {flags} {json.dumps(str(path))}",
                         f"#guard olderProfilesRefuse {lean_bytes(wire)} {ORDINAL} {label_text}"]
            seen["cases"][label] = {"parquet": fingerprint(wire), "field": name, "selected_ordinal": ORDINAL,
                                    "nullable": nullable, "stored_chunk_cap": stored_cap,
                                    "expanded_chunk_cap": expanded_cap, "gzip_calls": calls, "groups": groups_meta}
            outputs[label] = (path, pa.schema([pa.field(name, pa.date32(), nullable=nullable)]), groups)

        for label, (wire, error, limits, output) in controls.items():
            commands.append(f"#guard rejects {lean_bytes(wire)} {ORDINAL} {error} {limits} {output}")
            seen["controls"][label] = {"parquet": fingerprint(wire), "error": error,
                                       "source_limits": limits, "output_limits": output}
        seen["controls"]["malformed_member_crc_valid_outer"]["recomputed_parquet_crc"] = recomputed
        seen["controls"]["malformed_raw_suffix_extent"]["mutated_header_offset"] = raw[0]
        for key in ("malformed_level_extent", "malformed_expanded_gzip_extent", "malformed_page_row_count"):
            seen["controls"][key]["mutated_header_offset"] = last_offset
        for key in ("malformed_stored_level_crc", "malformed_member_crc_valid_outer",
                    "malformed_raw_suffix_extent", "malformed_expanded_gzip_extent"):
            wire, cause = late[key]
            commands.append(f"#guard keepsPrefix {lean_bytes(wire)} {ORDINAL} 1 {format_groups(expected[:1])} {cause}")

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
    print(f"PASS {len(files)} genuine GZIP-column V2 DATE IPC readbacks, "
          f"{sum(len(group['data']) for case in seen['cases'].values() for group in case['groups'])} original pages, "
          f"and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
