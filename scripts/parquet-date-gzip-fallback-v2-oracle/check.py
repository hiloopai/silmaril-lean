"""Compare genuine V2 GZIP DATE dictionary fallback with native Date32 IPC."""

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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Fallback/Gzip/V2/Tests.lean"
NAME, ORDINAL = "日付", 1


def inspect(pa, pq, wire, settings, support, prior, fallback):
    batch, nullable, checksum, rows = settings
    thrift, hybrid = support["THRIFT"], support["hybrid"]
    gzip_member, fingerprint, read_group = [prior[key] for key in ("gzip_member", "fingerprint", "read_group")]
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow[ORDINAL] == pa.field(NAME, pa.date32(), nullable=nullable)
    assert str(parquet.schema.column(0).logical_type) == "None"
    assert [read_group(pa, parquet, NAME, i) for i in range(parquet.num_row_groups)] == rows
    _, meta = fallback["footer"](wire, thrift)
    kind = thrift["TType"]
    leaf = thrift["list_field"](meta, 2)[ORDINAL + 1]
    assert leaf[1] == (kind.I32, 1) and leaf[3] == (kind.I32, int(nullable))
    assert leaf[6] == (kind.I32, 6) and leaf[10] == (kind.STRUCT, {6: (kind.STRUCT, {})})

    def stored_frame(frame):
        offset, header, start, stored = frame
        assert len(stored) == header[3][1] and (4 in header) == checksum
        outer = header[4][1] % 2**32 if checksum else None
        if checksum:
            assert outer == zlib.crc32(stored)
        return {"frame": offset, "stored_start": start, "parquet_crc": outer,
                "stored": fingerprint(stored), "declared_expanded_size": header[2][1]}

    checked, originals = [], []
    for index, expected in enumerate(rows):
        column = parquet.metadata.row_group(index).column(ORDINAL)
        assert column.compression == "GZIP" and column.num_values == len(expected)
        assert set(column.encodings) == {"PLAIN", "RLE", "RLE_DICTIONARY"}
        dictionary, *pages = support["raw_frames"](wire, column)
        dict_obs = stored_frame(dictionary)
        expanded, member_crc = gzip_member(dictionary[3])
        assert dictionary[0] == column.dictionary_page_offset and dictionary[1][1][1] == 2
        assert dict_obs["declared_expanded_size"] == len(expanded)
        entries = [word for word, in struct.iter_unpack("<i", expanded)]
        assert [dictionary[1][7][1][i][1] for i in (1, 2)] == [len(entries), 0]
        assert entries == list(dict.fromkeys(day for day in expected[:batch] if day is not None))
        assert dictionary[2] + len(dictionary[3]) == pages[0][0] == column.data_page_offset
        cursor, observations = 0, []
        for frame in pages:
            assert frame[1][1][1] == 3
            page = stored_frame(frame)
            info = frame[1][8][1]
            count, nulls, page_rows, tag, levels, rep, is_compressed = [info[i][1] for i in range(1, 8)]
            slots = expected[cursor:cursor + count]
            cursor += count
            assert (count, nulls, page_rows, rep) == (batch, slots.count(None), batch, 0)
            assert is_compressed in (True, False) and info[7][0] == kind.BOOL
            assert 0 <= levels <= min(len(frame[3]), page["declared_expanded_size"])
            definitions, suffix = frame[3][:levels], frame[3][levels:]
            if nullable:
                assert hybrid(definitions, 1, count) == [int(x is not None) for x in slots]
            else:
                assert levels == 0 and nulls == 0
            values, inner_crc = gzip_member(suffix) if is_compressed else (suffix, None)
            assert len(values) + levels == page["declared_expanded_size"]
            present = [day for day in slots if day is not None]
            if tag == 8:
                indices = hybrid(values[1:], values[0], len(present))
                assert [entries[i] for i in indices] == present
            else:
                assert tag == 0
                assert [word for word, in struct.iter_unpack("<i", values)] == present
            observations.append({**page, "tag": tag, "rows": count, "nulls": nulls,
                                 "is_compressed": is_compressed, "member_crc": inner_crc,
                                 "raw_levels": fingerprint(definitions), "stored_suffix": fingerprint(suffix),
                                 "decoded_suffix": fingerprint(values)})
        assert cursor == len(expected) and [page["tag"] for page in observations] == [8, 0, 0, 0]
        stop = dictionary[0] + column.total_compressed_size
        assert pages[-1][2] + len(pages[-1][3]) == stop
        checked.append({"span": [dictionary[0], stop],
                        "dictionary": {**dict_obs, "member_crc": member_crc, "signed_entries": entries},
                        "expanded_total": len(expanded) + sum(p["declared_expanded_size"] for p in observations),
                        "data": observations})
        originals.append((dictionary, pages))
    return checked, originals


def edit_header(wire, frame, changes, thrift):
    offset, header, payload, _ = frame
    struct_kind, data = header[8]
    edited = thrift["encode"]({**header, 8: (struct_kind, {**data, **changes})})
    assert len(edited) == payload - offset
    return wire[:offset] + edited + wire[payload:]


def inner_crc_control(wire, frame, prior, thrift):
    _, header, _, stored = frame
    info = header[8][1]
    assert info[7][1] is True
    prior["gzip_member"](stored[info[5][1]:])
    # The previous helper flips the trailer CRC, repairs the outer CRC, and checks zlib rejection.
    return prior["damaged_member_crc"](wire, frame, thrift, level_bytes=info[5][1])[0]


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
    prior = runpy.run_path(str(ROOT / "scripts/parquet-date-gzip-v1-oracle/check.py"))
    fallback = runpy.run_path(str(ROOT / "scripts/parquet-date-gzip-fallback-oracle/check.py"))
    sample = runpy.run_path(str(ROOT / "scripts/parquet-date-snappy-fallback-oracle/check.py"))
    format_groups = runpy.run_path(str(ROOT / "scripts/parquet-date-selected-leaf-oracle/check.py"))["lean_groups"]
    ipc = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    pins = json.loads((ROOT / "scripts/parquet-date-gzip-fallback-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    seen["producer"] = {"seed": sample["SEED"], "dictionary_pagesize_limit": 8, "data_page_size": 24,
                        "zlib_runtime": zlib.ZLIB_RUNTIME_VERSION}

    raw_rows = sample["groups"](128)
    compressed_rows = sample["groups"](256)
    # End the second group with repeat data so its final original suffix has a GZIP member.
    last = compressed_rows[-1]
    compressed_rows[-1] = last[:512] + last[768:] + last[512:768]
    required = [[0 if day is None else day for day in group] for group in sample["groups"](128)]
    cases = {"nullable_raw_references": (128, True, True, raw_rows),
             "nullable_gzip_references": (256, True, True, compressed_rows),
             "required_no_crc": (128, False, False, required)}
    files = {label: fallback["produce"](pa, pq, *settings, page_version="2.0")
             for label, settings in cases.items()}
    checked = {label: inspect(pa, pq, files[label], settings, support, prior, fallback)
               for label, settings in cases.items()}
    for label, expected_flag in (("nullable_raw_references", False), ("nullable_gzip_references", True),
                                 ("required_no_crc", True)):
        groups, _ = checked[label]
        assert {group["data"][0]["is_compressed"] for group in groups} == {expected_flag}
        assert {p["is_compressed"] for group in groups for p in group["data"][1:]} == {False, True}

    compressed = files["nullable_gzip_references"]
    raw = files["nullable_raw_references"]
    _, raw_frames = checked["nullable_raw_references"]
    packed_obs, packed_frames = checked["nullable_gzip_references"]
    dictionary, packed = packed_frames[1]
    raw_reference = raw_frames[1][1][0]
    first, first_plain, reversal, last_raw = raw_frames[0][1]
    packed_plain = packed[-1]
    assert packed_plain[1][8][1][7][1] is True
    assert packed[1][1][8][1][7][1] is False

    def group_error(index, cause):
        return f"(.source (.groupFailure {index} {cause}))"

    def chunk_page(page, frame, cause):
        return f"(.chunk (.page {page} {frame[0]} {cause}))"

    def references(page, frame, cause):
        return chunk_page(page, frame, f"(.references (.page {cause}))")

    def plain(page, frame, cause):
        return f"(.plain {page} {frame[0]} {cause})"

    controls, prefixes = {}, []
    zero_writer = "{ ipc := { batches := 0 } }"

    def late_control(label, damaged, cause, rows):
        controls[label] = (damaged, group_error(1, cause), "{}", zero_writer)
        prefixes.append((damaged, cause, rows[:1]))

    for label, data, frame, page, rows in (
        ("dictionary", compressed, dictionary, 0, compressed_rows),
        ("raw_reference_levels", raw, raw_reference, 1, raw_rows),
        ("compressed_plain_levels", compressed, packed_plain, 4, compressed_rows),
        ("raw_plain_levels", compressed, packed[1], 2, compressed_rows),
    ):
        damaged, (_, declared, computed) = prior["damaged_outer"](data, frame)
        prior["observe_refusal"](pa, pq, damaged, NAME, rows[0], crc=True)
        late_control(f"malformed_{label}_outer_crc", damaged,
                     chunk_page(page, frame, f"(.checksum (.mismatch {declared} {computed}))"), rows)
    member_error = "(.payload (.malformed .gzip))"
    for label, frame, cause in (
        ("compressed_reference", packed[0], references(1, packed[0], member_error)),
        ("compressed_plain", packed_plain, plain(4, packed_plain, member_error)),
    ):
        damaged = inner_crc_control(compressed, frame, prior, thrift)
        prior["observe_refusal"](pa, pq, damaged, NAME, compressed_rows[0], crc=False)
        late_control(f"malformed_{label}_inner_crc_valid_outer", damaged, cause, compressed_rows)

    multiple = fallback["append_member"](compressed, packed_plain, thrift, level_bytes=packed_plain[1][8][1][5][1])
    opened = pq.ParquetFile(pa.BufferReader(multiple), page_checksum_verification=True)
    assert prior["read_group"](pa, opened, NAME, 0) == compressed_rows[0]
    *_, appended = support["raw_frames"](multiple, opened.metadata.row_group(1).column(ORDINAL))
    assert appended[0] == packed_plain[0] and zlib.crc32(appended[3]) == appended[1][4][1] % 2**32
    # The V2 prefix is raw, so independently split it before testing member exhaustion.
    prefix_size = appended[1][8][1][5][1]
    member = zlib.decompressobj(wbits=31)
    assert member.decompress(appended[3][prefix_size:]) == zlib.decompress(packed_plain[3][prefix_size:], wbits=31)
    assert member.eof and zlib.decompress(member.unused_data, wbits=31) == b""
    late_control("assembled_second_suffix_member", multiple,
                 plain(4, packed_plain, "(.payload (.trailingInput .gzip))"), compressed_rows)

    i32, boolean = thrift["TType"].I32, thrift["TType"].BOOL
    raw_info = raw_reference[1][8][1]

    def framing(cause):
        return f"(.chunk (.framing (.header {cause})))"

    late_control("malformed_raw_reference_flag_true", edit_header(raw, raw_reference, {7: (boolean, True)}, thrift),
                 references(1, raw_reference, member_error), raw_rows)
    late_control("malformed_gzip_reference_flag_false", edit_header(compressed, packed[0], {7: (boolean, False)}, thrift),
                 framing(".invalidV2Lengths"), compressed_rows)
    late_control("malformed_reference_repetition_extent", edit_header(raw, raw_reference, {6: (i32, 1)}, thrift),
                 references(1, raw_reference, "(.levels .unexpectedRepetitionSection)"), raw_rows)
    late_control("malformed_reference_level_extent", edit_header(raw, raw_reference, {5: (i32, 63)}, thrift),
                 framing(".invalidV2Lengths"), raw_rows)
    late_control("malformed_reference_null_count",
                 edit_header(raw, raw_reference, {2: (i32, raw_info[2][1] + 1)}, thrift),
                 references(1, raw_reference, "(.levels .presentCountMismatch)"), raw_rows)
    late_control("malformed_reference_row_count",
                 edit_header(raw, raw_reference, {3: (i32, raw_info[3][1] + 1)}, thrift),
                 framing(".invalidV2Counts"), raw_rows)

    phase = edit_header(raw, reversal, {4: (i32, 8)}, thrift)
    v1 = fallback["produce"](pa, pq, *cases["nullable_raw_references"])
    dictionary_only = fallback["produce"](pa, pq, *cases["nullable_raw_references"],
                                          page_version="2.0", dictionary_limit=2**20)
    for data in (v1, dictionary_only):
        opened = pq.ParquetFile(pa.BufferReader(data), page_checksum_verification=True)
        assert [prior["read_group"](pa, opened, NAME, i) for i in range(opened.num_row_groups)] == raw_rows
    v1_col = pq.ParquetFile(pa.BufferReader(v1)).metadata.row_group(0).column(ORDINAL)
    dictionary_col = pq.ParquetFile(pa.BufferReader(dictionary_only)).metadata.row_group(0).column(ORDINAL)
    dict_pages = list(support["raw_frames"](dictionary_only, dictionary_col))[1:]
    assert all(p[1][1][1] == 3 and p[1][8][1][4][1] == 8 for p in dict_pages)
    first_group = packed_obs[0]
    chunk_size = first_group["span"][1] - first_group["span"][0]
    controls.update({
        "genuine_v1_fallback": (v1, group_error(0, f"(.header 1 {v1_col.data_page_offset} .expectedV2)"), "{}", "{}"),
        "genuine_v2_dictionary_only": (dictionary_only, group_error(0, "(.sequence .missingPlain)"), "{}", "{}"),
        "malformed_reentry_before_bad_header": (edit_header(phase, last_raw, {4: (i32, 5)}, thrift),
                                  group_error(0, f"(.sequence (.suffixEncoding 3 {reversal[0]} 8))"), "{}", "{}"),
        "malformed_bad_header_before_reentry": (edit_header(phase, first_plain, {4: (i32, 5)}, thrift),
                                  group_error(0, f"(.header 2 {first_plain[0]} (.encoding 5))"), "{}", "{}"),
        "malformed_plain_first": (edit_header(raw, first, {4: (i32, 0)}, thrift),
                                  group_error(0, f"(.sequence (.prefixEncoding 1 {first[0]} 0))"), "{}", "{}"),
        "low_stored_chunk_cap": (compressed, group_error(0, "(.chunk .chunkLimit)"),
                                 f"{{ maxChunkBytes := {chunk_size - 1} }}", "{}"),
        "low_expanded_chunk_cap": (compressed, group_error(0, "(.chunk .expandedChunkLimit)"),
                                    f"{{ maxExpandedChunkBytes := {first_group['expanded_total'] - 1} }}", "{}"),
        "low_raw_index_byte_cap": (raw, group_error(0, chunk_page(1, first, "(.references .indexByteLimit)")),
                                   "{ indices := ⟨1048576, 0⟩ }", "{}"),
    })

    fingerprint = prior["fingerprint"]
    seen["cases"], seen["controls"] = {}, {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-gzip-fallback-v2-") as temporary:
        folder = Path(temporary)
        outputs, commands = {}, []

        def input_path(label, wire):
            path = folder / (label + ".parquet")
            path.write_bytes(wire)
            return json.dumps(str(path))

        for label, wire in files.items():
            batch, nullable, checksum, rows = cases[label]
            groups = checked[label][0]
            all_pages = [[group["dictionary"], *group["data"]] for group in groups]
            bounds = [tuple(group["span"]) for group in groups]
            offsets = [[page["frame"] for page in pages] for pages in all_pages]
            crcs = format_groups([[page["parquet_crc"] for page in pages] for pages in all_pages])
            entries = [group["dictionary"]["signed_entries"] for group in groups]
            flags = json.dumps([[page["is_compressed"] for page in group["data"]] for group in groups])
            stored_cap = max(stop - start for start, stop in bounds)
            expanded_cap = max(group["expanded_total"] for group in groups)
            path = folder / (label + ".arrows")
            label_text = json.dumps(NAME, ensure_ascii=False)
            source = input_path(label, wire)
            commands.append(f"#eval (show IO Unit from do\n"
                            f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                            f"  readBack input {ORDINAL} {label_text} {str(nullable).lower()} {format_groups(rows)} "
                            f"{bounds} {offsets} {crcs} {entries} {flags} {stored_cap} {expanded_cap} "
                            f"{json.dumps(str(path))}\n"
                            f"  unless olderProfilesRefuse input {ORDINAL} {offsets[0][1]} do\n"
                            f'    throw (IO.userError "an older profile admitted {label}"))')
            seen["cases"][label] = {"parquet": fingerprint(wire), "field": NAME, "selected_ordinal": ORDINAL,
                                    "nullable": nullable, "page_checksum": checksum, "write_batch_size": batch,
                                    "stored_chunk_cap": stored_cap, "expanded_chunk_cap": expanded_cap,
                                    "groups": groups}
            outputs[label] = (path, pa.schema([pa.field(NAME, pa.date32(), nullable=nullable)]), rows)
        for label, (wire, error, limits, output) in controls.items():
            source = input_path(label, wire)
            commands.append(f"#eval (show IO Unit from do\n"
                            f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                            f"  assertRejects {json.dumps(label)} input {ORDINAL} {error} {limits} {output})")
            seen["controls"][label] = {"parquet": fingerprint(wire), "error": error,
                                       "source_limits": limits, "output_limits": output}
        for index, (wire, cause, earlier) in enumerate(prefixes):
            source = input_path(f"prefix-{index}", wire)
            commands.append(f"#eval (show IO Unit from do\n"
                            f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                            f"  unless keepsPrefix input {ORDINAL} 1 {format_groups(earlier)} {cause} do\n"
                            f'    throw (IO.userError "prefix {index} differed"))')
        driver = folder / "Oracle.lean"
        driver.write_text(TESTS.read_text(encoding="utf-8") + "\nset_option maxRecDepth 4096\n"
                          + "\n".join(commands) + "\n", encoding="utf-8")
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
        assert seen == json.loads(manifest.read_text(encoding="utf-8"))
    print(f"PASS {len(files)} genuine V2 GZIP DATE fallback files, "
          f"{sum(len(case[-1]) for case in cases.values())} mixed chunks and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
