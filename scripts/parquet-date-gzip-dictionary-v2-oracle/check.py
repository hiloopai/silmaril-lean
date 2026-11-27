"""Compare genuine V2 GZIP DATE dictionary chunks with native Date32 IPC."""

import argparse
from importlib.metadata import version
import json
import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import zlib


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Gzip/V2/Tests.lean"
NAME, ORDINAL = "日付", 1
MIN_DAY, MAX_DAY = -(2**31), 2**31 - 1


def out_of_bounds(wire, frame, count, support):
    """Set the first packed 2-bit index to 3 and repair the stored page CRC."""
    offset, header, start, stored = frame
    thrift, hybrid = support["THRIFT"], support["hybrid"]
    levels = header[8][1][5][1]
    assert header[8][1][7][1] is False
    suffix = stored[levels:]
    width, first_run = suffix[:2]
    assert width == 2 and first_run & 1 and first_run < 128
    original_indices = hybrid(suffix[1:], width, count)
    assert all(i < 3 for i in original_indices)
    changed = suffix[:2] + bytes([suffix[2] | 3]) + suffix[3:]
    assert hybrid(changed[1:], width, count) == [3, *original_indices[1:]]
    repaired = stored[:levels] + changed
    crc = zlib.crc32(repaired)
    crc_signed = crc if crc < 2**31 else crc - 2**32
    encoded = thrift["encode"]({**header, 4: (thrift["TType"].I32, crc_signed)})
    assert len(encoded) == start - offset
    return wire[:offset] + encoded + repaired + wire[start + len(stored):], crc


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
    v2 = runpy.run_path(str(ROOT / "scripts/parquet-date-gzip-fallback-v2-oracle/check.py"))
    sample = runpy.run_path(str(ROOT / "scripts/parquet-date-snappy-fallback-oracle/check.py"))
    format_groups = runpy.run_path(str(ROOT / "scripts/parquet-date-selected-leaf-oracle/check.py"))["lean_groups"]
    ipc = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    pins = json.loads((ROOT / "scripts/parquet-date-gzip-fallback-v2-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    dictionary_limit = 2**20
    seen["producer"] = {"dictionary_pagesize_limit": dictionary_limit, "data_page_size": 24,
                        "zlib_runtime": zlib.ZLIB_RUNTIME_VERSION}

    patterns = (
        [MIN_DAY, None, -19, MAX_DAY, -19, None, MIN_DAY, MAX_DAY],
        [-719528, MAX_DAY, None, MIN_DAY, MIN_DAY, None, MAX_DAY, -719528],
    )

    def rows(batch, nullable):
        return [[day if nullable or day is not None else 0 for day in pattern] * (batch * 3 // 8)
                for pattern in patterns]

    cases = {"nullable_raw": (128, True, True, rows(128, True)),
             "nullable_gzip": (256, True, True, rows(256, True)),
             "required_no_crc": (128, False, False, rows(128, False))}
    files = {label: fallback["produce"](pa, pq, *settings, page_version="2.0", dictionary_limit=dictionary_limit)
             for label, settings in cases.items()}
    checked = {label: v2["inspect"](pa, pq, files[label], settings, support, prior, fallback, dictionary_only=True)
               for label, settings in cases.items()}
    for label, expected_flag in (("nullable_raw", False), ("nullable_gzip", True), ("required_no_crc", True)):
        assert {p["is_compressed"] for group in checked[label][0] for p in group["data"]} == {expected_flag}
        assert [len(group["data"]) for group in checked[label][0]] == [3, 3]

    raw, compressed = files["nullable_raw"], files["nullable_gzip"]
    raw_rows, compressed_rows = cases["nullable_raw"][-1], cases["nullable_gzip"][-1]
    raw_obs, raw_frames = checked["nullable_raw"]
    compressed_obs, compressed_frames = checked["nullable_gzip"]
    raw_reference = raw_frames[1][1][-1]
    compressed_dictionary, compressed_refs = compressed_frames[1]
    compressed_reference = compressed_refs[-1]

    def group_error(index, cause):
        return f"(.source (.groupFailure {index} {cause}))"

    def chunk_page(page, frame, cause):
        return f"(.chunk (.page {page} {frame[0]} {cause}))"

    def references(page, frame, cause):
        return chunk_page(page, frame, f"(.references {cause})")

    controls, prefixes = {}, []
    zero_writer = "{ ipc := { batches := 0 } }"

    def late_control(label, damaged, cause, expected):
        controls[label] = (damaged, group_error(1, cause), "{}", zero_writer)
        prefixes.append((label, cause, expected[:1]))

    for label, data, frame, page, expected in (
        ("dictionary", compressed, compressed_dictionary, 0, compressed_rows),
        ("raw_reference_levels", raw, raw_reference, 3, raw_rows),
        ("gzip_reference_levels", compressed, compressed_reference, 3, compressed_rows),
    ):
        assert page == 0 or frame[1][8][1][5][1] > 0
        damaged, (_, declared, computed) = prior["damaged_outer"](data, frame)
        prior["observe_refusal"](pa, pq, damaged, NAME, expected[0], crc=True)
        late_control(f"malformed_{label}_outer_crc", damaged,
                     chunk_page(page, frame, f"(.checksum (.mismatch {declared} {computed}))"), expected)

    inner = v2["inner_crc_control"](compressed, compressed_reference, prior, thrift)
    prior["observe_refusal"](pa, pq, inner, NAME, compressed_rows[0], crc=False)
    late_control("malformed_reference_inner_crc_valid_outer", inner,
                 references(3, compressed_reference, "(.page (.payload (.malformed .gzip)))"), compressed_rows)

    info = raw_reference[1][8][1]
    reference_count = info[1][1] - info[2][1]
    assert len(raw_obs[1]["dictionary"]["signed_entries"]) == 3
    bounds, repaired_crc = out_of_bounds(raw, raw_reference, reference_count, support)
    opened = pq.ParquetFile(pa.BufferReader(bounds), page_checksum_verification=True)
    *_, damaged = support["raw_frames"](bounds, opened.metadata.row_group(1).column(ORDINAL))
    assert damaged[0] == raw_reference[0] and zlib.crc32(damaged[3]) == repaired_crc == damaged[1][4][1] % 2**32
    prior["observe_refusal"](pa, pq, bounds, NAME, raw_rows[0], crc=False)
    late_control("malformed_reference_index_valid_crc", bounds,
                 references(3, raw_reference, "(.outOfBounds 3)"), raw_rows)

    levels = compressed_reference[1][8][1][5][1]
    multiple = fallback["append_member"](compressed, compressed_reference, thrift, level_bytes=levels)
    opened = pq.ParquetFile(pa.BufferReader(multiple), page_checksum_verification=True)
    assert prior["read_group"](pa, opened, NAME, 0) == compressed_rows[0]
    *_, appended = support["raw_frames"](multiple, opened.metadata.row_group(1).column(ORDINAL))
    assert appended[0] == compressed_reference[0]
    assert appended[3][:levels] == compressed_reference[3][:levels]
    assert zlib.crc32(appended[3]) == appended[1][4][1] % 2**32
    late_control("assembled_second_reference_member", multiple,
                 references(3, compressed_reference, "(.page (.payload (.trailingInput .gzip)))"), compressed_rows)

    late_rows = [[MIN_DAY, None] * 192, sample["groups"](128)[1]]
    late = fallback["produce"](pa, pq, 128, True, True, late_rows, page_version="2.0", dictionary_limit=8)
    opened = pq.ParquetFile(pa.BufferReader(late), page_checksum_verification=True)
    assert [prior["read_group"](pa, opened, NAME, i) for i in range(opened.num_row_groups)] == late_rows
    mixed = []
    for group in range(2):
        _, *pages = support["raw_frames"](late, opened.metadata.row_group(group).column(ORDINAL))
        mixed.append(pages)
    assert [[f[1][8][1][4][1] for f in pages] for pages in mixed] == [[8, 8, 8], [8, 0, 0, 0]]
    first_plain, reversal = mixed[1][1:3]
    cause = f"(.header 2 {first_plain[0]} (.encoding 0))"
    late_control("genuine_late_fallback", late, cause, late_rows)
    reentry = v2["edit_header"](late, reversal, {4: (thrift["TType"].I32, 8)}, thrift)
    late_control("malformed_reentry_after_first_plain", reentry, cause, late_rows)

    v1 = fallback["produce"](pa, pq, *cases["nullable_raw"], dictionary_limit=dictionary_limit)
    v1_file = pq.ParquetFile(pa.BufferReader(v1), page_checksum_verification=True)
    assert prior["read_group"](pa, v1_file, NAME, 0) == raw_rows[0]
    v1_col = v1_file.metadata.row_group(0).column(ORDINAL)
    _, *v1_pages = support["raw_frames"](v1, v1_col)
    assert all(f[1][1][1] == 0 and f[1][5][1][2][1] == 8 for f in v1_pages)
    first_group = compressed_obs[0]
    first_reference = raw_frames[0][1][0]
    controls.update({
        "genuine_v1_dictionary": (v1, group_error(0, f"(.header 1 {v1_col.data_page_offset} .expectedV2)"), "{}", "{}"),
        "low_expanded_chunk_cap": (compressed, group_error(0, "(.chunk .expandedChunkLimit)"),
                                    f"{{ maxExpandedChunkBytes := {first_group['expanded_total'] - 1} }}", "{}"),
        "low_index_byte_cap": (raw, group_error(0, references(1, first_reference, ".indexByteLimit")),
                               "{ indices := ⟨1048576, 0⟩ }", "{}"),
    })
    fingerprint = prior["fingerprint"]
    seen["cases"], seen["controls"] = {}, {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-gzip-dictionary-v2-") as temporary:
        folder = Path(temporary)
        outputs, commands, inputs = {}, [], {}

        def input_path(label, wire):
            path = folder / (label + ".parquet")
            path.write_bytes(wire)
            inputs[label] = json.dumps(str(path))
            return inputs[label]

        for label, wire in files.items():
            batch, nullable, checksum, expected = cases[label]
            groups = checked[label][0]
            all_pages = [[group["dictionary"], *group["data"]] for group in groups]
            spans = [tuple(group["span"]) for group in groups]
            offsets = [[page["frame"] for page in pages] for pages in all_pages]
            crcs = format_groups([[page["parquet_crc"] for page in pages] for pages in all_pages])
            entries = [group["dictionary"]["signed_entries"] for group in groups]
            flags = json.dumps([[page["is_compressed"] for page in group["data"]] for group in groups])
            stored_cap = max(stop - start for start, stop in spans)
            expanded_cap = max(group["expanded_total"] for group in groups)
            path = folder / (label + ".arrows")
            source = input_path(label, wire)
            label_text = json.dumps(NAME, ensure_ascii=False)
            commands.append(f"#eval (show IO Unit from do\n"
                            f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                            f"  readBack input {ORDINAL} {label_text} {str(nullable).lower()} {format_groups(expected)} "
                            f"{spans} {offsets} {crcs} {entries} {flags} {stored_cap} {expanded_cap} "
                            f"{json.dumps(str(path))}\n"
                            f"  unless olderProfilesRefuse input {ORDINAL} do\n"
                            f'    throw (IO.userError "an older profile admitted {label}"))')
            seen["cases"][label] = {"parquet": fingerprint(wire), "field": NAME, "selected_ordinal": ORDINAL,
                                    "nullable": nullable, "page_checksum": checksum, "write_batch_size": batch,
                                    "stored_chunk_cap": stored_cap, "expanded_chunk_cap": expanded_cap, "groups": groups}
            outputs[label] = (path, pa.schema([pa.field(NAME, pa.date32(), nullable=nullable)]), expected)
        for label, (wire, error, limits, output) in controls.items():
            source = input_path(label, wire)
            commands.append(f"#eval (show IO Unit from do\n"
                            f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                            f"  assertRejects {json.dumps(label)} input {ORDINAL} {error} {limits} {output})")
            seen["controls"][label] = {"parquet": fingerprint(wire), "error": error,
                                       "source_limits": limits, "output_limits": output}
        seen["controls"]["malformed_reference_index_valid_crc"]["repaired_crc"] = repaired_crc
        for label, cause, earlier in prefixes:
            commands.append(f"#eval (show IO Unit from do\n"
                            f"  let input := Bytes.mk (← IO.FS.readBinFile {inputs[label]})\n"
                            f"  unless keepsPrefix input {ORDINAL} 1 {format_groups(earlier)} {cause} do\n"
                            f'    throw (IO.userError "{label} prefix differed"))')
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
    print(f"PASS {len(files)} genuine dictionary-only V2 GZIP DATE files, "
          f"{sum(len(case[-1]) for case in cases.values())} original chunks and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
