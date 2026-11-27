"""Compare genuine ZSTD V2 DATE dictionary fallback with native Date32 IPC."""

import argparse
from importlib.metadata import version
import json
import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Fallback/Zstd/V2/Tests.lean"
NAME, ORDINAL = "日付", 1
MIN_DAY, MAX_DAY = -(2**31), 2**31 - 1
BATCH = 128


def launch_driver(folder, files, cases, inspected, controls, format_groups, pa, ipc):
    outputs, commands = {}, []

    def input_path(label, wire):
        path = folder / (label + ".parquet")
        path.write_bytes(wire)
        return json.dumps(str(path))

    for label, wire in files.items():
        nullable, _, rows, _, reference_pages = cases[label]
        observations = inspected[label][0]
        all_pages = [[group["dictionary"], *group["data"]] for group in observations]
        spans = [tuple(group["span"]) for group in observations]
        offsets = [[page["frame"] for page in pages] for pages in all_pages]
        crcs = format_groups([[page["parquet_crc"] for page in pages] for pages in all_pages])
        dictionaries = [group["dictionary"]["signed_entries"] for group in observations]
        flags = json.dumps([[p["is_compressed"] for p in group["data"]] for group in observations])
        tags = json.dumps([[p["tag"] for p in group["data"]] for group in observations])
        stored_cap = max(stop - start for start, stop in spans)
        expanded_cap = max(group["expanded_total"] for group in observations)
        first_plain = reference_pages + 1
        source = input_path(label, wire)
        out = folder / (label + ".arrows")
        commands.append(f"#eval (show IO Unit from do\n"
                        f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                        f"  readBack input {ORDINAL} {json.dumps(NAME, ensure_ascii=False)} "
                        f"{str(nullable).lower()} {format_groups(rows)} {spans} {offsets} {crcs} "
                        f"{dictionaries} {flags} {tags} {stored_cap} {expanded_cap} {json.dumps(str(out))}\n"
                        f"  unless strictProfilesRefuse input {ORDINAL} {first_plain} {offsets[0][first_plain]} do\n"
                        f'    throw (IO.userError "an existing strict reader admitted {label}"))')
        outputs[label] = (out, pa.schema([pa.field(NAME, pa.date32(), nullable)]), rows)

    for label, (wire, index, reason, limits, output, prefix) in controls.items():
        source = input_path(label, wire)
        commands.append(f"#eval (show IO Unit from do\n"
                        f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                        f"  assertRejects {json.dumps(label)} input {ORDINAL} "
                        f"(.source (.groupFailure {index} {reason})) {limits} {output}\n"
                        + (f"  unless keepsPrefix input {ORDINAL} {index} {format_groups(prefix)} {reason} do\n"
                           f'    throw (IO.userError "{label} prefix differed")\n' if prefix is not None else "")
                        + ")")

    driver = folder / "Oracle.lean"
    driver.write_text(TESTS.read_text(encoding="utf-8") + "\nset_option maxRecDepth 4096\n"
                      + "\n".join(commands) + "\n", encoding="utf-8")
    subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                    "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
    emitted = {}
    for label, (path, schema, rows) in outputs.items():
        wire = path.read_bytes()
        ipc["observe"](pa, wire, schema, rows)
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
    zstd = load("parquet-date-zstd-v1-oracle")
    zstd_v2 = load("parquet-date-zstd-v2-oracle")
    dictionary = load("parquet-date-zstd-dictionary-v2-oracle")
    support = load("parquet-timestamp-snappy-dictionary-oracle")
    thrift = support["THRIFT"]
    flat = load("parquet-flat-zstd")
    fallback = load("parquet-date-gzip-fallback-oracle")
    fallback_v2 = load("parquet-date-gzip-fallback-v2-oracle")
    example = load("parquet-date-snappy-fallback-oracle")
    format_groups = load("parquet-date-selected-leaf-oracle")["lean_groups"]
    ipc = load("arrow-date32-writer-oracle")
    pins = json.loads((ROOT / "scripts/parquet-date-zstd-dictionary-v2-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain", "frame_extent_libzstd",
                                      "producer_compression_level")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    extent = zstd["frame_extent"]()
    fingerprint = prior["fingerprint"]
    seen["producer"] = {"write_batch_size": BATCH, "data_page_size": 24, "row_seed": example["SEED"]}

    mixed_rows = example["groups"](BATCH)
    lead = [MIN_DAY, None, MAX_DAY, MIN_DAY, None, MAX_DAY, MIN_DAY, MAX_DAY] * (BATCH // 8)
    nullable_rows = [lead + group for group in mixed_rows]
    required_rows = [[0 if day is None else day for day in group] for group in mixed_rows]
    cases = {"nullable_crc_two_reference_pages": (True, True, nullable_rows, 12, 2),
             "required_no_crc_one_reference_page": (False, False, required_rows, 8, 1)}
    files = {label: dictionary["produce"](pa, pq, BATCH, nullable, crc, rows, dictionary_limit=cap)
             for label, (nullable, crc, rows, cap, _) in cases.items()}
    inspected = {
        label: dictionary["inspect"](pa, pq, files[label], (BATCH, nullable, crc, rows), prior, support,
                                    flat, fallback, extent, reference_pages=references)
        for label, (nullable, crc, rows, _, references) in cases.items()
    }
    label = "nullable_crc_two_reference_pages"
    source = files[label]
    observations, frames = inspected[label]
    for group in observations:
        for tag in (0, 8):
            assert {p["is_compressed"] for p in group["data"] if p["tag"] == tag} == {False, True}

    leading, pages = frames[1]
    raw_reference, compressed_reference, raw_plain, compressed_plain, _ = pages
    assert [frame[1][8][1][7][1] for frame in pages[:4]] == [False, True, False, True]
    controls, repaired = {}, {}
    writer_limit = "{ ipc := { batches := 0 } }"

    def late(label, wire, reason):
        controls[label] = (wire, 1, reason, "{}", writer_limit, nullable_rows[:1])

    def reference_crc(page, frame, error):
        return f"(.dictionary (.chunk (.page {page} {frame[0]} {error})))"

    for phase, number, frame in (
        ("dictionary", 0, leading),
        ("raw_reference_levels", 1, raw_reference),
        ("zstd_reference_levels", 2, compressed_reference),
        ("raw_plain_levels", 3, raw_plain),
        ("zstd_plain_levels", 4, compressed_plain),
    ):
        damaged, (_, declared, computed) = prior["damaged_outer"](source, frame)
        prior["observe_refusal"](pa, pq, damaged, NAME, nullable_rows[0], crc=True)
        checksum = f"(.mismatch {declared} {computed})"
        if phase == "dictionary":
            reason = f"(.dictionary (.dictionary {frame[0]} (.checksum {checksum})))"
        elif "reference" in phase:
            reason = reference_crc(number, frame, f"(.checksum {checksum})")
        else:
            reason = f"(.plain (.checksum {number} {frame[0]} {checksum}))"
        late(f"malformed_{phase}_stored_crc", damaged, reason)

    magic = "(.frame (.frame .badMagic))"
    for phase, number, frame in (("reference", 2, compressed_reference), ("plain", 4, compressed_plain)):
        levels = frame[1][8][1][5][1]
        stored = frame[3]
        # Keep the Compact header extent while independently verifying the bad suffix.
        for octet in range(256):
            edited = stored[:levels] + bytes([stored[levels] ^ 1, octet]) + stored[levels + 2:]
            try:
                damaged, crc = zstd["replace_stored"](source, frame, edited, thrift)
            except AssertionError:
                continue
            break
        else:
            raise AssertionError("No repaired CRC retained the original field extent")
        assert edited[:levels] == stored[:levels] and extent(edited[levels:]) is None
        prior["observe_refusal"](pa, pq, damaged, NAME, nullable_rows[0], crc=False)
        reason = (f"(.dictionary (.preparation {number} {frame[0]} {magic}))" if phase == "reference"
                  else f"(.plain (.decode {number} {frame[0]} {magic}))")
        key = f"malformed_{phase}_magic_valid_crc"
        late(key, damaged, reason)
        repaired[key] = crc

    wrong_flag = zstd_v2["change_flag"](source, raw_plain, True, thrift)
    assert extent(raw_plain[3][raw_plain[1][8][1][5][1]:]) is None
    late("malformed_raw_plain_flag_true", wrong_flag, f"(.plain (.decode 3 {raw_plain[0]} {magic}))")

    encoding = thrift["TType"].I32
    plain_first = fallback_v2["edit_header"](source, raw_reference, {4: (encoding, 0)}, thrift)
    late("malformed_plain_before_references", plain_first, f"(.sequence (.prefixEncoding 1 {raw_reference[0]} 0))")
    reentry = fallback_v2["edit_header"](source, compressed_plain, {4: (encoding, 8)}, thrift)
    reentry_cause = f"(.sequence (.suffixEncoding 4 {compressed_plain[0]} 8))"
    late("malformed_dictionary_reentry", reentry, reentry_cause)
    later = fallback_v2["edit_header"](reentry, pages[-1], {4: (encoding, 2)}, thrift)
    late("malformed_reentry_before_later_bad_header", later, reentry_cause)

    no_plain_rows = [nullable_rows[0], [MIN_DAY, None] * 192]
    no_plain = dictionary["produce"](pa, pq, BATCH, True, True, no_plain_rows, dictionary_limit=12)
    opened = pq.ParquetFile(pa.BufferReader(no_plain), page_checksum_verification=True)
    assert [prior["read_group"](pa, opened, NAME, i) for i in range(2)] == no_plain_rows
    _, *only_references = support["raw_frames"](no_plain, opened.metadata.row_group(1).column(ORDINAL))
    assert [p[1][8][1][4][1] for p in only_references] == [8, 8, 8]
    late("genuine_late_dictionary_only", no_plain, "(.sequence .missingPlain)")

    v1 = dictionary["produce"](pa, pq, BATCH, True, True, nullable_rows,
                               page_version="1.0", dictionary_limit=12)
    v1_file = pq.ParquetFile(pa.BufferReader(v1), page_checksum_verification=True)
    assert prior["read_group"](pa, v1_file, NAME, 0) == nullable_rows[0]
    v1_column = v1_file.metadata.row_group(0).column(ORDINAL)
    first_reference = frames[0][1][0]
    controls.update({
        "genuine_v1_fallback": (v1, 0, f"(.header 1 {v1_column.data_page_offset} .expectedV2)", "{}", "{}", None),
        "low_index_cap": (source, 0, reference_crc(1, first_reference, "(.references .indexByteLimit)"),
                          "{ indices := ⟨1048576, 0⟩ }", "{}", None),
        "low_expanded_chunk_cap": (source, 0, "(.dictionary (.chunk .expandedChunkLimit))",
                                   f"{{ maxExpandedChunkBytes := {observations[0]['expanded_total'] - 1} }}", "{}", None),
    })

    with tempfile.TemporaryDirectory(prefix="parquet-date-zstd-fallback-v2-") as temporary:
        emitted = launch_driver(Path(temporary), files, cases, inspected, controls, format_groups, pa, ipc)
    seen["cases"] = {
        label: {"parquet": fingerprint(files[label]), "field": NAME, "ordinal": ORDINAL,
                "nullable": nullable, "stored_crc": crc, "dictionary_pagesize_limit": cap,
                "reference_pages_per_group": references, "groups": inspected[label][0],
                "lean_ipc": fingerprint(emitted[label])}
        for label, (nullable, crc, _, cap, references) in cases.items()
    }
    seen["controls"] = {
        label: {"parquet": fingerprint(wire), "group": index, "cause": reason,
                "source_limits": limits, "output_limits": output}
        for label, (wire, index, reason, limits, output, _) in controls.items()
    }
    for label, crc in repaired.items():
        seen["controls"][label]["recomputed_parquet_crc"] = crc
    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(seen, indent=2)
    group_count = sum(len(case["groups"]) for case in seen["cases"].values())
    data_count = sum(len(group["data"]) for case in seen["cases"].values() for group in case["groups"])
    print(f"PASS {len(files)} genuine ZSTD V2 DATE fallback files, {group_count} dictionaries, "
          f"{data_count} data pages with both flags in each phase, and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
