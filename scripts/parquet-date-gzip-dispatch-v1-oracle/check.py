"""Compare genuine mixed V1 GZIP DATE groups with native Date32 IPC."""

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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Gzip/Dispatch/V1/Tests.lean"
NAME, ORDINAL = "日付", 1
MIN_DAY, MAX_DAY = -(2**31), 2**31 - 1


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
    pins = json.loads((ROOT / "scripts/parquet-date-gzip-dictionary-v1-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    seen["producer"] = {"seed": sample["SEED"], "dictionary_pagesize_limit": 8,
                        "data_page_size": 24, "zlib_runtime": zlib.ZLIB_RUNTIME_VERSION}

    def rows(nullable):
        return [[MIN_DAY, None if nullable else MIN_DAY] * 192,
                [day if nullable or day is not None else 0 for day in sample["groups"](128)[1]],
                [None if nullable else MAX_DAY, MAX_DAY] * 128]

    cases = {"nullable_crc": (128, True, True, rows(True)),
             "required_no_crc": (128, False, False, rows(False))}
    files = {label: fallback["produce"](pa, pq, *settings) for label, settings in cases.items()}
    checked = {label: fallback["inspect"](pa, pq, files[label], *settings, support, prior, dictionary_groups=(0, 2))
               for label, settings in cases.items()}
    for groups, _ in checked.values():
        assert [[page["tag"] for page in group["data"]] for group in groups] == [
            [8, 8, 8], [8, 0, 0, 0], [8, 8]]

    source = files["nullable_crc"]
    expected = cases["nullable_crc"][-1]
    observed, original = checked["nullable_crc"]
    fallback_pages = original[1][1]
    first_ref, first_plain, reversal, last_plain = fallback_pages
    last_dictionary, last_refs = original[2]
    last_ref = last_refs[-1]

    def group_error(index, cause):
        return f"(.source (.groupFailure {index} {cause}))"

    def chunk_page(page, frame, cause):
        return f"(.chunk (.page {page} {frame[0]} {cause}))"

    def references(page, frame, cause):
        return chunk_page(page, frame, f"(.references {cause})")

    controls, prefixes = {}, []
    zero_writer = "{ ipc := { batches := 0 } }"

    def group_control(label, damaged, index, cause, choice):
        controls[label] = (damaged, group_error(index, cause), "{}", zero_writer)
        prefixes.append((label, index, cause, choice))

    def external_crc_failure(damaged, index):
        opened = pq.ParquetFile(pa.BufferReader(damaged), page_checksum_verification=True)
        for earlier in range(index):
            assert prior["read_group"](pa, opened, NAME, earlier) == expected[earlier]
        try:
            prior["read_group"](pa, opened, NAME, index)
        except (pa.ArrowException, OSError) as error:
            assert "CRC" in str(error)
        else:
            raise AssertionError("PyArrow admitted a corrupted stored CRC")

    for label, index, frame, page, choice in (
        ("fallback_plain", 1, last_plain, 4, "fallback"),
        ("fallback_reference", 1, first_ref, 1, "fallback"),
        ("dictionary", 2, last_dictionary, 0, "dictionary"),
        ("dictionary_reference", 2, last_ref, 2, "dictionary"),
    ):
        damaged, (_, declared, computed) = prior["damaged_outer"](source, frame)
        external_crc_failure(damaged, index)
        cause = chunk_page(page, frame, f"(.checksum (.mismatch {declared} {computed}))")
        group_control(f"malformed_{label}_stored_crc", damaged, index, cause, choice)

    damaged_middle = controls["malformed_fallback_plain_stored_crc"][0]
    both, (_, declared, computed) = prior["damaged_outer"](damaged_middle, last_dictionary)
    external_crc_failure(both, 1)
    middle_cause = next(cause for label, _, cause, _ in prefixes if label == "malformed_fallback_plain_stored_crc")
    group_control("malformed_two_groups_first_failure", both, 1, middle_cause, "fallback")
    tail_cause = chunk_page(0, last_dictionary, f"(.checksum (.mismatch {declared} {computed}))")

    for label, index, frame, cause, choice in (
        ("fallback_plain", 1, last_plain,
         f"(.plain 4 {last_plain[0]} (.payload (.malformed .gzip)))", "fallback"),
        ("dictionary_reference", 2, last_ref,
         references(2, last_ref, "(.page (.payload (.malformed .gzip)))"), "dictionary"),
    ):
        damaged, _ = prior["damaged_member_crc"](source, frame, thrift)
        opened = pq.ParquetFile(pa.BufferReader(damaged), page_checksum_verification=True)
        assert [prior["read_group"](pa, opened, NAME, prior_index) for prior_index in range(index)] == expected[:index]
        group_control(f"malformed_{label}_member_crc_valid_outer", damaged, index, cause, choice)

    reentry = fallback["edit_encoding"](source, reversal, 8, thrift)
    group_control("malformed_reentry", reentry, 1, f"(.sequence (.suffixEncoding 3 {reversal[0]} 8))", "fallback")
    early_bad = fallback["edit_encoding"](reentry, first_plain, 5, thrift)
    group_control("malformed_unsupported_tag_before_reentry", early_bad, 1,
                  f"(.header 2 {first_plain[0]} (.encoding 5))", "fallback")

    v2 = fallback["produce"](pa, pq, *cases["nullable_crc"], page_version="2.0")
    v2_file = pq.ParquetFile(pa.BufferReader(v2), page_checksum_verification=True)
    assert prior["read_group"](pa, v2_file, NAME, 0) == expected[0]
    v2_col = v2_file.metadata.row_group(0).column(ORDINAL)
    plain_only = prior["produce"](pa, pq, NAME, True, True, expected)
    plain_file = pq.ParquetFile(pa.BufferReader(plain_only), page_checksum_verification=True)
    assert plain_file.metadata.row_group(0).column(ORDINAL).dictionary_page_offset is None
    assert prior["read_group"](pa, plain_file, NAME, 0) == expected[0]
    group = observed[0]
    controls.update({
        "genuine_v2_mixed_groups": (v2, group_error(0, f"(.header 1 {v2_col.data_page_offset} .expectedV1)"), "{}", "{}"),
        "genuine_plain_only": (plain_only, group_error(0, "(.chunk .dictionaryOffset)"), "{}", "{}"),
        "low_expanded_chunk_cap": (source, group_error(0, "(.chunk .expandedChunkLimit)"),
                                    f"{{ maxExpandedChunkBytes := {group['expanded_total'] - 1} }}", "{}"),
    })
    fingerprint = prior["fingerprint"]
    seen["cases"], seen["controls"] = {}, {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-gzip-dispatch-v1-") as temporary:
        folder = Path(temporary)
        outputs, commands, inputs = {}, [], {}

        def input_path(label, wire):
            path = folder / (label + ".parquet")
            path.write_bytes(wire)
            inputs[label] = json.dumps(str(path))
            return inputs[label]

        for label, wire in files.items():
            batch, nullable, checksum, slots = cases[label]
            groups = checked[label][0]
            all_pages = [[group["dictionary"], *group["data"]] for group in groups]
            spans = [tuple(group["span"]) for group in groups]
            offsets = [[page["frame"] for page in pages] for pages in all_pages]
            crcs = format_groups([[page["parquet_crc"] for page in pages] for pages in all_pages])
            entries = [group["dictionary"]["signed_entries"] for group in groups]
            stored_cap = max(stop - start for start, stop in spans)
            expanded_cap = max(group["expanded_total"] for group in groups)
            path = folder / (label + ".arrows")
            source = input_path(label, wire)
            label_text = json.dumps(NAME, ensure_ascii=False)
            commands.append(f"#eval (show IO Unit from do\n"
                            f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                            f"  readBack input {ORDINAL} {label_text} {str(nullable).lower()} {format_groups(slots)} "
                            f"{spans} {offsets} {crcs} {entries} [.dictionary, .fallback, .dictionary] {stored_cap} {expanded_cap} "
                            f"{json.dumps(str(path))}\n"
                            f"  unless uniformProfilesRefuse input {ORDINAL} {offsets[1][2]} do\n"
                            f'    throw (IO.userError "a uniform profile admitted {label}"))')
            seen["cases"][label] = {"parquet": fingerprint(wire), "field": NAME, "selected_ordinal": ORDINAL,
                                    "nullable": nullable, "page_checksum": checksum, "write_batch_size": batch,
                                    "stored_chunk_cap": stored_cap, "expanded_chunk_cap": expanded_cap,
                                    "profiles": ["dictionary", "fallback", "dictionary"], "groups": groups}
            outputs[label] = (path, pa.schema([pa.field(NAME, pa.date32(), nullable=nullable)]), slots)
        for label, (wire, error, limits, output) in controls.items():
            source = input_path(label, wire)
            commands.append(f"#eval (show IO Unit from do\n"
                            f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                            f"  assertRejects {json.dumps(label)} input {ORDINAL} {error} {limits} {output})")
            seen["controls"][label] = {"parquet": fingerprint(wire), "error": error,
                                       "source_limits": limits, "output_limits": output}
        for label, index, cause, choice in prefixes:
            commands.append(f"#eval (show IO Unit from do\n"
                            f"  let input := Bytes.mk (← IO.FS.readBinFile {inputs[label]})\n"
                            f"  unless keepsPrefix input {ORDINAL} {index} {format_groups(expected[:index])} {cause} do\n"
                            f'    throw (IO.userError "{label} prefix differed")\n'
                            f"  unless agrees input {ORDINAL} {index} .{choice} do\n"
                            f'    throw (IO.userError "{label} profile error differed"))')
        commands.append(f"#eval (show IO Unit from do\n"
                        f"  let input := Bytes.mk (← IO.FS.readBinFile {inputs['malformed_two_groups_first_failure']})\n"
                        f"  let .ok bound := Date.Leaf.openLeaf {{}} input {ORDINAL} | throw (IO.userError \"open failed\")\n"
                        f"  match Date.Leaf.Gzip.Dispatch.V1.readGroup {{}} bound 2 with\n"
                        f"  | .error cause => unless cause == {tail_cause} do throw (IO.userError \"tail cause differed\")\n"
                        f"  | .ok _ => throw (IO.userError \"tail unexpectedly succeeded\"))")
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
    print(f"PASS {len(files)} genuine mixed-profile V1 GZIP DATE files, "
          f"{sum(len(case[-1]) for case in cases.values())} original chunks and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
