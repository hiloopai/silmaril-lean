"""Check explicitly selected Snappy V2 DATE dictionary-only and fallback profiles."""

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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Snappy/V2/Tests.lean"
NAME, ORDINAL = "日付", 1


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

    support = load("parquet-timestamp-snappy-dictionary")
    thrift = support["THRIFT"]
    dictionary, fallback = load("parquet-date-snappy-dictionary"), load("parquet-date-snappy-fallback")
    reader = load("parquet-date-dictionary")["read_group"]
    format_groups = load("parquet-date-selected-leaf")["lean_groups"]
    ipc = load("arrow-date32-writer")
    fingerprint = fallback["fingerprint"]
    prior_pins = {profile: json.loads((ROOT / "scripts" / f"parquet-date-snappy-{profile}-oracle"
                                      / "fixtures.json").read_text(encoding="utf-8"))
                  for profile in ("dictionary", "fallback")}
    seen = {key: prior_pins["dictionary"][key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256",
            "thrift", "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    seen["zlib_runtime"] = zlib.ZLIB_RUNTIME_VERSION
    positives = {}

    def pin_case(label, parent, old_label, profile, wire, rows, checked):
        old_case = prior_pins[parent]["cases"][old_label]
        assert fingerprint(wire) == old_case["parquet"] and checked[0] == old_case["groups"]
        positives[label] = (profile, wire, rows, checked, old_case["lean_ipc"])

    for checksum, label, old_label in [(True, "dictionary_crc", "v2_crc"),
                                       (False, "dictionary_no_crc", "v2_no_crc")]:
        wire = dictionary["produce"](pa, pq, "2.0", checksum=checksum)
        checked = dictionary["inspect"](pa, pq, wire, "2.0", checksum, support, reader)
        pin_case(label, "dictionary", old_label, ".dictionaryOnly", wire, dictionary["GROUPS"], checked)
    for batch, label, old_label in [(128, "fallback_compressed_references", "v2"),
                                    (32, "fallback_literal_references", "v2_raw_references")]:
        rows = fallback["groups"](batch)
        wire = fallback["produce"](pa, pq, "2.0", batch, rows)
        checked = fallback["inspect"](pa, pq, wire, "2.0", batch, rows, support, reader)
        pin_case(label, "fallback", old_label, ".fallback", wire, rows, checked)

    controls = {}

    def add(label, profile, wire, index, cause, *, earlier=None, limits="{}"):
        controls[label] = (profile, wire, index, cause, earlier, limits)

    _, dictionary_wire, dict_rows, (dict_observed, dict_frames), _ = positives["dictionary_crc"]
    _, fallback_wire, fallback_rows, (fallback_observed, fallback_frames), _ = positives[
        "fallback_compressed_references"]
    v1_dictionary = dictionary["produce"](pa, pq, "1.0")
    v1_fallback = fallback["produce"](pa, pq, "1.0", 128, fallback_rows)
    for (suffix, parent, profile, wire, rows) in [
        ("dictionary", "dictionary", ".dictionaryOnly", v1_dictionary, dict_rows),
        ("fallback", "fallback", ".fallback", v1_fallback, fallback_rows),
    ]:
        compare = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
        assert [reader(pa, compare, i) for i in range(compare.num_row_groups)] == rows
        old_label = "v1_crc" if parent == "dictionary" else "v1"
        assert fingerprint(wire) == prior_pins[parent]["cases"][old_label]["parquet"]
        column = compare.metadata.row_group(0).column(ORDINAL)
        frame = list(support["raw_frames"](wire, column))[1]
        assert frame[1][1][1] == 0
        add("genuine_v1_" + suffix, profile, wire, 0, f"(.header 1 {frame[0]} .expectedV2)")

    fallback_first_plain = fallback_frames[0][1][1]
    add("genuine_fallback_under_dictionary_only", ".dictionaryOnly", fallback_wire, 0,
        f"(.header 2 {fallback_first_plain[0]} (.data (.encoding 0)))")
    add("genuine_dictionary_only_under_fallback", ".fallback", dictionary_wire, 0, "(.sequence .missingPlain)")

    crc_bad, offset, declared, actual = dictionary["corrupt_crc"](dictionary_wire, dict_frames[2][0])
    dictionary["assert_refusal"](pa, pq, crc_bad, 2, reader, crc=True)
    add("mutated_late_dictionary_crc", ".dictionaryOnly", crc_bad, 2,
        f"(.chunk (.page 0 {offset} (.checksum (.mismatch {declared} {actual}))))", earlier=dict_rows[:2])

    refs, recomputed, _ = dictionary["corrupt_reference"](
        dictionary_wire, dict_frames[1][1], dict_observed[1]["stored_suffix_start"], thrift)
    dictionary["assert_refusal"](pa, pq, refs, 1, reader)
    add("mutated_late_invalid_reference_valid_crc", ".dictionaryOnly", refs, 1,
        f"(.decode (.snappy (.page 1 {dict_frames[1][1][0]} (.references (.outOfBounds 3)))))",
        earlier=dict_rows[:1])

    crc_bad, (offset, declared, actual) = fallback["corrupt_crc"](fallback_wire, fallback_frames[1][1][-1])
    fallback["observe_crc_refusal"](pa, pq, crc_bad, fallback_rows, reader)
    add("mutated_late_fallback_plain_crc", ".fallback", crc_bad, 1,
        f"(.decode (.snappy (.page 4 {offset} (.checksum (.mismatch {declared} {actual})))))",
        earlier=fallback_rows[:1])
    reentry, later = fallback_frames[1][1][2:]
    changed = fallback["edit_v2_header"](fallback_wire, reentry, {4: 8}, thrift)
    changed = fallback["edit_v2_header"](changed, later, {4: 5}, thrift)
    add("mutated_late_reentry_before_unsupported_header", ".fallback", changed, 1,
        f"(.sequence (.suffixEncoding 3 {reentry[0]} 8))", earlier=fallback_rows[:1])
    changed = fallback["edit_v2_header"](fallback_wire, fallback_frames[1][1][0], {4: 0}, thrift)
    add("mutated_late_plain_at_prefix", ".fallback", changed, 1,
        f"(.sequence (.prefixEncoding 1 {fallback_frames[1][1][0][0]} 0))", earlier=fallback_rows[:1])
    add("low_aggregate_expansion_cap", ".fallback", fallback_wire, 0, "(.chunk .expandedChunkLimit)",
        limits=f"{{ maxExpandedChunkBytes := {fallback_observed[0]['expanded_total'] - 1} }}")

    seen["cases"], seen["controls"] = {}, {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-snappy-dictionary-v2-") as temporary:
        folder = Path(temporary)
        commands, outputs = [], {}

        def path_for(name, wire):
            path = folder / (name + ".parquet")
            path.write_bytes(wire)
            return json.dumps(str(path))

        for label, (profile, wire, rows, (observed, frames), old_ipc) in positives.items():
            groups = [[chunk[0], *chunk[1]] if profile == ".fallback" else list(chunk) for chunk in frames]
            bounds = [tuple(group["span"]) for group in observed]
            offsets = [[frame[0] for frame in group] for group in groups]
            crcs = [[frame[1][4][1] % 2**32 if 4 in frame[1] else None for frame in group] for group in groups]
            flags = [[frame[1][8][1][7][1] for frame in group[1:]] for group in groups]
            cap = max(sum(frame[1][2][1] for frame in group) for group in groups)
            path = folder / (label + ".arrows")
            commands.append(f"#eval (show IO Unit from do\n"
                            f"  let input := Bytes.mk (← IO.FS.readBinFile {path_for(label, wire)})\n"
                            f"  readBack {profile} input {ORDINAL} {json.dumps(NAME, ensure_ascii=False)} "
                            f"{format_groups(rows)} {bounds} {offsets} {format_groups(crcs)} "
                            f"{json.dumps(flags)} {cap} {json.dumps(str(path))})")
            seen["cases"][label] = {"profile": profile[1:], "parquet": fingerprint(wire), "frames": offsets,
                                    "crc": crcs, "value_suffix_compressed": flags, "expanded_chunk_cap": cap}
            outputs[label] = (path, rows, old_ipc)

        for label, (profile, wire, index, cause, earlier, limits) in controls.items():
            output = "{ ipc := { batches := 0 } }" if earlier is not None else "{}"
            error = f"(.source (.groupFailure {index} {cause}))"
            cmd = (f"#eval (show IO Unit from do\n"
                   f"  let input := Bytes.mk (← IO.FS.readBinFile {path_for(label, wire)})\n"
                   f"  unless rejects {profile} input {ORDINAL} {error} {limits} {output} do\n"
                   f"    throw (IO.userError \"{label}: expected {error}\")")
            if earlier is not None:
                cmd += (f"\n  unless keepsPrefix {profile} input {ORDINAL} {index} {format_groups(earlier)} {cause} do\n"
                        f"    throw (IO.userError \"{label}: completed prefix differed\")")
            commands.append(cmd + ")")
            seen["controls"][label] = {"profile": profile[1:], "parquet": fingerprint(wire), "error": error,
                                       "source_limits": limits, "output_limits": output}
        seen["controls"]["mutated_late_invalid_reference_valid_crc"]["recomputed_crc"] = recomputed
        driver = folder / "Oracle.lean"
        driver.write_text(TESTS.read_text(encoding="utf-8") + "\nset_option maxRecDepth 8192\n"
                          + "\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
        for label, (path, rows, old_ipc) in outputs.items():
            emitted = path.read_bytes()
            assert emitted.endswith(bytes.fromhex("ffffffff00000000"))
            ipc["observe"](pa, emitted, pa.schema([pa.field(NAME, pa.date32())]), rows)
            seen["cases"][label]["lean_ipc"] = fingerprint(emitted)
            assert seen["cases"][label]["lean_ipc"] == old_ipc

    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8"))
    print(f"PASS {len(positives)} genuine Snappy-backed DATE V2 files and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
