"""Check three Snappy DATE V2 routes in an assembly of genuine PyArrow chunks."""

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


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Snappy/Dispatch/V2/Tests.lean"
NAME, ORDINAL = "日付", 1
ORDER = (("plain", 0), ("dictionary", 0), ("fallback", 0),
         ("plain", 1), ("dictionary", 1), ("fallback_literal", 1))
BRANCHES = ("plain", "dictionaryOnly", "fallback", "plain", "dictionaryOnly", "fallback")


def run_lean(folder, wire, groups, rows, controls, format_groups):
    def save(label, source):
        path = folder / (label + ".parquet")
        path.write_bytes(source)
        return json.dumps(str(path))

    source = save("assembly", wire)
    out = folder / "assembly.arrows"
    frames = [([group["dictionary"]] if "dictionary" in group else []) + group["data"] for group in groups]
    spans = [tuple(group["span"]) for group in groups]
    offsets = [[page["frame"] for page in pages] for pages in frames]
    crcs = format_groups([[page["parquet_crc"] for page in pages] for pages in frames])
    branches = "[" + ", ".join("." + name for name in BRANCHES) + "]"
    flags = json.dumps([[page["is_compressed"] for page in group["data"]] for group in groups])
    stored = max(stop - start for start, stop in spans)
    expanded = max(group["expanded_total"] for group in groups)
    limits = f"{{ maxChunkBytes := {stored}, maxExpandedChunkBytes := {expanded}, maxRows := {max(map(len, rows))} }}"
    commands = [f"#eval (show IO Unit from do\n"
                f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                f"  readBack input {ORDINAL} {json.dumps(NAME, ensure_ascii=False)} true "
                f"{format_groups(rows)} {spans} {offsets} {crcs} {branches} {flags} "
                f"{limits} {json.dumps(str(out))})"]
    for label, (case, index, cause, branch, prefix, caps) in controls.items():
        commands.append(f"#eval (show IO Unit from do\n"
                        f"  let input := Bytes.mk (← IO.FS.readBinFile {save(label, case)})\n"
                        f"  assertRejects {json.dumps(label)} input {ORDINAL} {index} .{branch} "
                        f"{format_groups(prefix)} {cause} {caps})")
    driver = folder / "Oracle.lean"
    driver.write_text(TESTS.read_text(encoding="utf-8") + "\nset_option maxRecDepth 8192\n"
                      + "\n".join(commands) + "\n", encoding="utf-8")
    subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                    "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
    return out.read_bytes()


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

    def pins(name):
        return json.loads((ROOT / "scripts" / f"{name}-oracle" / "fixtures.json").read_text(encoding="utf-8"))

    prior = load("parquet-date-gzip-v1")
    sample = load("parquet-date-gzip-v2")
    support = load("parquet-timestamp-snappy-dictionary")
    reader = load("parquet-date-dictionary")["read_group"]
    thrift = support["THRIFT"]
    plain = load("parquet-date-snappy-plain-v2")
    dictionary, fallback = load("parquet-date-snappy-dictionary"), load("parquet-date-snappy-fallback")
    assembly, relocate = load("parquet-date-gzip-plain-dispatch-v2"), load("parquet-timestamp-mixed-groups")
    footer = load("parquet-date-gzip-fallback")["footer"]
    format_groups = load("parquet-date-selected-leaf")["lean_groups"]
    ipc = load("arrow-date32-writer")
    fingerprint = prior["fingerprint"]
    versions = pins("parquet-date-snappy-dictionary-v2")
    seen = {key: versions[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                          "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]

    plain_rows = sample["mixed_groups"](True)
    by_parent = {"plain": plain_rows, "dictionary": dictionary["GROUPS"],
                 "fallback": fallback["groups"](128), "fallback_literal": fallback["groups"](32)}
    parents = {"plain": plain["produce"](pa, pq, NAME, True, True, plain_rows, sample["BATCH"]),
               "dictionary": dictionary["produce"](pa, pq, "2.0"),
               "fallback": fallback["produce"](pa, pq, "2.0", 128, by_parent["fallback"]),
               "fallback_literal": fallback["produce"](pa, pq, "2.0", 32, by_parent["fallback_literal"])}
    captures = {
        "plain": plain["inspect"](pa, pq, parents["plain"], NAME, True, True, plain_rows, prior, support),
        "dictionary": dictionary["inspect"](pa, pq, parents["dictionary"], "2.0", True, support, reader),
        "fallback": fallback["inspect"](pa, pq, parents["fallback"], "2.0", 128, by_parent["fallback"],
                                       support, reader),
        "fallback_literal": fallback["inspect"](pa, pq, parents["fallback_literal"], "2.0", 32,
                                               by_parent["fallback_literal"], support, reader),
    }
    strict_pins = pins("parquet-date-snappy-dictionary-v2")["cases"]
    expected_pins = {"plain": pins("parquet-date-snappy-plain-v2")["cases"]["nullable_crc"]["parquet"],
                     "dictionary": strict_pins["dictionary_crc"]["parquet"],
                     "fallback": strict_pins["fallback_compressed_references"]["parquet"],
                     "fallback_literal": strict_pins["fallback_literal_references"]["parquet"]}
    assert {label: fingerprint(wire) for label, wire in parents.items()} == expected_pins

    def observe(frame):
        offset, header, start, stored = frame
        page = {"frame": offset, "stored_start": start, "parquet_crc": header[4][1] % 2**32,
                "stored": fingerprint(stored), "expanded_bytes": header[2][1]}
        if header[1][1] == 3:
            info = header[8][1]
            levels = info[5][1]
            page.update({"tag": info[4][1], "is_compressed": info[7][1], "levels": fingerprint(stored[:levels]),
                         "stored_suffix": fingerprint(stored[levels:])})
        return page

    observed = {}
    for label, (metadata, frames) in captures.items():
        groups = []
        for chunk, original in zip(metadata, frames, strict=True):
            if label.startswith("fallback"):
                original = [original[0], *original[1]]
            pages = list(map(observe, original))
            group = {"span": chunk["span"], "expanded_total": sum(page["expanded_bytes"] for page in pages)}
            if label != "plain":
                group["dictionary"] = pages.pop(0)
            group["data"] = pages
            groups.append(group)
        observed[label] = groups

    rows = [by_parent[label][group] for label, group in ORDER]
    wire, groups = assembly["assemble"](parents, observed, footer, thrift, relocate["column_extent"],
                                         relocate["relocate_offset"], order=ORDER, profiles=BRANCHES)
    frames = assembly["inspect_assembly"](pa, pq, wire, parents, observed, groups, rows, True,
                                           prior, support, compression="SNAPPY")
    for phase in (0, 8):
        assert {p["is_compressed"] for group in groups if group["profile"] == "fallback"
                for p in group["data"] if p["tag"] == phase} == {False, True}
    controls = {}

    def add(label, case, index, cause, branch=None, caps="{}"):
        controls[label] = (case, index, cause, BRANCHES[index] if branch is None else branch, rows[:index], caps)

    def source_refuses(case, index, message=None):
        opened = pq.ParquetFile(pa.BufferReader(case), page_checksum_verification=True)
        assert [reader(pa, opened, earlier) for earlier in range(index)] == rows[:index]
        try:
            reader(pa, opened, index)
        except (pa.ArrowException, OSError) as error:
            if message is not None:
                assert message in str(error)
        else:
            raise AssertionError("PyArrow admitted the damaged selected group")

    def crc_damage(case, index, page):
        frame = frames[index][page]
        edited, (offset, declared, computed) = prior["damaged_outer"](case, frame)
        cause = f"(.page {page} {offset} (.checksum (.mismatch {declared} {computed})))"
        if BRANCHES[index] == "plain":
            return edited, f"(.plain (.plain {cause}))"
        if page == 0:
            return edited, f"(.dictionaryBacked (.chunk {cause}))"
        return edited, f"(.dictionaryBacked (.decode (.snappy {cause})))"

    for index, page, label in ((3, 2, "plain"), (4, 0, "dictionary"), (5, 4, "fallback")):
        damaged, reason = crc_damage(wire, index, page)
        source_refuses(damaged, index, "CRC")
        add(f"mutated_late_{label}_crc", damaged, index, reason)
    bad_plain, reason = crc_damage(wire, 3, 2)
    two, _ = crc_damage(bad_plain, 4, 0)
    source_refuses(two, 3, "CRC")
    add("mutated_two_routes_first_error", two, 3, reason)

    raw_ref = frames[4][1]
    changed, recomputed, _ = dictionary["corrupt_reference"](wire, raw_ref, raw_ref[2] + raw_ref[1][8][1][5][1],
                                                            thrift)
    source_refuses(changed, 4)
    add("mutated_late_reference_with_valid_crc", changed, 4,
        f"(.dictionaryBacked (.decode (.snappy (.page 1 {raw_ref[0]} (.references (.outOfBounds 3))))))")

    reentry, unsupported = frames[5][3:5]
    edit = fallback["edit_v2_header"]
    changed = edit(wire, reentry, {4: 8}, thrift)
    changed = edit(changed, unsupported, {4: 5}, thrift)
    changed, _ = crc_damage(changed, 5, 0)
    add("mutated_reentry_before_later_header_and_dictionary_crc", changed, 5,
        f"(.dictionaryBacked (.sequence (.suffixEncoding 3 {reentry[0]} 8)))")

    changed = edit(wire, raw_ref, {4: 0}, thrift)
    add("mutated_plain_header_selects_fallback", changed, 4,
        f"(.dictionaryBacked (.sequence (.prefixEncoding 1 {raw_ref[0]} 0)))", "fallback")

    footer_start, metadata = footer(wire, thrift)
    group = thrift["list_field"](metadata, 4)[3]
    column = thrift["list_field"](group, 1)[ORDINAL][3][1]
    assert 11 not in column
    column[11] = column[9]
    edited = thrift["encode"](metadata)
    claimed = wire[:footer_start] + edited + struct.pack("<I", len(edited)) + b"PAR1"
    add("mutated_plain_footer_claims_dictionary", claimed, 3,
        f"(.dictionaryBacked (.chunk (.page 1 {frames[3][1][0]} .dataOffset)))", "fallback")

    old = dictionary["produce"](pa, pq, "1.0")
    opened = pq.ParquetFile(pa.BufferReader(old), page_checksum_verification=True)
    assert [reader(pa, opened, i) for i in range(opened.num_row_groups)] == dictionary["GROUPS"]
    column = opened.metadata.row_group(0).column(ORDINAL)
    first_data = list(support["raw_frames"](old, column))[1]
    assert first_data[1][1][1] == 0
    add("genuine_v1_dictionary", old, 0, f"(.dictionaryBacked (.header 1 {first_data[0]} .expectedV2))",
        "dictionaryOnly")
    add("genuine_gzip_v2", sample["produce_mixed"](pa, pq, NAME, True, True, plain_rows),
        0, "(.plain (.plain (.codec 2)))")
    for branch in ("dictionaryOnly", "fallback"):
        add("page_cap_before_" + branch, parents["dictionary"], 0, "(.dictionaryBacked (.chunk (.framing .pageLimit)))",
            branch, "{ page := { maxPages := 0 } }")

    with tempfile.TemporaryDirectory(prefix="parquet-date-snappy-dispatch-v2-") as temporary:
        emitted = run_lean(Path(temporary), wire, groups, rows, controls, format_groups)
    assert emitted.endswith(bytes.fromhex("ffffffff00000000"))
    ipc["observe"](pa, emitted, pa.schema([pa.field(NAME, pa.date32())]), rows)
    seen["case"] = {"assembly": fingerprint(wire), "genuine_parents": expected_pins, "groups": groups,
                    "field": NAME, "ordinal": ORDINAL, "nullable": True, "lean_ipc": fingerprint(emitted)}
    seen["controls"] = {
        label: {"parquet": fingerprint(case), "group": index, "cause": error, "strict_branch": branch,
                "source_limits": caps, "ipc_batch_cap": 0}
        for label, (case, index, error, branch, _, caps) in controls.items()
    }
    seen["controls"]["mutated_late_reference_with_valid_crc"]["recomputed_crc"] = recomputed
    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8"))
    print(f"PASS Snappy V2 DATE assembly from {len(parents)} genuine PyArrow parents, "
          f"{len(groups)} original chunks across three routes, and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
