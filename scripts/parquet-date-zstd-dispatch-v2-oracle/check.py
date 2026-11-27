"""Check three ZSTD V2 DATE routes in an assembly of genuine PyArrow chunks."""

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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Zstd/Dispatch/V2/Tests.lean"
NAME, ORDINAL = "日付", 1
MIN_DAY, MAX_DAY = -(2**31), 2**31 - 1
ORDER = tuple((profile, group) for group in range(2) for profile in ("plain", "dictionary", "fallback"))
PROFILES = tuple(profile for profile, _ in ORDER)


def launch_driver(folder, source, observed, rows, controls, format_groups, pa, ipc):
    commands = []

    def input_path(label, wire):
        path = folder / (label + ".parquet")
        path.write_bytes(wire)
        return json.dumps(str(path))

    original = input_path("assembled_nullable_crc", source)
    out = folder / "assembled_nullable_crc.arrows"
    all_pages = [([group["dictionary"]] if "dictionary" in group else []) + group["data"] for group in observed]
    spans = [tuple(group["span"]) for group in observed]
    offsets = [[page["frame"] for page in pages] for pages in all_pages]
    crcs = format_groups([[page["parquet_crc"] for page in pages] for pages in all_pages])
    profiles = "[" + ", ".join("." + profile for profile in PROFILES) + "]"
    flags = json.dumps([[page["is_compressed"] for page in group["data"]] for group in observed])
    stored_cap = max(stop - start for start, stop in spans)
    expanded_cap = max(group["expanded_total"] for group in observed)
    commands.append(f"#eval (show IO Unit from do\n"
                    f"  let input := Bytes.mk (← IO.FS.readBinFile {original})\n"
                    f"  readBack input {ORDINAL} {json.dumps(NAME, ensure_ascii=False)} true "
                    f"{format_groups(rows)} {spans} {offsets} {crcs} {profiles} {flags} "
                    f"{stored_cap} {expanded_cap} {json.dumps(str(out))})")

    for label, (wire, index, reason, route) in controls.items():
        case = input_path(label, wire)
        commands.append(f"#eval (show IO Unit from do\n"
                        f"  let input := Bytes.mk (← IO.FS.readBinFile {case})\n"
                        f"  assertRejects {json.dumps(label)} input {ORDINAL} "
                        f"(.source (.groupFailure {index} {reason})) {{}} {{ ipc := {{ batches := 0 }} }}\n"
                        f"  unless agrees input {ORDINAL} {index} .{route} do\n"
                        f'    throw (IO.userError "{label} differed from its strict route")\n'
                        f"  unless keepsPrefix input {ORDINAL} {index} {format_groups(rows[:index])} {reason} do\n"
                        f'    throw (IO.userError "{label} source prefix differed"))')
    driver = folder / "Oracle.lean"
    driver.write_text(TESTS.read_text(encoding="utf-8") + "\nset_option maxRecDepth 8192\n"
                      + "\n".join(commands) + "\n", encoding="utf-8")
    subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                    "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
    wire = out.read_bytes()
    ipc["observe"](pa, wire, pa.schema([pa.field(NAME, pa.date32())]), rows)
    return wire


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
    sample_plain = load("parquet-date-gzip-v2-oracle")
    sample_fallback = load("parquet-date-snappy-fallback-oracle")
    assembly = load("parquet-date-gzip-plain-dispatch-v2-oracle")
    relocate = load("parquet-timestamp-mixed-groups-oracle")
    support = load("parquet-timestamp-snappy-dictionary-oracle")
    thrift = support["THRIFT"]
    fallback_v2 = load("parquet-date-gzip-fallback-v2-oracle")
    footer = load("parquet-date-gzip-fallback-oracle")["footer"]
    zstd = load("parquet-date-zstd-v1-oracle")
    plain = load("parquet-date-zstd-v2-oracle")
    dictionary = load("parquet-date-zstd-dictionary-v2-oracle")
    flat = load("parquet-flat-zstd")
    format_groups = load("parquet-date-selected-leaf-oracle")["lean_groups"]
    ipc = load("arrow-date32-writer-oracle")
    pins = json.loads((ROOT / "scripts/parquet-date-zstd-fallback-v2-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain", "frame_extent_libzstd",
                                      "producer_compression_level")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    extent = zstd["frame_extent"]()
    fingerprint = prior["fingerprint"]

    plain_batch = sample_plain["BATCH"]
    plain_rows = sample_plain["mixed_groups"](True)
    dictionary_rows = [
        [MIN_DAY, None, -19, MAX_DAY, -19, None, MIN_DAY, MAX_DAY] * 24,
        [-719528, MAX_DAY, None, MIN_DAY, MIN_DAY, None, MAX_DAY, -719528] * 24,
    ]
    lead = [MIN_DAY, None, MAX_DAY, MIN_DAY, None, MAX_DAY, MIN_DAY, MAX_DAY] * 16
    fallback_rows = [lead + group for group in sample_fallback["groups"](128)]
    parents = {
        "plain": zstd["produce"](pa, pq, NAME, True, True, plain_rows, plain_batch, version="2.0"),
        "dictionary": dictionary["produce"](pa, pq, 64, True, True, dictionary_rows),
        "fallback": dictionary["produce"](pa, pq, 128, True, True, fallback_rows, dictionary_limit=12),
    }
    observed = {
        "plain": plain["inspect"](pa, pq, parents["plain"], NAME, True, True, plain_rows,
                                  plain_batch, prior, support, flat, extent)[0],
        "dictionary": dictionary["inspect"](pa, pq, parents["dictionary"], (64, True, True, dictionary_rows),
                                             prior, support, flat, {"footer": footer}, extent)[0],
        "fallback": dictionary["inspect"](pa, pq, parents["fallback"], (128, True, True, fallback_rows),
                                           prior, support, flat, {"footer": footer}, extent, reference_pages=2)[0],
    }
    by_parent = {"plain": plain_rows, "dictionary": dictionary_rows, "fallback": fallback_rows}
    rows = [by_parent[label][group] for label, group in ORDER]
    wire, groups = assembly["assemble"](parents, observed, footer, thrift, relocate["column_extent"],
                                         relocate["relocate_offset"], order=ORDER, profiles=PROFILES)
    frames = assembly["inspect_assembly"](pa, pq, wire, parents, observed, groups, rows, True,
                                           prior, support, compression="ZSTD")
    assert {p["is_compressed"] for group in observed["plain"] for p in group["data"]} == {False, True}
    for tag in (0, 8):
        assert {p["is_compressed"] for group in observed["fallback"] for p in group["data"] if p["tag"] == tag} == {
            False, True}

    controls = {}

    def add(label, case, index, error, route=None):
        controls[label] = (case, index, error, PROFILES[index] if route is None else route)

    def crc_damage(case, index, page):
        frame = frames[index][page]
        edited, (_, declared, computed) = prior["damaged_outer"](case, frame)
        crc = f"(.mismatch {declared} {computed})"
        if PROFILES[index] == "plain":
            error = f"(.plain (.zstd (.checksum {page} {frame[0]} {crc})))"
        elif page == 0:
            error = f"(.dictionaryBacked (.dictionary (.dictionary {frame[0]} (.checksum {crc}))))"
        elif PROFILES[index] == "fallback" and frame[1][8][1][4][1] == 0:
            error = f"(.dictionaryBacked (.plain (.checksum {page} {frame[0]} {crc})))"
        else:
            error = f"(.dictionaryBacked (.dictionary (.chunk (.page {page} {frame[0]} (.checksum {crc})))))"
        return edited, error

    def check_crc_refusal(case, index):
        opened = pq.ParquetFile(pa.BufferReader(case), page_checksum_verification=True)
        assert [prior["read_group"](pa, opened, NAME, earlier) for earlier in range(index)] == rows[:index]
        try:
            prior["read_group"](pa, opened, NAME, index)
        except (pa.ArrowException, OSError) as error:
            assert "CRC" in str(error)
        else:
            raise AssertionError("PyArrow admitted a damaged stored CRC")

    for index, page in ((3, 2), (4, 1), (4, 0), (5, 4)):
        damaged, reason = crc_damage(wire, index, page)
        check_crc_refusal(damaged, index)
        add(f"malformed_{PROFILES[index]}_page_{page}_stored_crc", damaged, index, reason)

    first, first_reason = crc_damage(wire, 3, 2)
    two, _ = crc_damage(first, 4, 1)
    check_crc_refusal(two, 3)
    add("malformed_two_routes_first_error", two, 3, first_reason)

    encoding = thrift["TType"].I32
    reentry_frame = frames[5][4]
    reentry = fallback_v2["edit_header"](wire, reentry_frame, {4: (encoding, 8)}, thrift)
    reentry_cause = f"(.dictionaryBacked (.sequence (.suffixEncoding 4 {reentry_frame[0]} 8)))"
    add("malformed_fallback_reentry", reentry, 5, reentry_cause)
    reentry_and_crc, _ = crc_damage(reentry, 5, 0)
    add("malformed_fallback_reentry_precedes_bad_dictionary", reentry_and_crc, 5, reentry_cause)

    legacy = frames[4][1]
    legacy_wire = fallback_v2["edit_header"](wire, legacy, {4: (encoding, 2)}, thrift)
    add("malformed_dictionary_header", legacy_wire, 4,
        f"(.dictionaryBacked (.dictionary (.header 1 {legacy[0]} (.encoding 2))))")

    footer_start, metadata = footer(wire, thrift)
    group = thrift["list_field"](metadata, 4)[3]
    column = thrift["list_field"](group, 1)[ORDINAL][3][1]
    assert 11 not in column
    column[11] = column[9]
    edited_footer = thrift["encode"](metadata)
    claimed = wire[:footer_start] + edited_footer + struct.pack("<I", len(edited_footer)) + b"PAR1"
    add("malformed_plain_claims_dictionary", claimed, 3,
        f"(.dictionaryBacked (.dictionary (.chunk (.page 1 {frames[3][1][0]} .dataOffset))))", "fallback")

    ordinal, raw = next((index, frame) for index, frame in enumerate(frames[3]) if not frame[1][8][1][7][1])
    assert extent(raw[3][raw[1][8][1][5][1]:]) is None
    wrong_flag = plain["change_flag"](wire, raw, True, thrift)
    add("malformed_plain_raw_suffix_flag_true", wrong_flag, 3,
        f"(.plain (.zstd (.decode {ordinal} {raw[0]} (.frame (.frame .badMagic)))))")

    with tempfile.TemporaryDirectory(prefix="parquet-date-zstd-dispatch-v2-") as temporary:
        emitted = launch_driver(Path(temporary), wire, groups, rows, controls, format_groups, pa, ipc)
    seen["case"] = {"assembly": fingerprint(wire), "genuine_parents": {k: fingerprint(v) for k, v in parents.items()},
                    "field": NAME, "ordinal": ORDINAL, "nullable": True, "groups": groups, "lean_ipc": fingerprint(emitted)}
    seen["controls"] = {
        label: {"parquet": fingerprint(case), "group": index, "cause": error, "strict_route": route, "ipc_batch_cap": 0}
        for label, (case, index, error, route) in controls.items()
    }
    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(seen, indent=2)
    print(f"PASS assembled ZSTD V2 DATE file from {len(parents)} genuine PyArrow parents, "
          f"{len(groups)} groups across three routes, and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
