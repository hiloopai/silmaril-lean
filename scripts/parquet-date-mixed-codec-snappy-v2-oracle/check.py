"""Check mixed GZIP, Zstandard and Snappy DATE V2 from genuine PyArrow chunks."""

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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/MixedCodec/V2/WithSnappy/Tests.lean"
NAME, ORDINAL = "日付", 1
ORDER = (("plain", 0), ("snappy_dictionary", 0), ("zstd_plain", 0), ("snappy_plain", 1),
         ("plain", 1), ("snappy_fallback", 0), ("snappy_dictionary", 1), ("snappy_fallback_literal", 1))
PROFILES = ("gzip_plain", "snappy_dictionary", "zstd_plain", "snappy_plain", "gzip_plain",
            "snappy_fallback", "snappy_dictionary", "snappy_fallback")
CODES = [2, 1, 6, 1, 2, 1, 1, 1]


def run_lean(folder, wire, rows, controls, format_groups):
    def save(label, source):
        path = folder / (label + ".parquet")
        path.write_bytes(source)
        return json.dumps(str(path))

    source = save("mixed_codec_assembly", wire)
    out = folder / "mixed_codec_assembly.arrows"
    commands = [f"#eval (show IO Unit from do\n"
                f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                f"  readBack input {ORDINAL} {json.dumps(NAME, ensure_ascii=False)} true "
                f"{format_groups(rows)} {CODES} {{}} {json.dumps(str(out))})"]
    for label, (case, index, code, cause) in controls.items():
        commands.append(f"#eval (show IO Unit from do\n"
                        f"  let input := Bytes.mk (← IO.FS.readBinFile {save(label, case)})\n"
                        f"  assertRejects {json.dumps(label)} input {ORDINAL} {index} {code} {cause} {{}}\n"
                        f"  unless keepsPrefix input {ORDINAL} {index} {format_groups(rows[:index])} {cause} {{}} do\n"
                        f'    throw (IO.userError "{label}: completed prefix differed"))')
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
        return runpy.run_path(str(ROOT / "scripts" / name / "check.py"))

    def pins(name):
        return json.loads((ROOT / "scripts" / name / "fixtures.json").read_text(encoding="utf-8"))

    prior = load("parquet-date-gzip-v1-oracle")
    gzip = load("parquet-date-gzip-v2-oracle")
    zstd = load("parquet-date-zstd-v1-oracle")
    zstd_v2 = load("parquet-date-zstd-v2-oracle")
    snappy = load("parquet-date-snappy-plain-v2-oracle")
    dictionary = load("parquet-date-snappy-dictionary-oracle")
    fallback = load("parquet-date-snappy-fallback-oracle")
    support = load("parquet-timestamp-snappy-dictionary-oracle")
    thrift = support["THRIFT"]
    assembly = load("parquet-date-gzip-plain-dispatch-v2-oracle")
    relocate = load("parquet-timestamp-mixed-groups-oracle")
    footer = load("parquet-date-gzip-fallback-oracle")["footer"]
    flat = load("parquet-flat-zstd")
    selected = load("parquet-date-selected-leaf-oracle")
    read_dictionary_group = load("parquet-date-dictionary-oracle")["read_group"]
    ipc = load("arrow-date32-writer-oracle")
    fingerprint = prior["fingerprint"]
    old_mixed = pins("parquet-date-mixed-codec-v2-oracle")
    old_snappy = pins("parquet-date-snappy-dispatch-v2-oracle")
    seen = {key: old_mixed[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                           "thrift_wheel_sha256", "lean_toolchain", "frame_extent_libzstd")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    extent = zstd["frame_extent"]()
    seen["zlib_runtime"] = zlib.ZLIB_RUNTIME_VERSION
    batch = gzip["BATCH"]
    plain_rows = gzip["mixed_groups"](True)
    source_rows = {"plain": plain_rows, "zstd_plain": plain_rows, "snappy_plain": plain_rows,
                   "snappy_dictionary": dictionary["GROUPS"], "snappy_fallback": fallback["groups"](128),
                   "snappy_fallback_literal": fallback["groups"](32)}
    parents = {
        "plain": gzip["produce_mixed"](pa, pq, NAME, True, True, plain_rows),
        "zstd_plain": zstd["produce"](pa, pq, NAME, True, True, plain_rows, batch, version="2.0"),
        "snappy_plain": snappy["produce"](pa, pq, NAME, True, True, plain_rows, batch),
        "snappy_dictionary": dictionary["produce"](pa, pq, "2.0"),
        "snappy_fallback": fallback["produce"](pa, pq, "2.0", 128, source_rows["snappy_fallback"]),
        "snappy_fallback_literal": fallback["produce"](pa, pq, "2.0", 32, source_rows["snappy_fallback_literal"]),
    }
    captures = {
        "plain": gzip["inspect"](pa, pq, parents["plain"], NAME, True, True, plain_rows,
                                 {True, False}, prior, support),
        "zstd_plain": zstd_v2["inspect"](pa, pq, parents["zstd_plain"], NAME, True, True, plain_rows,
                                        batch, prior, support, flat, extent),
        "snappy_plain": snappy["inspect"](pa, pq, parents["snappy_plain"], NAME, True, True, plain_rows,
                                          prior, support),
        "snappy_dictionary": dictionary["inspect"](pa, pq, parents["snappy_dictionary"], "2.0", True,
                                                    support, read_dictionary_group),
        "snappy_fallback": fallback["inspect"](pa, pq, parents["snappy_fallback"], "2.0", 128,
                                              source_rows["snappy_fallback"], support, read_dictionary_group),
        "snappy_fallback_literal": fallback["inspect"](pa, pq, parents["snappy_fallback_literal"], "2.0", 32,
                                                      source_rows["snappy_fallback_literal"], support,
                                                      read_dictionary_group),
    }
    old_mixed_parents = old_mixed["case"]["genuine_parents"]
    old_snappy_parents = old_snappy["case"]["genuine_parents"]
    expected_pins = {label: old_snappy_parents[label.removeprefix("snappy_")] if label.startswith("snappy_")
                     else old_mixed_parents[label] for label in parents}
    assert {label: fingerprint(wire) for label, wire in parents.items()} == expected_pins

    def observe(frame):
        offset, header, start, stored = frame
        page = {"frame": offset, "stored_start": start, "parquet_crc": header[4][1] % 2**32,
                "stored": fingerprint(stored)}
        if header[1][1] == 3:
            data = header[8][1]
            levels = data[5][1]
            page.update({"tag": data[4][1], "is_compressed": data[7][1], "levels": fingerprint(stored[:levels]),
                         "stored_suffix": fingerprint(stored[levels:])})
        return page

    observations = {}
    for label, (description, original) in captures.items():
        groups = []
        for chunk, frames in zip(description, original, strict=True):
            if label.startswith("snappy_fallback"):
                frames = [frames[0], *frames[1]]
            pages = list(map(observe, frames))
            group = {"span": chunk["span"]}
            if label == "snappy_dictionary" or label.startswith("snappy_fallback"):
                group["dictionary"] = pages.pop(0)
            group["data"] = pages
            groups.append(group)
        observations[label] = groups

    rows = [source_rows[label][index] for label, index in ORDER]
    compression = {label: "SNAPPY" if label.startswith("snappy") else "ZSTD" if label == "zstd_plain" else "GZIP"
                   for label in parents}
    wire, groups = assembly["assemble"](parents, observations, footer, thrift, relocate["column_extent"],
                                         relocate["relocate_offset"], order=ORDER, profiles=PROFILES)
    frames = assembly["inspect_assembly"](pa, pq, wire, parents, observations, groups, rows, True, prior, support,
                                           compression=compression)
    _, actual = flat["numeric_codecs"](wire)
    assert [code[ORDINAL] for code in actual] == CODES and any(code[0] != code[ORDINAL] for code in actual)
    for phase in (0, 8):
        assert {page["is_compressed"] for group in groups if group["profile"] == "snappy_fallback"
                for page in group["data"] if page["tag"] == phase} == {True, False}

    controls = {}

    def add(label, case, index, reason, code=None):
        controls[label] = (case, index, CODES[index] if code is None else code, reason)

    def check_crc_refusal(source, index):
        opened = pq.ParquetFile(pa.BufferReader(source), page_checksum_verification=True)
        assert [prior["read_group"](pa, opened, NAME, i) for i in range(index)] == rows[:index]
        try:
            prior["read_group"](pa, opened, NAME, index)
        except (pa.ArrowException, OSError) as error:
            assert "CRC" in str(error)
        else:
            raise AssertionError("PyArrow admitted a damaged selected chunk")

    def crc_damage(source, index, page):
        changed, (offset, declared, computed) = prior["damaged_outer"](source, frames[index][page])
        mismatch = f"(.mismatch {declared} {computed})"
        reason = f"(.page {page} {offset} (.checksum {mismatch}))"
        match PROFILES[index]:
            case "gzip_plain":
                return changed, f"(.twoCodec (.gzip (.plain (.gzip {reason}))))"
            case "zstd_plain":
                return changed, f"(.twoCodec (.zstd (.plain (.zstd (.checksum {page} {offset} {mismatch})))))"
            case "snappy_plain":
                return changed, f"(.snappy (.plain (.plain {reason})))"
            case "snappy_dictionary":
                assert page == 0
                return changed, f"(.snappy (.dictionaryBacked (.chunk {reason})))"
            case "snappy_fallback":
                assert page > 0
                return changed, f"(.snappy (.dictionaryBacked (.decode (.snappy {reason}))))"
        raise AssertionError("unknown test profile")

    for index, page in ((2, 0), (3, 2), (4, 2), (6, 0), (7, 4)):
        changed, reason = crc_damage(wire, index, page)
        check_crc_refusal(changed, index)
        add("mutated_late_" + PROFILES[index] + "_crc", changed, index, reason)
    first, reason = crc_damage(wire, 3, 2)
    two, _ = crc_damage(first, 4, 2)
    check_crc_refusal(two, 3)
    add("mutated_two_codecs_first_error", two, 3, reason)

    reentry, later = frames[7][3:5]
    changed = fallback["edit_v2_header"](wire, reentry, {4: 8}, thrift)
    changed = fallback["edit_v2_header"](changed, later, {4: 5}, thrift)
    add("mutated_snappy_reentry_before_later_header", changed, 7,
        f"(.snappy (.dictionaryBacked (.sequence (.suffixEncoding 3 {reentry[0]} 8))))")

    def retag(index, new_codec):
        start, metadata = footer(wire, thrift)
        group = thrift["list_field"](metadata, 4)[index]
        column = thrift["list_field"](group, 1)[ORDINAL][3][1]
        assert column[4][1] == CODES[index]
        column[4] = thrift["TType"].I32, new_codec
        edited = thrift["encode"](metadata)
        return wire[:start] + edited + struct.pack("<I", len(edited)) + b"PAR1"

    add("mutated_unknown_footer_codec", retag(6, 77), 6, "(.twoCodec (.unsupportedCodec 77))", 77)
    ordinal, frame = next((index, frame) for index, frame in enumerate(frames[3]) if frame[1][8][1][7][1])
    assert extent(frame[3][frame[1][8][1][5][1]:]) is None
    add("mutated_snappy_body_labelled_zstd", retag(3, 6), 3,
        f"(.twoCodec (.zstd (.plain (.zstd (.decode {ordinal} {frame[0]} (.frame (.frame .badMagic)))))))", 6)

    native_uncompressed = selected["produce"](pa, pq, NAME, True, ORDINAL, "2.0", plain_rows)
    opened = pq.ParquetFile(pa.BufferReader(native_uncompressed))
    assert opened.metadata.row_group(0).column(ORDINAL).compression == "UNCOMPRESSED"
    assert [prior["read_group"](pa, opened, NAME, index) for index in range(opened.num_row_groups)] == plain_rows
    add("genuine_unsupported_uncompressed", native_uncompressed, 0, "(.twoCodec (.unsupportedCodec 0))", 0)

    with tempfile.TemporaryDirectory(prefix="parquet-date-mixed-codec-snappy-v2-") as temporary:
        emitted = run_lean(Path(temporary), wire, rows, controls, selected["lean_groups"])
    assert emitted.endswith(bytes.fromhex("ffffffff00000000"))
    ipc["observe"](pa, emitted, pa.schema([pa.field(NAME, pa.date32())]), rows)
    seen["case"] = {"assembly": fingerprint(wire), "genuine_parents": expected_pins,
                    "field": NAME, "ordinal": ORDINAL, "nullable": True, "codecs": CODES, "groups": groups,
                    "lean_ipc": fingerprint(emitted)}
    seen["controls"] = {label: {"parquet": fingerprint(source), "group": index, "codec": code,
                                 "cause": cause, "ipc_batch_cap": 0}
                        for label, (source, index, code, cause) in controls.items()}
    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8"))
    print(f"PASS mixed GZIP/ZSTD/Snappy V2 DATE assembly from {len(parents)} genuine PyArrow parents, "
          f"{len(groups)} original chunks, and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
