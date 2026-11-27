"""Check mixed-codec V2 DATE from an assembly of genuine PyArrow chunks."""

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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/MixedCodec/V2/Tests.lean"
NAME, ORDINAL = "日付", 1
MIN_DAY, MAX_DAY = -(2**31), 2**31 - 1
ORDER = (("plain", 0), ("zstd_dictionary", 0), ("gzip_fallback", 0),
         ("zstd_plain", 1), ("gzip_dictionary", 1), ("zstd_fallback", 1))
PROFILES = ("gzip_plain", "zstd_dictionary", "gzip_fallback", "zstd_plain", "gzip_dictionary", "zstd_fallback")
CODECS = [2, 6, 2, 6, 2, 6]


def launch_driver(folder, wire, rows, controls, format_groups, pa, ipc):
    commands = []

    def input_path(label, source):
        path = folder / (label + ".parquet")
        path.write_bytes(source)
        return json.dumps(str(path))

    source = input_path("assembled_mixed_codecs", wire)
    out = folder / "assembled_mixed_codecs.arrows"
    commands.append(f"#eval (show IO Unit from do\n"
                    f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                    f"  readBack input {ORDINAL} {json.dumps(NAME, ensure_ascii=False)} true "
                    f"{format_groups(rows)} {CODECS} {{}} {json.dumps(str(out))})")
    for label, (case, index, code, cause) in controls.items():
        source = input_path(label, case)
        commands.append(f"#eval (show IO Unit from do\n"
                        f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                        f"  assertRejects {json.dumps(label)} input {ORDINAL} {index} {code} {cause} {{}}\n"
                        f"  unless keepsPrefix input {ORDINAL} {index} {format_groups(rows[:index])} {cause} {{}} do\n"
                        f'    throw (IO.userError "{label}: source prefix differed"))')
    driver = folder / "Oracle.lean"
    driver.write_text(TESTS.read_text(encoding="utf-8") + "\nset_option maxRecDepth 8192\n"
                      + "\n".join(commands) + "\n", encoding="utf-8")
    subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                    "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
    emitted = out.read_bytes()
    assert emitted.endswith(bytes.fromhex("ffffffff00000000"))
    ipc["observe"](pa, emitted, pa.schema([pa.field(NAME, pa.date32())]), rows)
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
    gzip_plain = load("parquet-date-gzip-v2-oracle")
    gzip_fallback = load("parquet-date-gzip-fallback-oracle")
    gzip_backed = load("parquet-date-gzip-fallback-v2-oracle")
    zstd = load("parquet-date-zstd-v1-oracle")
    zstd_plain = load("parquet-date-zstd-v2-oracle")
    zstd_backed = load("parquet-date-zstd-dictionary-v2-oracle")
    snappy = load("parquet-date-snappy-fallback-oracle")
    assembly = load("parquet-date-gzip-plain-dispatch-v2-oracle")
    relocation = load("parquet-timestamp-mixed-groups-oracle")
    support = load("parquet-timestamp-snappy-dictionary-oracle")
    thrift = support["THRIFT"]
    footer = gzip_fallback["footer"]
    flat = load("parquet-flat-zstd")
    format_groups = load("parquet-date-selected-leaf-oracle")["lean_groups"]
    ipc = load("arrow-date32-writer-oracle")
    pins = json.loads((ROOT / "scripts/parquet-date-zstd-dispatch-v2-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain", "frame_extent_libzstd",
                                      "producer_compression_level")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    seen["zlib_runtime"] = zlib.ZLIB_RUNTIME_VERSION
    extent = zstd["frame_extent"]()
    fingerprint = prior["fingerprint"]
    read_group = prior["read_group"]

    plain_rows = gzip_plain["mixed_groups"](True)
    pattern = ([MIN_DAY, None, -19, MAX_DAY, -19, None, MIN_DAY, MAX_DAY],
               [-719528, MAX_DAY, None, MIN_DAY, MIN_DAY, None, MAX_DAY, -719528])
    gzip_dictionary_rows = [rows * 48 for rows in pattern]
    zstd_dictionary_rows = [rows * 24 for rows in pattern]
    fallback_rows = snappy["groups"](128)
    lead = [MIN_DAY, None, MAX_DAY, MIN_DAY, None, MAX_DAY, MIN_DAY, MAX_DAY] * 16
    zstd_fallback_rows = [lead + group for group in fallback_rows]
    rows = {"plain": plain_rows, "gzip_dictionary": gzip_dictionary_rows, "gzip_fallback": fallback_rows,
            "zstd_plain": plain_rows, "zstd_dictionary": zstd_dictionary_rows, "zstd_fallback": zstd_fallback_rows}
    parents = {
        "plain": gzip_plain["produce_mixed"](pa, pq, NAME, True, True, plain_rows),
        "gzip_dictionary": gzip_fallback["produce"](pa, pq, 128, True, True, gzip_dictionary_rows,
                                                     page_version="2.0", dictionary_limit=2**20),
        "gzip_fallback": gzip_fallback["produce"](pa, pq, 128, True, True, fallback_rows,
                                                   page_version="2.0", dictionary_limit=8),
        "zstd_plain": zstd["produce"](pa, pq, NAME, True, True, plain_rows, gzip_plain["BATCH"], version="2.0"),
        "zstd_dictionary": zstd_backed["produce"](pa, pq, 64, True, True, zstd_dictionary_rows),
        "zstd_fallback": zstd_backed["produce"](pa, pq, 128, True, True, zstd_fallback_rows, dictionary_limit=12),
    }
    observations = {
        "plain": gzip_plain["inspect"](pa, pq, parents["plain"], NAME, True, True, plain_rows,
                                       {False, True}, prior, support)[0],
        "gzip_dictionary": gzip_backed["inspect"](pa, pq, parents["gzip_dictionary"],
                                                    (128, True, True, gzip_dictionary_rows), support,
                                                    prior, gzip_fallback, dictionary_groups=(0, 1))[0],
        "gzip_fallback": gzip_backed["inspect"](pa, pq, parents["gzip_fallback"], (128, True, True, fallback_rows),
                                                  support, prior, gzip_fallback)[0],
        "zstd_plain": zstd_plain["inspect"](pa, pq, parents["zstd_plain"], NAME, True, True, plain_rows,
                                             gzip_plain["BATCH"], prior, support, flat, extent)[0],
        "zstd_dictionary": zstd_backed["inspect"](pa, pq, parents["zstd_dictionary"], (64, True, True, zstd_dictionary_rows),
                                                   prior, support, flat, gzip_fallback, extent)[0],
        "zstd_fallback": zstd_backed["inspect"](pa, pq, parents["zstd_fallback"], (128, True, True, zstd_fallback_rows),
                                                 prior, support, flat, gzip_fallback, extent, reference_pages=2)[0],
    }
    compression = {label: "ZSTD" if label.startswith("zstd_") else "GZIP" for label in parents}

    def assemble(order, profiles, expected):
        wire, groups = assembly["assemble"](parents, observations, footer, thrift, relocation["column_extent"],
                                             relocation["relocate_offset"], order=order, profiles=profiles)
        frames = assembly["inspect_assembly"](pa, pq, wire, parents, observations, groups, expected, True,
                                               prior, support, compression=compression)
        _, codes = flat["numeric_codecs"](wire)
        assert [code[ORDINAL] for code in codes] == CODECS + ([1] if len(order) > len(ORDER) else [])
        assert any(row[0] != row[ORDINAL] for row in codes)
        return wire, groups, frames

    expected = [rows[label][group] for label, group in ORDER]
    wire, groups, frames = assemble(ORDER, PROFILES, expected)
    for index in (0, 2, 3, 5):
        assert {page["is_compressed"] for page in groups[index]["data"]} == {False, True}
    controls = {}

    def add(label, case, index, cause, code=None):
        controls[label] = (case, index, CODECS[index] if code is None else code, cause)

    def check_crc_refusal(source, index):
        opened = pq.ParquetFile(pa.BufferReader(source), page_checksum_verification=True)
        assert [read_group(pa, opened, NAME, earlier) for earlier in range(index)] == expected[:index]
        try:
            read_group(pa, opened, NAME, index)
        except (pa.ArrowException, OSError) as error:
            assert "CRC" in str(error)
        else:
            raise AssertionError("PyArrow admitted a damaged stored CRC")

    gzip_frame = frames[2][2]
    bad_gzip, (offset, declared, computed) = prior["damaged_outer"](wire, gzip_frame)
    gzip_error = f"(.gzip (.dictionaryBacked (.chunk (.page 2 {offset} (.checksum (.mismatch {declared} {computed}))))))"
    check_crc_refusal(bad_gzip, 2)
    add("malformed_gzip_fallback_crc", bad_gzip, 2, gzip_error)

    zstd_frame = frames[5][4]
    bad_zstd, (offset, declared, computed) = prior["damaged_outer"](wire, zstd_frame)
    zstd_error = f"(.zstd (.dictionaryBacked (.plain (.checksum 4 {offset} (.mismatch {declared} {computed})))))"
    check_crc_refusal(bad_zstd, 5)
    add("malformed_zstd_fallback_crc", bad_zstd, 5, zstd_error)

    both, _ = prior["damaged_outer"](bad_gzip, zstd_frame)
    check_crc_refusal(both, 2)
    add("malformed_both_codecs_first_failure", both, 2, gzip_error)

    def retag(index, codec):
        start, meta = footer(wire, thrift)
        row_group = thrift["list_field"](meta, 4)[index]
        column = thrift["list_field"](row_group, 1)[ORDINAL][3][1]
        assert column[4][1] == CODECS[index]
        column[4] = thrift["TType"].I32, codec
        encoded = thrift["encode"](meta)
        return wire[:start] + encoded + struct.pack("<I", len(encoded)) + b"PAR1"

    add("synthetic_unknown_footer_codec", retag(4, 77), 4, "(.unsupportedCodec 77)", 77)

    mislabelled = retag(0, 6)
    first, frame = next((index, frame) for index, frame in enumerate(frames[0]) if frame[1][8][1][7][1])
    definitions = frame[1][8][1][5][1]
    assert extent(frame[3][definitions:]) is None
    add("synthetic_gzip_body_labelled_zstd", mislabelled, 0,
        f"(.zstd (.plain (.zstd (.decode {first} {frame[0]} (.frame (.frame .badMagic))))))", 6)

    # Add a genuine Snappy chunk after six supported groups. The standalone
    # Snappy producer is verified before this separate test assembly.
    parents["snappy"] = snappy["produce"](pa, pq, "2.0", 128, fallback_rows)
    compression["snappy"] = "SNAPPY"
    snappy_obs, snappy_frames = snappy["inspect"](pa, pq, parents["snappy"], "2.0", 128, fallback_rows, support,
                                                  lambda pa, opened, i: read_group(pa, opened, NAME, i))

    def observe_frame(frame):
        offset, header, start, stored = frame
        return {"frame": offset, "stored_start": start, "parquet_crc": header[4][1] % 2**32,
                "stored": fingerprint(stored)}

    observations["snappy"] = [
        {"span": group["span"], "dictionary": observe_frame(original[0]),
         "data": [observe_frame(page) for page in original[1]]}
        for group, original in zip(snappy_obs, snappy_frames, strict=True)
    ]
    tail, tail_groups, tail_frames = assemble(ORDER + (("snappy", 0),), PROFILES + ("snappy_fallback",),
                                               expected + [fallback_rows[0]])
    add("assembled_late_unsupported_snappy", tail, 6, "(.unsupportedCodec 1)", 1)
    damaged, _ = prior["damaged_outer"](tail, tail_frames[-1][1])
    check_crc_refusal(damaged, 6)
    add("malformed_unsupported_snappy_crc", damaged, 6, "(.unsupportedCodec 1)", 1)

    with tempfile.TemporaryDirectory(prefix="parquet-date-mixed-codec-v2-") as temporary:
        emitted = launch_driver(Path(temporary), wire, expected, controls, format_groups, pa, ipc)
    seen["case"] = {"assembly": fingerprint(wire), "genuine_parents": {label: fingerprint(parents[label])
                     for label, _ in ORDER}, "field": NAME, "ordinal": ORDINAL, "nullable": True,
                    "codecs": CODECS, "groups": groups, "lean_ipc": fingerprint(emitted)}
    seen["unsupported_snappy"] = {"genuine_parent": fingerprint(parents["snappy"]), "group": tail_groups[-1]}
    seen["controls"] = {label: {"parquet": fingerprint(case), "group": index, "codec": code,
                                 "cause": cause, "ipc_batch_cap": 0}
                        for label, (case, index, code, cause) in controls.items()}
    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(seen, indent=2)
    print(f"PASS mixed GZIP/ZSTD V2 DATE assembly from {len(ORDER)} genuine PyArrow parents, "
          f"{len(groups)} groups across six routes, and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
