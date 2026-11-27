"""Read three GZIP DATE V2 profiles in an assembled file of genuine PyArrow chunks."""

import argparse
from copy import deepcopy
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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Gzip/Dispatch/V2/WithPlain/Tests.lean"
NAME, ORDINAL = "日付", 1
MIN_DAY, MAX_DAY = -(2**31), 2**31 - 1
ORDER = (("plain", 0), ("backed", 0), ("backed", 1), ("plain", 1), ("backed", 2))
PROFILES = ("plain", "dictionary", "fallback", "plain", "dictionary")


def assemble(parents, observations, footer, thrift, extent, relocate):
    """Copy the original chunk octets and rebuild absolute footer offsets."""
    types = thrift["TType"]
    footers = {label: footer(wire, thrift)[1] for label, wire in parents.items()}
    base = deepcopy(footers["plain"])
    assert base[2] == footers["backed"][2]
    body = bytearray(b"PAR1")
    output_groups, selected = [], []
    for index, (label, source_index) in enumerate(ORDER):
        wire = parents[label]
        group = deepcopy(thrift["list_field"](footers[label], 4)[source_index])
        group_start = len(body)
        for ordinal, chunk in enumerate(thrift["list_field"](group, 1)):
            column = chunk[3][1]
            assert not (set(chunk) & {1, 4, 5, 6, 7}) and not (set(column) & {10, 14, 15})
            start, stop = extent(column)
            delta = len(body) - start
            original = wire[start:stop]
            body.extend(original)
            assert body[start + delta:stop + delta] == original
            relocate(column, 9, delta)
            if 11 in column:
                relocate(column, 11, delta)
            if chunk[2][1] != 0:
                relocate(chunk, 2, delta)
            if ordinal == ORDINAL:
                obs = deepcopy(observations[label][source_index])
                assert obs["span"] == [start, stop]
                frames = list(obs["data"])
                if "dictionary" in obs:
                    frames.insert(0, obs["dictionary"])
                for frame in frames:
                    frame["frame"] += delta
                    frame["stored_start"] += delta
                obs["span"] = [start + delta, stop + delta]
                obs["source_group"] = [label, source_index]
                obs["profile"] = PROFILES[index]
                selected.append(obs)
        if 5 in group:
            group[5] = types.I64, group_start
        if 7 in group:
            group[7] = types.I16, index
        output_groups.append(group)
    base[3] = types.I64, sum(group[3][1] for group in output_groups)
    base[4] = types.LIST, (types.STRUCT, output_groups)
    base[6] = types.STRING, b"Fixture assembly from PyArrow 26.0.1 V2 DATE chunks"
    encoded = thrift["encode"](base)
    return bytes(body) + encoded + struct.pack("<I", len(encoded)) + b"PAR1", selected


def inspect_assembly(pa, pq, wire, parents, original, observed, expected, nullable, prior, support):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow[ORDINAL] == pa.field(NAME, pa.date32(), nullable=nullable)
    assert [prior["read_group"](pa, parquet, NAME, i) for i in range(parquet.num_row_groups)] == expected
    result = []
    for index, group in enumerate(observed):
        label, source_index = group["source_group"]
        start, stop = group["span"]
        original_start, original_stop = original[label][source_index]["span"]
        assert wire[start:stop] == parents[label][original_start:original_stop]
        column = parquet.metadata.row_group(index).column(ORDINAL)
        assert column.compression == "GZIP" and column.total_compressed_size == stop - start
        if label == "plain":
            assert column.dictionary_page_offset is None and column.data_page_offset == start
            frames = list(prior["frames"](wire, column, support["THRIFT"]))
        else:
            assert column.dictionary_page_offset == start
            frames = list(support["raw_frames"](wire, column))
        pinned = list(group["data"])
        if "dictionary" in group:
            pinned.insert(0, group["dictionary"])
        for frame, pin in zip(frames, pinned, strict=True):
            offset, header, payload, stored = frame
            assert offset == pin["frame"] and payload == pin["stored_start"]
            assert prior["fingerprint"](stored) == pin["stored"]
            assert (header[4][1] % 2**32 if 4 in header else None) == pin["parquet_crc"]
            if 4 in header:
                assert zlib.crc32(stored) == pin["parquet_crc"]
        result.append(frames)
    return result


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
        return runpy.run_path(str(ROOT / f"scripts/{name}-oracle/check.py"))

    support = load("parquet-timestamp-snappy-dictionary")
    thrift = support["THRIFT"]
    assembly = load("parquet-timestamp-mixed-groups")
    prior = load("parquet-date-gzip-v1")
    plain = load("parquet-date-gzip-v2")
    fallback = load("parquet-date-gzip-fallback")
    v2 = load("parquet-date-gzip-fallback-v2")
    sample = load("parquet-date-snappy-fallback")
    format_groups = load("parquet-date-selected-leaf")["lean_groups"]
    ipc = load("arrow-date32-writer")
    pins = json.loads((ROOT / "scripts/parquet-date-gzip-dispatch-v2-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    seen["producer"] = {"zlib_runtime": zlib.ZLIB_RUNTIME_VERSION, "plain_batch_size": plain["BATCH"],
                        "plain_seed": plain["SEED"], "dictionary_seed": sample["SEED"],
                        "dictionary_pagesize_limit": 8}
    fingerprint = prior["fingerprint"]
    files, cases = {}, {}
    for label, batch, nullable, checksum in (("assembled_nullable_crc", 128, True, True),
                                             ("assembled_required_no_crc", 128, False, False)):
        plain_rows = plain["mixed_groups"](nullable)
        dictionary_rows = [[MIN_DAY, None if nullable else MIN_DAY] * (batch * 3 // 2),
                           [x if nullable or x is not None else 0 for x in sample["groups"](batch)[1]],
                           [None if nullable else MAX_DAY, MAX_DAY] * batch]
        parents = {"plain": plain["produce_mixed"](pa, pq, NAME, nullable, checksum, plain_rows),
                   "backed": fallback["produce"](pa, pq, batch, nullable, checksum, dictionary_rows, page_version="2.0")}
        plain_obs, _ = plain["inspect"](pa, pq, parents["plain"], NAME, nullable, checksum, plain_rows,
                                       {False, True}, prior, support)
        dictionary_obs, _ = v2["inspect"](pa, pq, parents["backed"], (batch, nullable, checksum, dictionary_rows),
                                          support, prior, fallback, dictionary_groups=(0, 2))
        original = {"plain": plain_obs, "backed": dictionary_obs}
        wire, observed = assemble(parents, original, fallback["footer"], thrift, assembly["column_extent"],
                                  assembly["relocate_offset"])
        by_parent = {"plain": plain_rows, "backed": dictionary_rows}
        expected = [by_parent[parent][index] for parent, index in ORDER]
        frames = inspect_assembly(pa, pq, wire, parents, original, observed, expected, nullable, prior, support)
        files[label] = wire
        cases[label] = {"parents": {name: fingerprint(data) for name, data in parents.items()}, "groups": observed,
                        "frames": frames, "expected": expected, "nullable": nullable, "batch": batch}

    source = files["assembled_nullable_crc"]
    case = cases["assembled_nullable_crc"]
    expected, frames = case["expected"], case["frames"]
    controls, prefixes = {}, []
    zero_writer = "{ ipc := { batches := 0 } }"

    def source_error(index, cause):
        return f"(.source (.groupFailure {index} {cause}))"

    def late_control(label, damaged, index, cause):
        controls[label] = (damaged, source_error(index, cause), "{}", zero_writer)
        prefixes.append((label, index, cause))

    def outer_damage(wire, index, ordinal):
        frame = frames[index][ordinal]
        damaged, (offset, declared, computed) = prior["damaged_outer"](wire, frame)
        page = f"(.page {ordinal} {offset} (.checksum (.mismatch {declared} {computed})))"
        cause = f"(.plain (.gzip {page}))" if PROFILES[index] == "plain" else f"(.dictionaryBacked (.chunk {page}))"
        return damaged, cause

    def compare_crc_refusal(wire, index):
        opened = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
        assert [prior["read_group"](pa, opened, NAME, earlier) for earlier in range(index)] == expected[:index]
        try:
            prior["read_group"](pa, opened, NAME, index)
        except (pa.ArrowException, OSError) as error:
            assert "CRC" in str(error)
        else:
            raise AssertionError("PyArrow admitted a damaged stored CRC")

    for index, ordinal in ((2, 2), (3, 0), (4, 1)):
        damaged, cause = outer_damage(source, index, ordinal)
        compare_crc_refusal(damaged, index)
        late_control(f"malformed_{PROFILES[index]}_stored_crc", damaged, index, cause)
    first, first_cause = outer_damage(source, 2, 2)
    two, later_cause = outer_damage(first, 3, 0)
    compare_crc_refusal(two, 2)
    late_control("malformed_two_routes_first_failure", two, 2, first_cause)

    ordinal, raw_plain = next((i, page) for i, page in enumerate(frames[3]) if not page[1][8][1][7][1])
    assert raw_plain[1][8][1][5][1] > 0
    wrong_flag = v2["edit_header"](source, raw_plain, {7: (thrift["TType"].BOOL, True)}, thrift)
    cause = f"(.plain (.gzip (.page {ordinal} {raw_plain[0]} (.scalar (.payload (.malformed .gzip))))))"
    late_control("malformed_plain_raw_suffix_flag_true", wrong_flag, 3, cause)

    start, footer = fallback["footer"](source, thrift)
    group = thrift["list_field"](footer, 4)[3]
    column = thrift["list_field"](group, 1)[ORDINAL][3][1]
    assert 11 not in column
    column[11] = column[9]
    edited_footer = thrift["encode"](footer)
    claimed = source[:start] + edited_footer + struct.pack("<I", len(edited_footer)) + b"PAR1"
    late_control("malformed_plain_claims_dictionary", claimed, 3,
                 f"(.dictionaryBacked (.chunk (.page 1 {frames[3][1][0]} .dataOffset)))")

    reverted = frames[2][3]
    reentry = v2["edit_header"](source, reverted, {4: (thrift["TType"].I32, 8)}, thrift)
    late_control("malformed_fallback_reentry", reentry, 2,
                 f"(.dictionaryBacked (.sequence (.suffixEncoding 3 {reverted[0]} 8)))")

    first_group = case["groups"][0]
    controls["low_stored_chunk_cap"] = (
        source, source_error(0, "(.plain (.gzip .storedChunkLimit))"),
        f"{{ maxChunkBytes := {first_group['span'][1] - first_group['span'][0] - 1} }}", "{}")

    seen["cases"], seen["controls"] = {}, {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-gzip-plain-dispatch-v2-") as temporary:
        folder = Path(temporary)
        outputs, commands, inputs = {}, [], {}

        def input_path(label, wire):
            path = folder / (label + ".parquet")
            path.write_bytes(wire)
            inputs[label] = json.dumps(str(path))
            return inputs[label]

        profile_list = "[" + ", ".join("." + name for name in PROFILES) + "]"
        for label, wire in files.items():
            fixture = cases[label]
            nullable, groups, slots = fixture["nullable"], fixture["groups"], fixture["expected"]
            frames_all = [([group["dictionary"]] if "dictionary" in group else []) + group["data"] for group in groups]
            spans = [tuple(group["span"]) for group in groups]
            offsets = [[page["frame"] for page in pages] for pages in frames_all]
            crcs = format_groups([[page["parquet_crc"] for page in pages] for pages in frames_all])
            flags = json.dumps([[page["is_compressed"] for page in group["data"]] for group in groups])
            stored_cap = max(stop - start for start, stop in spans)
            expanded_cap = max(group["expanded_total"] for group in groups)
            path = folder / (label + ".arrows")
            parquet_path = input_path(label, wire)
            commands.append(f"#eval (show IO Unit from do\n"
                            f"  let input := Bytes.mk (← IO.FS.readBinFile {parquet_path})\n"
                            f"  readBack input {ORDINAL} {json.dumps(NAME, ensure_ascii=False)} "
                            f"{str(nullable).lower()} {format_groups(slots)} "
                            f"{spans} {offsets} {crcs} {profile_list} {flags} {stored_cap} {expanded_cap} "
                            f"{json.dumps(str(path))})")
            seen["cases"][label] = {"assembly": fingerprint(wire), "pyarrow_parents": fixture["parents"],
                                    "nullable": nullable, "dictionary_batch_size": fixture["batch"],
                                    "field": NAME, "selected_ordinal": ORDINAL, "groups": groups}
            outputs[label] = (path, pa.schema([pa.field(NAME, pa.date32(), nullable=nullable)]), slots)
        for label, (wire, error, limits, output) in controls.items():
            parquet_path = input_path(label, wire)
            commands.append(f"#eval (show IO Unit from do\n"
                            f"  let input := Bytes.mk (← IO.FS.readBinFile {parquet_path})\n"
                            f"  assertRejects {json.dumps(label)} input {ORDINAL} {error} {limits} {output})")
            seen["controls"][label] = {"parquet": fingerprint(wire), "error": error,
                                       "source_limits": limits, "output_limits": output}
        for label, index, cause in prefixes:
            commands.append(f"#eval (show IO Unit from do\n"
                            f"  let input := Bytes.mk (← IO.FS.readBinFile {inputs[label]})\n"
                            f"  unless keepsPrefix input {ORDINAL} {index} {format_groups(expected[:index])} {cause} do\n"
                            f'    throw (IO.userError "{label} prefix differed"))')
        commands.append(f"#eval (show IO Unit from do\n"
                        f"  let input := Bytes.mk (← IO.FS.readBinFile {inputs['malformed_two_routes_first_failure']})\n"
                        f"  let .ok bound := Date.Leaf.openLeaf {{}} input {ORDINAL} | throw (IO.userError \"open failed\")\n"
                        f"  match Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup {{}} bound 3 with\n"
                        f"  | .error cause => unless cause == {later_cause} do throw (IO.userError \"later cause differed\")\n"
                        f"  | .ok _ => throw (IO.userError \"later group unexpectedly succeeded\"))")
        driver = folder / "Oracle.lean"
        driver.write_text(TESTS.read_text(encoding="utf-8") + "\nset_option maxRecDepth 4096\n"
                          + "\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
        for label, (path, schema, slots) in outputs.items():
            wire = path.read_bytes()
            ipc["observe"](pa, wire, schema, slots)
            seen["cases"][label]["lean_ipc"] = fingerprint(wire)

    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8"))
    print(f"PASS {len(files)} mixed-profile V2 GZIP DATE assemblies from PyArrow chunks, "
          f"{len(files) * len(ORDER)} selected groups and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
