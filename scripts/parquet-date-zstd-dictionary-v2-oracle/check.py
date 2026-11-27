"""Compare genuine ZSTD V2 dictionary DATE chunks with native Date32 IPC."""

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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Zstd/V2/Tests.lean"
NAME, ORDINAL = "日付", 1
MIN_DAY, MAX_DAY = -(2**31), 2**31 - 1
DICTIONARY_LIMIT = 2**20


def produce(pa, pq, batch, nullable, checksum, groups, *, page_version="2.0", dictionary_limit=DICTIONARY_LIMIT):
    schema = pa.schema([pa.field("plain_int32", pa.int32(), False), pa.field(NAME, pa.date32(), nullable)])
    with pa.BufferOutputStream() as sink:
        with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version,
                              compression={NAME: "ZSTD"}, compression_level={NAME: 3}, use_dictionary=[NAME],
                              write_statistics=False, store_schema=False, write_page_checksum=checksum,
                              dictionary_pagesize_limit=dictionary_limit, write_batch_size=batch,
                              data_page_size=24) as writer:
            for days in groups:
                columns = [pa.array(range(len(days)), type=pa.int32()),
                           pa.array(days, type=pa.int32()).view(pa.date32())]
                writer.write_table(pa.Table.from_arrays(columns, schema=schema))
        return sink.getvalue().to_pybytes()


def inspect(pa, pq, wire, settings, prior, support, flat, fallback, extent):
    batch, nullable, checksum, groups = settings
    thrift, hybrid = support["THRIFT"], support["hybrid"]
    kind = thrift["TType"]
    fingerprint = prior["fingerprint"]
    codec = pa.Codec("zstd")
    file = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert file.schema_arrow[ORDINAL] == pa.field(NAME, pa.date32(), nullable=nullable)
    assert str(file.schema.column(0).logical_type) == "None"
    assert [prior["read_group"](pa, file, NAME, i) for i in range(file.num_row_groups)] == groups
    footer_start, numeric_codecs = flat["numeric_codecs"](wire)
    assert numeric_codecs == [[0, 6] for _ in groups]
    _, footer = fallback["footer"](wire, thrift)
    leaf = thrift["list_field"](footer, 2)[ORDINAL + 1]
    assert leaf[1] == (kind.I32, 1) and leaf[3] == (kind.I32, int(nullable))
    assert leaf[6] == (kind.I32, 6) and leaf[10] == (kind.STRUCT, {6: (kind.STRUCT, {})})

    def stored_observation(frame):
        offset, header, start, stored = frame
        assert len(stored) == header[3][1] and (4 in header) == checksum
        crc = header[4][1] % 2**32 if checksum else None
        if checksum:
            assert crc == zlib.crc32(stored)
        return {"frame": offset, "stored_start": start, "parquet_crc": crc,
                "declared_expanded_size": header[2][1], "stored": fingerprint(stored)}

    def decode_frame(stored, expected):
        assert extent(stored) == len(stored)
        shape = flat["first_block"](stored)
        assert shape["dictionary_field_bytes"] == 0
        plain = codec.decompress(stored, expected).to_pybytes()
        assert len(plain) == expected
        return plain, shape

    observations, originals = [], []
    for index, expected in enumerate(groups):
        column = file.metadata.row_group(index).column(ORDINAL)
        assert column.compression == "ZSTD" and column.num_values == len(expected)
        assert set(column.encodings) == {"PLAIN", "RLE", "RLE_DICTIONARY"}
        dictionary, *frames = support["raw_frames"](wire, column)
        begin = column.dictionary_page_offset
        stop = begin + column.total_compressed_size
        assert 4 <= begin < stop <= footer_start
        assert dictionary[0] == begin and dictionary[1][1][1] == 2
        assert dictionary[2] + len(dictionary[3]) == frames[0][0] == column.data_page_offset
        dict_observation = stored_observation(dictionary)
        expanded, shape = decode_frame(dictionary[3], dictionary[1][2][1])
        entries = [word for word, in struct.iter_unpack("<i", expanded)]
        assert [dictionary[1][7][1][key][1] for key in (1, 2)] == [len(entries), 0]
        assert entries == list(dict.fromkeys(day for day in expected if day is not None))
        dict_observation.update({"expanded": fingerprint(expanded), "zstd_frame": shape, "signed_entries": entries})

        cursor, pages = 0, []
        for frame in frames:
            _, header, _, stored = frame
            assert header[1][1] == 3
            info = header[8][1]
            count, nulls, rows, tag, definitions, repetitions, flag = [info[key][1] for key in range(1, 8)]
            slots = expected[cursor:cursor + count]
            cursor += count
            assert (count, nulls, rows, tag, repetitions) == (batch, slots.count(None), batch, 8, 0)
            assert len(slots) == count and definitions <= min(header[2][1], header[3][1])
            levels, suffix = stored[:definitions], stored[definitions:]
            if nullable:
                assert hybrid(levels, 1, count) == [int(day is not None) for day in slots]
            else:
                assert levels == b"" and nulls == 0
            scalar_size = header[2][1] - definitions
            if flag:
                prepared, shape = decode_frame(suffix, scalar_size)
            else:
                assert header[2][1] == header[3][1]
                prepared, shape = suffix, None
            assert len(prepared) == scalar_size
            width, runs = prepared[0], prepared[1:]
            indices = hybrid(runs, width, count - nulls)
            assert all(i < len(entries) for i in indices)
            assert [entries[i] for i in indices] == [day for day in slots if day is not None]
            pages.append({**stored_observation(frame), "num_values": count, "num_nulls": nulls,
                          "raw_levels": fingerprint(levels), "is_compressed": flag, "stored_suffix": fingerprint(suffix),
                          "index_stream": fingerprint(prepared), "zstd_frame": shape, "index_width": width,
                          "ordered_indices": fingerprint(bytes(indices))})
        assert cursor == len(expected) and len(pages) == 3
        assert frames[-1][2] + len(frames[-1][3]) == stop
        all_pages = [dict_observation, *pages]
        observations.append({"span": [begin, stop], "expanded_total": sum(p["declared_expanded_size"] for p in all_pages),
                             "dictionary": dict_observation, "data": pages})
        originals.append((dictionary, frames))
    return observations, originals


def launch_driver(folder, files, cases, inspected, controls, format_groups, pa, ipc):
    outputs, commands = {}, []

    def input_path(label, wire):
        path = folder / (label + ".parquet")
        path.write_bytes(wire)
        return json.dumps(str(path))

    for label, wire in files.items():
        _, nullable, _, expected = cases[label]
        observed = inspected[label][0]
        all_pages = [[group["dictionary"], *group["data"]] for group in observed]
        spans = [tuple(group["span"]) for group in observed]
        offsets = [[page["frame"] for page in pages] for pages in all_pages]
        crcs = format_groups([[page["parquet_crc"] for page in pages] for pages in all_pages])
        dictionaries = [group["dictionary"]["signed_entries"] for group in observed]
        flags = json.dumps([[page["is_compressed"] for page in group["data"]] for group in observed])
        stored_cap = max(stop - start for start, stop in spans)
        expanded_cap = max(group["expanded_total"] for group in observed)
        source = input_path(label, wire)
        out = folder / (label + ".arrows")
        commands.append(f"#eval (show IO Unit from do\n"
                        f"  let input := Bytes.mk (← IO.FS.readBinFile {source})\n"
                        f"  readBack input {ORDINAL} {json.dumps(NAME, ensure_ascii=False)} "
                        f"{str(nullable).lower()} {format_groups(expected)} {spans} {offsets} {crcs} "
                        f"{dictionaries} {flags} {stored_cap} {expanded_cap} {json.dumps(str(out))}\n"
                        f"  unless plainProfilesRefuse input {ORDINAL} do\n"
                        f'    throw (IO.userError "an existing PLAIN reader admitted {label}"))')
        outputs[label] = (out, pa.schema([pa.field(NAME, pa.date32(), nullable)]), expected)

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
    for label, (path, schema, groups) in outputs.items():
        wire = path.read_bytes()
        ipc["observe"](pa, wire, schema, groups)
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
    support = load("parquet-timestamp-snappy-dictionary-oracle")
    thrift = support["THRIFT"]
    flat = load("parquet-flat-zstd")
    fallback = load("parquet-date-gzip-fallback-oracle")
    fallback_v2 = load("parquet-date-gzip-fallback-v2-oracle")
    gzip_dictionary = load("parquet-date-gzip-dictionary-v2-oracle")
    format_groups = load("parquet-date-selected-leaf-oracle")["lean_groups"]
    ipc = load("arrow-date32-writer-oracle")
    pins = json.loads((ROOT / "scripts/parquet-date-zstd-v1-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain", "frame_extent_libzstd",
                                      "producer_compression_level")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    extent = zstd["frame_extent"]()
    seen["producer"] = {"dictionary_pagesize_limit": DICTIONARY_LIMIT, "data_page_size": 24}

    patterns = ([MIN_DAY, None, -19, MAX_DAY, -19, None, MIN_DAY, MAX_DAY],
                [-719528, MAX_DAY, None, MIN_DAY, MIN_DAY, None, MAX_DAY, -719528])

    def rows(batch, nullable):
        return [[day if nullable or day is not None else 0 for day in pattern] * (batch * 3 // 8)
                for pattern in patterns]

    cases = {"nullable_raw_crc": (64, True, True, rows(64, True)),
             "nullable_zstd_crc": (128, True, True, rows(128, True)),
             "required_zstd_no_crc": (128, False, False, rows(128, False))}
    files = {label: produce(pa, pq, *settings) for label, settings in cases.items()}
    inspected = {label: inspect(pa, pq, files[label], settings, prior, support, flat, fallback, extent)
                 for label, settings in cases.items()}
    for label, (groups, _) in inspected.items():
        assert {p["is_compressed"] for group in groups for p in group["data"]} == {label != "nullable_raw_crc"}

    raw, compressed = files["nullable_raw_crc"], files["nullable_zstd_crc"]
    raw_rows, compressed_rows = cases["nullable_raw_crc"][-1], cases["nullable_zstd_crc"][-1]
    raw_observed, raw_frames = inspected["nullable_raw_crc"]
    compressed_observed, compressed_frames = inspected["nullable_zstd_crc"]
    raw_ref = raw_frames[1][1][-1]
    dictionary, refs = compressed_frames[1]
    compressed_ref = refs[-1]
    controls, repaired = {}, {}
    writer_limit = "{ ipc := { batches := 0 } }"

    def late(label, wire, reason, expected):
        controls[label] = (wire, 1, reason, "{}", writer_limit, expected[:1])

    def page_cause(page, frame, reason):
        return f"(.chunk (.page {page} {frame[0]} {reason}))"

    for label, source, frame, number, expected in (
        ("dictionary", compressed, dictionary, 0, compressed_rows),
        ("raw_levels", raw, raw_ref, 3, raw_rows),
        ("compressed_levels", compressed, compressed_ref, 3, compressed_rows),
    ):
        damaged, (_, declared, computed) = prior["damaged_outer"](source, frame)
        prior["observe_refusal"](pa, pq, damaged, NAME, expected[0], crc=True)
        checksum = f"(.checksum (.mismatch {declared} {computed}))"
        reason = f"(.dictionary {frame[0]} {checksum})" if number == 0 else page_cause(number, frame, checksum)
        late(f"malformed_{label}_stored_crc", damaged, reason, expected)

    def replace_stored(frame, edits):
        for altered in edits:
            try:
                return zstd["replace_stored"](compressed, frame, altered, thrift)
            except AssertionError:
                continue
        raise AssertionError("No edited CRC retained the Compact header extent")

    for label, frame, levels in (("dictionary", dictionary, 0),
                                  ("reference", compressed_ref, compressed_ref[1][8][1][5][1])):
        stored = frame[3]
        # Retain the Compact CRC field width by varying a second magic octet.
        edits = (stored[:levels] + bytes([stored[levels] ^ 1, octet]) + stored[levels + 2:]
                 for octet in range(256))
        damaged, crc = replace_stored(frame, edits)
        altered = damaged[frame[2]:frame[2] + len(stored)]
        assert altered[:levels] == stored[:levels] and extent(altered[levels:]) is None
        prior["observe_refusal"](pa, pq, damaged, NAME, compressed_rows[0], crc=False)
        magic = "(.frame (.frame .badMagic))"
        reason = (f"(.dictionary {frame[0]} (.payload {magic}))" if levels == 0
                  else f"(.preparation 3 {frame[0]} {magic})")
        key = f"malformed_{label}_magic_valid_crc"
        late(key, damaged, reason, compressed_rows)
        repaired[key] = crc

    original = dictionary[3]
    block = int.from_bytes(original[6:9], "little")
    assert original[4] == 0x20 and block & 7 == 1 and block >> 3 == original[5] == len(original) - 9
    trailing = original[:5] + bytes([original[5] - 1]) + (block - 8).to_bytes(3, "little") + original[9:]
    assert extent(trailing) == len(original) - 1
    assert len(pa.Codec("zstd").decompress(trailing[:-1], original[5] - 1)) == original[5] - 1
    edited, crc = replace_stored(dictionary, (trailing[:-1] + bytes([octet]) for octet in range(256)))
    key = "malformed_dictionary_trailing_byte_valid_crc"
    late(key, edited, f"(.dictionary {dictionary[0]} (.payload (.frame (.frame .trailingInput))))", compressed_rows)
    repaired[key] = crc

    info = raw_ref[1][8][1]
    assert len(raw_observed[1]["dictionary"]["signed_entries"]) == 3
    damaged, crc = gzip_dictionary["out_of_bounds"](raw, raw_ref, info[1][1] - info[2][1], support)
    prior["observe_refusal"](pa, pq, damaged, NAME, raw_rows[0], crc=False)
    key = "malformed_reference_index_valid_crc"
    late(key, damaged, page_cause(3, raw_ref, "(.references (.outOfBounds 3))"), raw_rows)
    repaired[key] = crc

    legacy = fallback_v2["edit_header"](raw, raw_ref, {4: (thrift["TType"].I32, 2)}, thrift)
    late("legacy_reference_encoding", legacy, f"(.header 3 {raw_ref[0]} (.encoding 2))", raw_rows)

    example = load("parquet-date-snappy-fallback-oracle")
    fallback_rows = [[MIN_DAY, None] * 192, example["groups"](128)[1]]
    mixed_wire = produce(pa, pq, 128, True, True, fallback_rows, dictionary_limit=8)
    mixed_file = pq.ParquetFile(pa.BufferReader(mixed_wire), page_checksum_verification=True)
    assert [prior["read_group"](pa, mixed_file, NAME, i) for i in range(2)] == fallback_rows
    mixed = [list(support["raw_frames"](mixed_wire, mixed_file.metadata.row_group(i).column(ORDINAL)))[1:]
             for i in range(2)]
    assert [[frame[1][8][1][4][1] for frame in pages] for pages in mixed] == [[8, 8, 8], [8, 0, 0, 0]]
    late("genuine_late_fallback", mixed_wire, f"(.header 2 {mixed[1][1][0]} (.encoding 0))", fallback_rows)

    v1 = produce(pa, pq, *cases["nullable_raw_crc"], page_version="1.0")
    v1_file = pq.ParquetFile(pa.BufferReader(v1), page_checksum_verification=True)
    assert prior["read_group"](pa, v1_file, NAME, 0) == raw_rows[0]
    v1_column = v1_file.metadata.row_group(0).column(ORDINAL)
    first_dictionary, first_refs = raw_frames[0]
    controls.update({
        "genuine_v1_dictionary": (v1, 0, f"(.header 1 {v1_column.data_page_offset} .expectedV2)", "{}", "{}", None),
        "low_entry_cap": (raw, 0, f"(.dictionary {first_dictionary[0]} .entryLimit)", "{ maxEntries := 2 }", "{}", None),
        "low_index_cap": (raw, 0, page_cause(1, first_refs[0], "(.references .indexByteLimit)"),
                          "{ indices := ⟨1048576, 0⟩ }", "{}", None),
        "low_expanded_chunk_cap": (compressed, 0, "(.chunk .expandedChunkLimit)",
                                   f"{{ maxExpandedChunkBytes := {compressed_observed[0]['expanded_total'] - 1} }}", "{}", None),
    })

    with tempfile.TemporaryDirectory(prefix="parquet-date-zstd-dictionary-v2-") as temporary:
        emitted = launch_driver(Path(temporary), files, cases, inspected, controls, format_groups, pa, ipc)
    fingerprint = prior["fingerprint"]
    seen["cases"] = {
        label: {"parquet": fingerprint(files[label]), "field": NAME, "ordinal": ORDINAL, "nullable": nullable,
                "batch": batch, "stored_crc": checksum, "groups": inspected[label][0],
                "lean_ipc": fingerprint(emitted[label])}
        for label, (batch, nullable, checksum, _) in cases.items()
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
    page_count = sum(len(group["data"]) for case in seen["cases"].values() for group in case["groups"])
    print(f"PASS {len(files)} genuine ZSTD V2 DATE dictionary files, {group_count} dictionaries, "
          f"{page_count} reference pages with both flags, and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
