"""Check genuine PyArrow GZIP V1 DATE fallback and native Date32 IPC readback."""

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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Fallback/Gzip/Tests.lean"
NAME, ORDINAL = "日付", 1


def produce(pa, pq, batch, nullable, checksum, groups, *, page_version="1.0", dictionary_limit=8):
    schema = pa.schema([pa.field("plain_int32", pa.int32(), False), pa.field(NAME, pa.date32(), nullable)])
    with pa.BufferOutputStream() as sink:
        with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version,
                              compression="GZIP", use_dictionary=[NAME], write_statistics=False,
                              store_schema=False, write_page_checksum=checksum,
                              dictionary_pagesize_limit=dictionary_limit, write_batch_size=batch,
                              data_page_size=24) as writer:
            for days in groups:
                columns = [pa.array([i % 4 for i in range(len(days))], type=pa.int32()),
                           pa.array(days, type=pa.int32()).view(pa.date32())]
                writer.write_table(pa.Table.from_arrays(columns, schema=schema))
        return sink.getvalue().to_pybytes()


def footer(wire, thrift):
    size = struct.unpack_from("<I", wire, len(wire) - 8)[0]
    start = len(wire) - size - 8
    memory = thrift["TMemoryBuffer"](wire[start:-8])
    return start, thrift["read_struct"](thrift["TCompactProtocol"](memory))


def inspect(pa, pq, wire, batch, nullable, checksum, rows, support, prior, *, dictionary_only=False):
    thrift, hybrid = support["THRIFT"], support["hybrid"]
    gzip_member, fingerprint, read_group = [prior[name] for name in ("gzip_member", "fingerprint", "read_group")]
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow[ORDINAL] == pa.field(NAME, pa.date32(), nullable=nullable)
    assert str(parquet.schema.column(0).logical_type) == "None"
    assert [read_group(pa, parquet, NAME, i) for i in range(parquet.num_row_groups)] == rows
    _, meta = footer(wire, thrift)
    kind = thrift["TType"]
    leaf = thrift["list_field"](meta, 2)[ORDINAL + 1]
    assert leaf[1] == (kind.I32, 1) and leaf[3] == (kind.I32, int(nullable))
    assert leaf[6] == (kind.I32, 6) and leaf[10] == (kind.STRUCT, {6: (kind.STRUCT, {})})

    def member(frame):
        offset, header, start, stored = frame
        assert (4 in header) == checksum
        outer = header[4][1] % 2**32 if checksum else None
        if checksum:
            assert outer == zlib.crc32(stored)
        expanded, inner = gzip_member(stored)
        assert len(stored) == header[3][1] and len(expanded) == header[2][1]
        return expanded, {"frame": offset, "stored_start": start, "parquet_crc": outer, "member_crc": inner,
                          "stored": fingerprint(stored), "expanded": fingerprint(expanded)}

    checked, originals = [], []
    for index, expected in enumerate(rows):
        column = parquet.metadata.row_group(index).column(ORDINAL)
        assert column.compression == "GZIP" and column.num_values == len(expected)
        assert set(column.encodings) == {"PLAIN", "RLE", "RLE_DICTIONARY"}
        dictionary, *pages = support["raw_frames"](wire, column)
        expanded, dict_obs = member(dictionary)
        entries = [word for word, in struct.iter_unpack("<i", expanded)]
        assert dictionary[0] == column.dictionary_page_offset
        assert dictionary[1][1][1] == 2
        assert [dictionary[1][7][1][field][1] for field in (1, 2)] == [len(entries), 0]
        dictionary_rows = expected if dictionary_only else expected[:batch]
        assert entries == list(dict.fromkeys(day for day in dictionary_rows if day is not None))
        assert pages[0][0] == column.data_page_offset == dictionary[2] + len(dictionary[3])
        cursor, observations = 0, []
        for frame in pages:
            assert frame[1][1][1] == 0
            info = frame[1][5][1]
            count, tag, definitions, repetitions = [info[field][1] for field in (1, 2, 3, 4)]
            assert (count, definitions, repetitions) == (batch, 3, 3)
            slots = expected[cursor:cursor + count]
            cursor += count
            expanded, page = member(frame)
            if nullable:
                size = struct.unpack_from("<I", expanded)[0]
                assert hybrid(expanded[4:4 + size], 1, count) == [int(x is not None) for x in slots]
                values = expanded[4 + size:]
            else:
                values = expanded
            present = [day for day in slots if day is not None]
            if tag == 8:
                indices = hybrid(values[1:], values[0], len(present))
                assert [entries[i] for i in indices] == present
            else:
                assert tag == 0
                assert [word for word, in struct.iter_unpack("<i", values)] == present
            observations.append({**page, "tag": tag, "rows": count, "nulls": slots.count(None),
                                 "scalar_bytes": fingerprint(values)})
        tags = [page["tag"] for page in observations]
        assert cursor == len(expected) and tags
        assert tags == ([8] * len(tags) if dictionary_only else [8, 0, 0, 0])
        stop = dictionary[0] + column.total_compressed_size
        assert pages[-1][2] + len(pages[-1][3]) == stop
        checked.append({"span": [dictionary[0], stop], "dictionary": {**dict_obs, "signed_entries": entries},
                        "expanded_total": len(entries) * 4 + sum(p["expanded"]["bytes"] for p in observations),
                        "data": observations})
        originals.append((dictionary, pages))
    return checked, originals


def edit_encoding(wire, frame, tag, thrift):
    offset, header, payload, _ = frame
    struct_kind, data = header[5]
    edited = thrift["encode"]({**header, 5: (struct_kind, {**data, 2: (thrift["TType"].I32, tag)})})
    assert len(edited) == payload - offset
    return wire[:offset] + edited + wire[payload:]


def append_member(wire, last, thrift, *, level_bytes=0):
    """Add a second empty member to the final page and update all stored extents."""
    offset, header, payload, stored = last
    start, meta = footer(wire, thrift)
    assert payload + len(stored) == start
    compressor = zlib.compressobj(wbits=31)
    extra = compressor.flush()
    edited = stored + extra
    check = zlib.decompressobj(wbits=31)
    assert check.decompress(edited[level_bytes:]) == zlib.decompress(stored[level_bytes:], wbits=31)
    assert check.eof and check.unused_data == extra and zlib.decompress(extra, wbits=31) == b""
    crc = zlib.crc32(edited)
    types = thrift["TType"]
    new_header = thrift["encode"]({**header, 3: (types.I32, len(edited)),
                                  4: (types.I32, crc if crc < 2**31 else crc - 2**32)})
    delta = len(new_header) + len(edited) - (start - offset)
    group = thrift["list_field"](meta, 4)[-1]
    column = thrift["list_field"](group, 1)[ORDINAL][3][1]
    column[7] = (types.I64, column[7][1] + delta)
    group[6] = (types.I64, group[6][1] + delta)
    updated = thrift["encode"](meta)
    return wire[:offset] + new_header + edited + updated + struct.pack("<I", len(updated)) + b"PAR1"


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
    sample = runpy.run_path(str(ROOT / "scripts/parquet-date-snappy-fallback-oracle/check.py"))
    format_groups = runpy.run_path(str(ROOT / "scripts/parquet-date-selected-leaf-oracle/check.py"))["lean_groups"]
    lean_bytes = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))["lean_bytes"]
    ipc = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    pins = json.loads((ROOT / "scripts/parquet-date-gzip-v1-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    seen["producer"] = {"seed": sample["SEED"], "dictionary_pagesize_limit": 8, "data_page_size": 24,
                        "zlib_runtime": zlib.ZLIB_RUNTIME_VERSION}

    optional = sample["groups"](128)
    required = [[0 if day is None else day for day in group] for group in sample["groups"](32)]
    cases = {"nullable_crc": (128, True, True, optional), "required_no_crc": (32, False, False, required)}
    files = {label: produce(pa, pq, *settings) for label, settings in cases.items()}
    checked = {label: inspect(pa, pq, files[label], *settings, support, prior) for label, settings in cases.items()}
    source = files["nullable_crc"]
    observed, original = checked["nullable_crc"]
    dictionary, late = original[1]
    first, first_plain, reentry, last = original[0][1]

    def group_error(index, cause):
        return f"(.source (.groupFailure {index} {cause}))"

    def chunk_page(page, offset, cause):
        return f"(.chunk (.page {page} {offset} {cause}))"

    controls, prefixes = {}, []
    zero_writer = "{ ipc := { batches := 0 } }"
    for label, index, frame in (("dictionary", 0, dictionary), ("references", 1, late[0]), ("plain", 4, late[-1])):
        damaged, (offset, declared, computed) = prior["damaged_outer"](source, frame)
        prior["observe_refusal"](pa, pq, damaged, NAME, optional[0], crc=True)
        cause = chunk_page(index, offset, f"(.checksum (.mismatch {declared} {computed}))")
        controls[f"malformed_{label}_outer_crc"] = (damaged, group_error(1, cause), "{}", zero_writer)
        prefixes.append((damaged, cause))
    for label, frame, cause in (
        ("dictionary", dictionary, chunk_page(0, dictionary[0], "(.payload (.malformed .gzip))")),
        ("references", late[0], chunk_page(1, late[0][0], "(.references (.page (.payload (.malformed .gzip))))")),
        ("plain", late[-1], f"(.plain 4 {late[-1][0]} (.payload (.malformed .gzip)))"),
    ):
        damaged, _ = prior["damaged_member_crc"](source, frame, thrift)
        prior["observe_refusal"](pa, pq, damaged, NAME, optional[0], crc=False)
        controls[f"malformed_{label}_inner_crc_valid_outer"] = (damaged, group_error(1, cause), "{}", zero_writer)
        prefixes.append((damaged, cause))

    multiple = append_member(source, late[-1], thrift)
    opened = pq.ParquetFile(pa.BufferReader(multiple), page_checksum_verification=True)
    assert prior["read_group"](pa, opened, NAME, 0) == optional[0]
    _, *frames = support["raw_frames"](multiple, opened.metadata.row_group(1).column(ORDINAL))
    assert frames[-1][0] == late[-1][0]
    assert frames[-1][1][4][1] % 2**32 == zlib.crc32(frames[-1][3])
    trailing = f"(.plain 4 {late[-1][0]} (.payload (.trailingInput .gzip)))"
    controls["assembled_second_member"] = (multiple, group_error(1, trailing), "{}", zero_writer)
    prefixes.append((multiple, trailing))

    phase = edit_encoding(source, reentry, 8, thrift)
    v2 = produce(pa, pq, *cases["nullable_crc"], page_version="2.0")
    dict_only = produce(pa, pq, *cases["nullable_crc"], dictionary_limit=2**20)
    for wire in (v2, dict_only):
        opened = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
        assert [prior["read_group"](pa, opened, NAME, i) for i in range(opened.num_row_groups)] == optional
    v2_meta = pq.ParquetFile(pa.BufferReader(v2)).metadata.row_group(0).column(ORDINAL)
    dict_meta = pq.ParquetFile(pa.BufferReader(dict_only)).metadata.row_group(0).column(ORDINAL)
    assert all(frame[1][1][1] == 3 for frame in list(support["raw_frames"](v2, v2_meta))[1:])
    assert all(frame[1][5][1][2][1] == 8 for frame in list(support["raw_frames"](dict_only, dict_meta))[1:])
    first_group = observed[0]
    dict_stored = first_group["dictionary"]["stored"]["bytes"]
    expanded_reference = first_group["data"][0]["expanded"]["bytes"]
    assert first_group["dictionary"]["expanded"]["bytes"] <= expanded_reference
    assert expanded_reference < first_group["data"][1]["expanded"]["bytes"]
    offset, header, payload, stored = late[-1]
    original_expanded = len(zlib.decompress(stored, wbits=31))
    assert original_expanded == header[2][1]
    edited = thrift["encode"]({**header, 2: (thrift["TType"].I32, original_expanded + 1)})
    assert len(edited) == payload - offset
    wrong_extent = source[:offset] + edited + source[payload:]
    extent_cause = f"(.plain 4 {offset} (.payload .outputSizeMismatch))"
    prefixes.append((wrong_extent, extent_cause))
    controls.update({
        "genuine_v2_fallback": (v2, group_error(0, f"(.header 1 {v2_meta.data_page_offset} .expectedV1)"), "{}", "{}"),
        "genuine_dictionary_only": (dict_only, group_error(0, "(.sequence .missingPlain)"), "{}", "{}"),
        "malformed_plain_first": (edit_encoding(source, first, 0, thrift),
                                  group_error(0, f"(.sequence (.prefixEncoding 1 {first[0]} 0))"), "{}", "{}"),
        "malformed_reentry_before_bad_header": (edit_encoding(phase, last, 5, thrift),
                                  group_error(0, f"(.sequence (.suffixEncoding 3 {reentry[0]} 8))"), "{}", "{}"),
        "malformed_bad_header_before_reentry": (edit_encoding(phase, first_plain, 5, thrift),
                                  group_error(0, f"(.header 2 {first_plain[0]} (.encoding 5))"), "{}", "{}"),
        "low_stored_chunk_cap": (source, group_error(0, "(.chunk .chunkLimit)"),
                                 f"{{ maxChunkBytes := {first_group['span'][1] - first_group['span'][0] - 1} }}", "{}"),
        "low_expanded_chunk_cap": (source, group_error(0, "(.chunk .expandedChunkLimit)"),
                                    f"{{ maxExpandedChunkBytes := {first_group['expanded_total'] - 1} }}", "{}"),
        "low_index_byte_cap": (source, group_error(0, chunk_page(1, first[0], "(.references .indexByteLimit)")),
                               "{ indices := ⟨1048576, 0⟩ }", "{}"),
        "low_dictionary_stored_cap": (
            source, group_error(0, chunk_page(0, original[0][0][0], "(.checksum .byteLimit)")),
            f"{{ scalar := ⟨{dict_stored - 1}, 16777216, ⟨1048576, 16777216⟩, 1048576⟩ }}", "{}"),
        "low_plain_expanded_cap": (
            source, group_error(0, f"(.plain 2 {first_plain[0]} (.payload .outputLimit))"),
            f"{{ scalar := ⟨16777216, {expanded_reference}, ⟨1048576, 16777216⟩, 1048576⟩ }}", "{}"),
        "zero_gzip_calls": (
            source, group_error(0, chunk_page(0, original[0][0][0], "(.payload .gzipIncomplete)")),
            "{ scalar := ⟨16777216, 16777216, ⟨1048576, 16777216⟩, 0⟩ }", "{}"),
        "malformed_plain_expanded_extent_valid_crc": (
            wrong_extent, group_error(1, extent_cause), "{}", zero_writer),
    })

    fingerprint = prior["fingerprint"]
    seen["cases"], seen["controls"] = {}, {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-gzip-fallback-") as temporary:
        folder = Path(temporary)
        outputs, commands = {}, []
        for label, wire in files.items():
            batch, nullable, checksum, rows = cases[label]
            groups = checked[label][0]
            all_pages = [[group["dictionary"], *group["data"]] for group in groups]
            bounds = [tuple(group["span"]) for group in groups]
            offsets = [[page["frame"] for page in pages] for pages in all_pages]
            crcs = format_groups([[page["parquet_crc"] for page in pages] for pages in all_pages])
            entries = [group["dictionary"]["signed_entries"] for group in groups]
            stored_cap = max(stop - start for start, stop in bounds)
            expanded_cap = max(group["expanded_total"] for group in groups)
            path = folder / (label + ".arrows")
            commands += [f"#eval readBack {lean_bytes(wire)} {ORDINAL} {json.dumps(NAME, ensure_ascii=False)} "
                         f"{str(nullable).lower()} {format_groups(rows)} {bounds} {offsets} {crcs} {entries} "
                         f"{stored_cap} {expanded_cap} {json.dumps(str(path))}",
                         f"#guard olderProfilesRefuse {lean_bytes(wire)} {ORDINAL}"]
            seen["cases"][label] = {"parquet": fingerprint(wire), "field": NAME, "selected_ordinal": ORDINAL,
                                    "nullable": nullable, "page_checksum": checksum, "write_batch_size": batch,
                                    "stored_chunk_cap": stored_cap, "expanded_chunk_cap": expanded_cap,
                                    "groups": groups}
            outputs[label] = (path, pa.schema([pa.field(NAME, pa.date32(), nullable=nullable)]), rows)
        for label, (wire, error, limits, output) in controls.items():
            commands.append(f"#eval assertRejects {json.dumps(label)} {lean_bytes(wire)} {ORDINAL} {error} {limits} {output}")
            seen["controls"][label] = {"parquet": fingerprint(wire), "error": error,
                                       "source_limits": limits, "output_limits": output}
        for wire, cause in prefixes:
            commands.append(f'#eval (show IO Unit from do unless keepsPrefix {lean_bytes(wire)} {ORDINAL} 1 '
                            f'{format_groups(optional[:1])} {cause} do throw (IO.userError "prefix differed"))')
        driver = folder / "Oracle.lean"
        driver.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n", encoding="utf-8")
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
    print(f"PASS {len(files)} genuine GZIP DATE fallback files, "
          f"{sum(len(value[-1]) for value in cases.values())} mixed chunks and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
