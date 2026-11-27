"""Compare genuine CRC-bearing Snappy DATE fallback with native Date32 IPC."""

import argparse
from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import random
import runpy
import struct
import subprocess
import sys
import tempfile
import zlib


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Fallback/Snappy/Tests.lean"
NAME, ORDINAL = "日付", 1
MIN_DAY, MAX_DAY = -(2**31), 2**31 - 1
SEED = 2429


def fingerprint(data):
    return {"bytes": len(data), "sha256": sha256(data).hexdigest()}


def groups(batch):
    values = random.Random(SEED)

    def noise():
        return [None if index % 7 == 0 else values.getrandbits(32) + MIN_DAY for index in range(batch)]

    def repeat(pattern):
        return pattern * (batch // len(pattern))

    return [
        repeat([MIN_DAY, None, -11, MIN_DAY, MAX_DAY, -11, None, MAX_DAY])
        + repeat([-7, None, -7, 8, None, 8, -7, 8]) + noise() + repeat([1, None, 0, 1, 0, None, 1, 0]),
        repeat([-17, MAX_DAY, None, MIN_DAY, MIN_DAY, None, -17, MAX_DAY])
        + noise() + repeat([5, None, -5, 5, -5, None, 5, -5]) + noise(),
    ]


def produce(pa, pq, page_version, batch, rows):
    schema = pa.schema([pa.field("plain_int32", pa.int32(), nullable=False), pa.field(NAME, pa.date32())])
    with pa.BufferOutputStream() as sink:
        with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version,
                              compression="SNAPPY", use_dictionary=[NAME], write_statistics=False,
                              store_schema=False, write_page_checksum=True,
                              dictionary_pagesize_limit=8, write_batch_size=batch, data_page_size=24) as writer:
            for days in rows:
                columns = [pa.array([index % 4 for index in range(len(days))], type=pa.int32()),
                           pa.array(days, type=pa.int32()).view(pa.date32())]
                writer.write_table(pa.Table.from_arrays(columns, schema=schema))
        return sink.getvalue().to_pybytes()


def inspect(pa, pq, wire, page_version, batch, rows, support, read_group):
    opened = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert opened.schema_arrow[ORDINAL] == pa.field(NAME, pa.date32(), nullable=True)
    assert str(opened.schema.column(0).logical_type) == "None"
    assert [read_group(pa, opened, i) for i in range(opened.num_row_groups)] == rows
    thrift, snappy, hybrid = support["THRIFT"], support["SNAPPY"], support["hybrid"]
    footer_size = struct.unpack_from("<I", wire, len(wire) - 8)[0]
    memory = thrift["TMemoryBuffer"](wire[-8 - footer_size:-8])
    meta = thrift["read_struct"](thrift["TCompactProtocol"](memory))
    kind = thrift["TType"]
    leaf = thrift["list_field"](meta, 2)[ORDINAL + 1]
    assert leaf[1] == (kind.I32, 1) and leaf[3] == (kind.I32, 1) and leaf[6] == (kind.I32, 6)
    assert leaf[10] == (kind.STRUCT, {6: (kind.STRUCT, {})})

    def expand(stored, size):
        expanded = snappy.decompress(stored, size).to_pybytes()
        assert len(expanded) == size
        return expanded

    observations, raw, flags = [], [], set()
    for index, expected in enumerate(rows):
        column = opened.metadata.row_group(index).column(ORDINAL)
        assert column.compression == "SNAPPY" and column.num_values == len(expected)
        assert column.encodings == ("PLAIN", "RLE", "RLE_DICTIONARY")
        dictionary, *pages = support["raw_frames"](wire, column)
        for _, header, _, stored in (dictionary, *pages):
            assert header[4][1] % 2**32 == zlib.crc32(stored)
        offset, header, payload, stored_dict = dictionary
        assert offset == column.dictionary_page_offset and header[1][1] == 2
        entries = [word for word, in struct.iter_unpack("<i", expand(stored_dict, header[2][1]))]
        assert [header[7][1][i][1] for i in (1, 2)] == [len(entries), 0]
        assert entries == list(dict.fromkeys(value for value in expected[:batch] if value is not None))
        assert pages[0][0] == column.data_page_offset == payload + len(stored_dict)

        cursor, data_obs = 0, []
        for frame_offset, header, body_start, stored in pages:
            v1 = page_version == "1.0"
            assert header[1][1] == (0 if v1 else 3)
            info = header[5 if v1 else 8][1]
            count = info[1][1]
            slots = expected[cursor:cursor + count]
            cursor += count
            if v1:
                assert [info[i][1] for i in (3, 4)] == [3, 3]
                expanded = expand(stored, header[2][1])
                level_size = struct.unpack_from("<I", expanded)[0]
                levels, values = expanded[4:4 + level_size], expanded[4 + level_size:]
                tag, flag, stored_levels = info[2][1], True, 0
            else:
                assert [info[i][1] for i in (2, 3, 6)] == [slots.count(None), count, 0]
                tag, flag, stored_levels = info[4][1], info[7][1], info[5][1]
                levels, suffix = stored[:stored_levels], stored[stored_levels:]
                size = header[2][1] - stored_levels
                values = expand(suffix, size) if flag else suffix
                assert len(values) == size
            assert hybrid(levels, 1, count) == [int(value is not None) for value in slots]
            present = [day for day in slots if day is not None]
            if tag == 8:
                indices = hybrid(values[1:], values[0], len(present))
                assert [entries[i] for i in indices] == present
            else:
                assert tag == 0
                assert [day for day, in struct.iter_unpack("<i", values)] == present
            flags.add((tag, flag))
            data_obs.append({"tag": tag, "frame": frame_offset, "stored_start": body_start,
                             "stored_bytes": fingerprint(stored), "stored_level_bytes": stored_levels,
                             "expanded_bytes": header[2][1], "value_suffix_compressed": flag,
                             "crc": header[4][1] % 2**32, "rows": count, "nulls": slots.count(None),
                             "decoded_scalar_bytes": fingerprint(values)})
        assert cursor == len(expected)
        assert [page["tag"] for page in data_obs] == [8, 0, 0, 0]
        assert [page["rows"] for page in data_obs] == [batch] * 4
        stop = offset + column.total_compressed_size
        assert data_obs[-1]["stored_start"] + data_obs[-1]["stored_bytes"]["bytes"] == stop
        observations.append({"span": [offset, stop], "dictionary_header": offset,
                             "dictionary_crc": dictionary[1][4][1] % 2**32,
                             "dictionary_stored": fingerprint(stored_dict), "signed_dictionary": entries,
                             "expanded_total": len(entries) * 4 + sum(p["expanded_bytes"] for p in data_obs),
                             "data": data_obs})
        raw.append((dictionary, pages))
    expected_flags = {(8, True), (0, True)} if page_version == "1.0" else {
        (8, batch == 128), (0, True), (0, False)}
    assert flags == expected_flags, flags
    return observations, raw


def corrupt_crc(wire, frame):
    offset, header, start, body = frame
    corrupted = bytes([body[0] ^ 1]) + body[1:]
    declared, computed = header[4][1] % 2**32, zlib.crc32(corrupted)
    assert declared != computed
    return wire[:start] + corrupted + wire[start + len(body):], (offset, declared, computed)


def edit_v2_header(wire, frame, changes, thrift):
    offset, header, start, _ = frame
    struct_kind, info = header[8]
    data = {**info, **{field: (thrift["TType"].I32, value) for field, value in changes.items()}}
    edited = thrift["encode"]({**header, 8: (struct_kind, data)})
    assert len(edited) == start - offset
    return wire[:offset] + edited + wire[start:]


def observe_crc_refusal(pa, pq, wire, rows, read_group):
    opened = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert read_group(pa, opened, 0) == rows[0]
    try:
        read_group(pa, opened, 1)
    except (pa.ArrowException, OSError) as error:
        assert "CRC" in str(error)
    else:
        raise AssertionError("PyArrow admitted a damaged Snappy DATE body")


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
    preceding = runpy.run_path(str(ROOT / "scripts/parquet-date-snappy-dictionary-oracle/check.py"))
    read_group = runpy.run_path(str(ROOT / "scripts/parquet-date-dictionary-oracle/check.py"))["read_group"]
    format_groups = runpy.run_path(str(ROOT / "scripts/parquet-date-selected-leaf-oracle/check.py"))["lean_groups"]
    lean_bytes = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))["lean_bytes"]
    ipc = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    pins = json.loads((ROOT / "scripts/parquet-date-snappy-dictionary-oracle/fixtures.json").read_text())
    seen = {key: pins[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                      "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    seen["producer"] = {"seed": SEED, "dictionary_pagesize_limit": 8, "data_page_size": 24,
                        "write_page_checksum": True}

    cases = {"v1": ("1.0", 128), "v2": ("2.0", 128), "v2_raw_references": ("2.0", 32)}
    rows = {label: groups(batch) for label, (_, batch) in cases.items()}
    files = {label: produce(pa, pq, profile, batch, rows[label]) for label, (profile, batch) in cases.items()}
    checked = {label: inspect(pa, pq, files[label], profile, batch, rows[label], support, read_group)
               for label, (profile, batch) in cases.items()}
    v2 = files["v2"]
    v2_observed, v2_frames = checked["v2"]
    assert v2_observed[1]["data"][-1]["stored_level_bytes"] > 0
    mutations = {
        "late_v1_plain_crc": ("v1", 4, checked["v1"][1][1][1][-1]),
        "late_v2_level_crc": ("v2", 4, v2_frames[1][1][-1]),
        "late_v2_reference_crc": ("v2", 1, v2_frames[1][1][0]),
    }
    controls, prefixes = {}, []
    writer_cap = "{ ipc := { batches := 0 } }"
    for label, (source, page, frame) in mutations.items():
        damaged, (offset, declared, computed) = corrupt_crc(files[source], frame)
        observe_crc_refusal(pa, pq, damaged, rows[source], read_group)
        cause = f"(.snappy (.page {page} {offset} (.checksum (.mismatch {declared} {computed}))))"
        controls[label] = (damaged, f"(.source (.groupFailure 1 {cause}))", "{}", writer_cap)
        prefixes.append((damaged, rows[source], cause))

    first, first_plain, reentry, last = v2_frames[0][1]
    reversed_phase = edit_v2_header(v2, reentry, {4: 8}, thrift)
    subsequent_bad = edit_v2_header(reversed_phase, last, {4: 5}, thrift)
    unsupported_first = edit_v2_header(reversed_phase, first_plain, {4: 5}, thrift)
    plain_first = edit_v2_header(v2, first, {4: 0}, thrift)
    late_last = v2_frames[1][1][-1]
    bad_count = edit_v2_header(v2, late_last, {1: 129, 3: 129}, thrift)
    count_cause = "(.snappy (.rowCount 512 513))"
    controls.update({
        "malformed_reverse_before_unsupported": (
            subsequent_bad, f"(.source (.groupFailure 0 (.sequence (.suffixEncoding 3 {reentry[0]} 8))))", "{}", "{}"),
        "malformed_unsupported_before_reverse": (
            unsupported_first, f"(.source (.groupFailure 0 (.snappy (.page 2 {first_plain[0]} (.encoding 5)))))", "{}", "{}"),
        "malformed_plain_first": (
            plain_first, f"(.source (.groupFailure 0 (.sequence (.prefixEncoding 1 {first[0]} 0))))", "{}", "{}"),
        "malformed_cumulative_late_row_count": (bad_count, f"(.source (.groupFailure 1 {count_cause}))", "{}", writer_cap),
    })
    prefixes.append((bad_count, rows["v2"], count_cause))

    group_zero = v2_observed[0]
    cap = group_zero["expanded_total"] - 1
    assert max(page["expanded_bytes"] for page in group_zero["data"]) < cap
    controls["cumulative_expansion_cap"] = (v2, "(.source (.groupFailure 0 (.snappy .expandedChunkLimit)))",
                                             f"{{ maxExpandedChunkBytes := {cap} }}", "{}")
    page_cap = max(len(group_zero["signed_dictionary"]) * 4, group_zero["data"][0]["expanded_bytes"])
    assert page_cap < group_zero["data"][1]["expanded_bytes"]
    controls["plain_page_expansion_cap"] = (
        v2, f"(.source (.groupFailure 0 (.plain 2 {first_plain[0]} (.payload .outputLimit))))",
        f"{{ scalar := ⟨16777216, {page_cap}, ⟨1048576, 16777216⟩, 0⟩ }}", "{}")
    dictionary_only = preceding["produce"](pa, pq, "2.0")
    assert fingerprint(dictionary_only) == pins["cases"]["v2_crc"]["parquet"]
    controls["dictionary_only"] = (dictionary_only, "(.source (.groupFailure 0 (.sequence .missingPlain)))", "{}", "{}")

    seen["cases"], seen["controls"] = {}, {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-snappy-fallback-") as temporary:
        folder = Path(temporary)
        outputs, commands = {}, []
        for label, wire in files.items():
            observed = checked[label][0]
            bounds = [tuple(group["span"]) for group in observed]
            offsets = [[group["dictionary_header"], *[page["frame"] for page in group["data"]]] for group in observed]
            crcs = format_groups([[group["dictionary_crc"], *[page["crc"] for page in group["data"]]]
                                  for group in observed])
            cap = max(group["expanded_total"] for group in observed)
            path = folder / (label + ".arrows")
            commands += [f"#eval readBack {lean_bytes(wire)} {ORDINAL} {json.dumps(NAME, ensure_ascii=False)} "
                         f"{format_groups(rows[label])} {bounds} {offsets} {crcs} {cap} {json.dumps(str(path))}",
                         f"#guard olderProfilesRefuse {lean_bytes(wire)} {ORDINAL} {json.dumps(NAME, ensure_ascii=False)}"]
            seen["cases"][label] = {"parquet": fingerprint(wire), "page_version": cases[label][0],
                                    "write_batch_size": cases[label][1], "selected_ordinal": ORDINAL,
                                    "field": NAME, "nullable": True, "max_expanded_chunk_bytes": cap,
                                    "groups": observed}
            outputs[label] = path
        for label, (wire, error, limits, output) in controls.items():
            commands.append(f"#guard rejects {lean_bytes(wire)} {ORDINAL} {error} {limits} {output}")
            seen["controls"][label] = {"parquet": fingerprint(wire), "error": error,
                                       "source_limits": limits, "output_limits": output}
        for wire, days, cause in prefixes:
            commands.append(f"#guard keepsPrefix {lean_bytes(wire)} {ORDINAL} 1 "
                            f"{format_groups(days[:1])} {cause}")

        driver = folder / "Oracle.lean"
        driver.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
        schema = pa.schema([pa.field(NAME, pa.date32())])
        for label, path in outputs.items():
            wire = path.read_bytes()
            ipc["observe"](pa, wire, schema, rows[label])
            seen["cases"][label]["lean_ipc"] = fingerprint(wire)

    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(seen, indent=2)
    print(f"PASS {len(files)} CRC-bearing Snappy DATE fallback streams, "
          f"{sum(len(value) for value in rows.values())} mixed chunks, and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
