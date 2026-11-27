"""Pin Snappy DATE dictionaries and inspect the decoded native Date32 IPC."""

import argparse
from hashlib import sha256
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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Snappy/Tests.lean"
NAME, ORDINAL = "日付", 1
MIN_DAY, MAX_DAY = -(2**31), 2**31 - 1
GROUPS = [
    [MIN_DAY, None, -1, MIN_DAY, MAX_DAY, -1] * 30,
    [0, -7, None, 0, 11016, None],
    [-2, None, -4, -2, -6, None] * 30,
]


def pin(data):
    return {"bytes": len(data), "sha256": sha256(data).hexdigest()}


def produce(pa, pq, page_version, *, checksum=True, fallback=False):
    schema = pa.schema([pa.field("plain_int32", pa.int32(), nullable=False), pa.field(NAME, pa.date32())])
    settings = dict(dictionary_pagesize_limit=8, write_batch_size=4, data_page_size=24) if fallback else {}
    groups = [list(range(24))] if fallback else GROUPS
    with pa.BufferOutputStream() as sink:
        with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version,
                              compression="SNAPPY", use_dictionary=[NAME], write_statistics=False,
                              store_schema=False, write_page_checksum=checksum, **settings) as writer:
            for days in groups:
                columns = [pa.array([i % 4 for i in range(len(days))], type=pa.int32()),
                           pa.array(days, type=pa.int32()).view(pa.date32())]
                writer.write_table(pa.Table.from_arrays(columns, schema=schema))
        return sink.getvalue().to_pybytes()


def inspect(pa, pq, wire, page_version, checksum, support, read_group):
    opened = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert opened.schema_arrow[ORDINAL] == pa.field(NAME, pa.date32(), nullable=True)
    assert str(opened.schema.column(0).logical_type) == "None"
    assert [read_group(pa, opened, i) for i in range(opened.num_row_groups)] == GROUPS
    thrift = support["THRIFT"]
    footer_size = struct.unpack_from("<I", wire, len(wire) - 8)[0]
    memory = thrift["TMemoryBuffer"](wire[-8 - footer_size:-8])
    meta = thrift["read_struct"](thrift["TCompactProtocol"](memory))
    kind = thrift["TType"]
    leaf = thrift["list_field"](meta, 2)[ORDINAL + 1]
    assert leaf[1] == (kind.I32, 1) and leaf[3] == (kind.I32, 1) and leaf[6] == (kind.I32, 6)
    assert leaf[10] == (kind.STRUCT, {6: (kind.STRUCT, {})})
    snappy, hybrid = support["SNAPPY"], support["hybrid"]

    observed, originals, flags = [], [], set()
    for index, rows in enumerate(GROUPS):
        column = opened.metadata.row_group(index).column(ORDINAL)
        assert column.compression == "SNAPPY" and column.num_values == len(rows)
        assert column.encodings == ("PLAIN", "RLE", "RLE_DICTIONARY")
        dictionary, data = support["raw_frames"](wire, column)
        for _, header, _, stored in (dictionary, data):
            assert (4 in header) == checksum
            if checksum:
                assert header[4][1] % 2**32 == zlib.crc32(stored)

        dict_offset, header, dict_start, stored_dict = dictionary
        assert dict_offset == column.dictionary_page_offset and header[1][1] == 2
        assert header[7][1][2][1] == 0 and header[7][1][1][1] * 4 == header[2][1]
        expanded = snappy.decompress(stored_dict, header[2][1]).to_pybytes()
        entries = [word for word, in struct.iter_unpack("<i", expanded)]
        assert entries == list(dict.fromkeys(day for day in rows if day is not None))

        data_offset, header, start, stored = data
        assert data_offset == column.data_page_offset == dict_start + len(stored_dict)
        if page_version == "1.0":
            assert header[1][1] == 0
            assert [header[5][1][i][1] for i in (1, 2, 3, 4)] == [len(rows), 8, 3, 3]
            expanded = snappy.decompress(stored, header[2][1]).to_pybytes()
            length = struct.unpack_from("<I", expanded)[0]
            levels, references = expanded[4:4 + length], expanded[4 + length:]
            suffix_start, stored_levels, flag = start, 0, True
        else:
            assert header[1][1] == 3
            info = header[8][1]
            assert [info[i][1] for i in (1, 2, 3, 4, 6)] == [len(rows), rows.count(None), len(rows), 8, 0]
            flag, stored_levels = info[7][1], info[5][1]
            levels, suffix = stored[:stored_levels], stored[stored_levels:]
            expected = header[2][1] - stored_levels
            references = snappy.decompress(suffix, expected).to_pybytes() if flag else suffix
            assert len(references) == expected
            suffix_start = start + stored_levels
        flags.add(flag)
        assert hybrid(levels, 1, len(rows)) == [int(day is not None) for day in rows]
        present = [day for day in rows if day is not None]
        indices = hybrid(references[1:], references[0], len(present))
        assert [entries[i] for i in indices] == present
        stop = start + len(stored)
        assert stop == dict_offset + column.total_compressed_size
        observed.append({"span": [dict_offset, stop], "frames": [dict_offset, data_offset],
                         "crc": [frame[1][4][1] % 2**32 if checksum else None for frame in (dictionary, data)],
                         "dictionary_stored": pin(stored_dict), "data_stored": pin(stored),
                         "data_expanded_bytes": header[2][1], "stored_level_bytes": stored_levels,
                         "value_suffix_compressed": flag, "signed_dictionary": entries,
                         "stored_suffix_start": suffix_start, "decoded_references": pin(references),
                         "slot_count": len(rows), "null_count": rows.count(None)})
        originals.append((dictionary, data))
    assert flags == ({True} if page_version == "1.0" else {True, False})
    return observed, originals


def assert_refusal(pa, pq, changed, index, read_group, *, crc=False):
    opened = pq.ParquetFile(pa.BufferReader(changed), page_checksum_verification=True)
    assert [read_group(pa, opened, i) for i in range(index)] == GROUPS[:index]
    try:
        read_group(pa, opened, index)
    except (pa.ArrowException, OSError) as error:
        if crc:
            assert "CRC" in str(error)
    else:
        raise AssertionError("PyArrow admitted the damaged selected DATE chunk")


def corrupt_crc(wire, frame):
    offset, header, start, body = frame
    changed = bytes([body[0] ^ 1]) + body[1:]
    expected, actual = header[4][1] % 2**32, zlib.crc32(changed)
    assert expected != actual
    return wire[:start] + changed + wire[start + len(body):], offset, expected, actual


def corrupt_reference(wire, frame, suffix_start, thrift):
    offset, header, start, body = frame
    assert header[8][1][7][1] is False
    relative = suffix_start - start
    refs = body[relative:]
    assert refs[:2] == b"\x02\x03" and refs[2] & 3 == 0
    # Reference 3 is absent. Keep the header width after recomputing CRC.
    patched = body[:relative + 2] + bytes([(refs[2] & 0xF0) | 3]) + refs[3:]
    crc = zlib.crc32(patched)
    signed = crc if crc < 2**31 else crc - 2**32
    replaced = thrift["encode"]({**header, 4: (thrift["TType"].I32, signed)})
    assert len(replaced) == start - offset
    return wire[:offset] + replaced + patched + wire[start + len(body):], crc, suffix_start + 2


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
    precedent = runpy.run_path(str(ROOT / "scripts/parquet-date-dictionary-oracle/check.py"))
    reader = precedent["read_group"]
    format_groups = runpy.run_path(str(ROOT / "scripts/parquet-date-selected-leaf-oracle/check.py"))["lean_groups"]
    lean_bytes = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))["lean_bytes"]
    ipc = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    pins = json.loads((ROOT / "scripts/parquet-date-dictionary-oracle/fixtures.json").read_text())
    seen = {k: pins[k] for k in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]

    profiles = {"v1_crc": ("1.0", True), "v2_crc": ("2.0", True), "v2_no_crc": ("2.0", False)}
    files = {label: produce(pa, pq, version_, checksum=crc) for label, (version_, crc) in profiles.items()}
    checked = {label: inspect(pa, pq, files[label], version_, crc, support, reader)
               for label, (version_, crc) in profiles.items()}
    v2 = files["v2_crc"]
    observations, frames = checked["v2_crc"]
    dictionary_bad, dict_offset, dict_expected, dict_actual = corrupt_crc(v2, frames[2][0])
    assert_refusal(pa, pq, dictionary_bad, 2, reader, crc=True)
    data_bad, data_offset, data_expected, data_actual = corrupt_crc(v2, frames[2][1])
    assert_refusal(pa, pq, data_bad, 2, reader, crc=True)
    references_bad, refs_crc, edited = corrupt_reference(v2, frames[1][1],
                                                        observations[1]["stored_suffix_start"], thrift)
    assert_refusal(pa, pq, references_bad, 1, reader)
    dict_cause = f"(.page 0 {dict_offset} (.checksum (.mismatch {dict_expected} {dict_actual})))"
    data_cause = f"(.page 1 {data_offset} (.checksum (.mismatch {data_expected} {data_actual})))"
    refs_cause = f"(.page 1 {frames[1][1][0]} (.references (.outOfBounds 3)))"

    fallback = produce(pa, pq, "2.0", fallback=True)
    column = pq.ParquetFile(pa.BufferReader(fallback)).metadata.row_group(0).column(ORDINAL)
    fallback_frames = list(support["raw_frames"](fallback, column))
    plain_page, plain_frame = next((i, frame) for i, frame in enumerate(fallback_frames[1:], 1)
                                   if frame[1][8][1][4][1] == 0)
    cap = "{ ipc := { batches := 0 } }"
    dict_expansion = f"(.source (.groupFailure 0 (.page 0 {frames[0][0][0]} (.payload .outputLimit))))"
    data_expansion = (f"(.source (.groupFailure 0 (.page 1 {frames[0][1][0]} "
                      "(.references (.page (.payload .outputLimit))))))")
    controls = {
        "late_dictionary_crc": (dictionary_bad, f"(.source (.groupFailure 2 {dict_cause}))", "{}", cap),
        "late_data_crc": (data_bad, f"(.source (.groupFailure 2 {data_cause}))", "{}", cap),
        "late_reference_with_valid_crc": (references_bad, f"(.source (.groupFailure 1 {refs_cause}))", "{}", cap),
        "dictionary_expansion": (v2, dict_expansion, "{ maxDictionaryBytes := 11 }", "{}"),
        "data_expansion": (v2, data_expansion,
                           "{ scalar := ⟨16777216, 24, ⟨1048576, 16777216⟩, 0⟩ }", "{}"),
        "chunk_expansion": (v2, "(.source (.groupFailure 0 .expandedChunkLimit))",
                            "{ maxExpandedChunkBytes := 1 }", "{}"),
        "snappy_fallback": (fallback,
                            f"(.source (.groupFailure 0 (.page {plain_page} {plain_frame[0]} (.encoding 0))))",
                            "{}", "{}"),
    }

    seen["cases"], seen["controls"] = {}, {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-snappy-dictionary-") as temporary:
        folder = Path(temporary)
        outputs, commands = {}, []
        for label, wire in files.items():
            groups = checked[label][0]
            bounds = [tuple(group["span"]) for group in groups]
            offsets = [group["frames"] for group in groups]
            crcs = format_groups([group["crc"] for group in groups])
            path = folder / (label + ".arrows")
            commands += [f"#eval readBack {lean_bytes(wire)} {ORDINAL} {json.dumps(NAME, ensure_ascii=False)} "
                         f"{format_groups(GROUPS)} {bounds} {offsets} {crcs} {json.dumps(str(path))}",
                         f"#guard uncompressedProfilesRefuse {lean_bytes(wire)} {ORDINAL} "
                         f"{json.dumps(NAME, ensure_ascii=False)}"]
            seen["cases"][label] = {"parquet": pin(wire), "selected_ordinal": ORDINAL,
                                    "field": NAME, "nullable": True, "groups": groups}
            outputs[label] = path

        for label, (wire, error, limits, output) in controls.items():
            commands.append(f"#guard rejects {lean_bytes(wire)} {ORDINAL} {error} {limits} {output}")
            seen["controls"][label] = {"parquet": pin(wire), "error": error,
                                       "source_limits": limits, "output_limits": output}
        for wire, index, cause in ((dictionary_bad, 2, dict_cause), (data_bad, 2, data_cause),
                                   (references_bad, 1, refs_cause)):
            commands.append(f"#guard keepsPrefix {lean_bytes(wire)} {ORDINAL} {index} "
                            f"{format_groups(GROUPS[:index])} {cause}")
        seen["controls"]["late_reference_with_valid_crc"].update({"recomputed_crc": refs_crc,
                                                                   "edited_offset": edited})
        driver = folder / "Oracle.lean"
        driver.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
        schema = pa.schema([pa.field(NAME, pa.date32())])
        for label, path in outputs.items():
            wire = path.read_bytes()
            ipc["observe"](pa, wire, schema, GROUPS)
            seen["cases"][label]["lean_ipc"] = pin(wire)

    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(seen, indent=2)
    print(f"PASS {len(files)} selected Snappy DATE IPC readbacks, "
          f"{len(files) * len(GROUPS)} original chunks, and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
