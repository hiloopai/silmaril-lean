"""Verify selected DATE dictionaries and independently read the emitted Date32 IPC."""

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


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Tests.lean"
ORDINAL = 1
NAME = "日付"
GROUPS = [
    [-(2**31), None, -1, -(2**31), 2**31 - 1, -1],
    [0, -7, None, 0, 11016, None],
    [-2, None, -4, -2, -6, None],
]


def fingerprint(wire):
    return {"bytes": len(wire), "sha256": sha256(wire).hexdigest()}


def produce(pa, pq, page_version, *, groups=GROUPS, dictionary=True, compression="NONE", **options):
    schema = pa.schema([pa.field("plain_int32", pa.int32(), nullable=False),
                        pa.field(NAME, pa.date32()), pa.field("neighbor", pa.string())])
    with pa.BufferOutputStream() as sink:
        with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version,
                              compression=compression, use_dictionary=[NAME] if dictionary else False,
                              write_statistics=False, store_schema=False, **options) as writer:
            for group in groups:
                values = pa.array(group, type=pa.int32()).view(pa.date32())
                columns = [pa.array(range(len(group)), type=pa.int32()), values,
                           pa.array(["other"] * len(group), type=pa.string())]
                writer.write_table(pa.Table.from_arrays(columns, schema=schema))
        return sink.getvalue().to_pybytes()


def read_group(pa, parquet, index):
    return parquet.read_row_group(index, columns=[NAME], use_threads=False).column(0).combine_chunks().view(
        pa.int32()).to_pylist()


def inspect(pa, pq, wire, page_version, frames, thrift):
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    assert parquet.schema_arrow.field(ORDINAL) == pa.field(NAME, pa.date32())
    assert str(parquet.schema.column(0).logical_type) == "None"
    assert [read_group(pa, parquet, i) for i in range(parquet.num_row_groups)] == GROUPS
    footer_size = struct.unpack_from("<I", wire, len(wire) - 8)[0]
    memory = thrift["TMemoryBuffer"](wire[-8 - footer_size:-8])
    metadata = thrift["read_struct"](thrift["TCompactProtocol"](memory))
    assert memory.cstringio_buf.tell() == footer_size
    leaf = thrift["list_field"](metadata, 2)[ORDINAL + 1]
    kind = thrift["TType"]
    assert leaf[1] == (kind.I32, 1) and leaf[3] == (kind.I32, 1) and leaf[6] == (kind.I32, 6)
    assert leaf[10] == (kind.STRUCT, {6: (kind.STRUCT, {})})

    seen = []
    for index, group in enumerate(GROUPS):
        column = parquet.metadata.row_group(index).column(ORDINAL)
        assert column.compression == "UNCOMPRESSED"
        assert column.encodings == ("PLAIN", "RLE", "RLE_DICTIONARY")
        dictionary, data = list(frames(wire, column))
        start, header, dict_body, body = dictionary
        words = list(dict.fromkeys(day for day in group if day is not None))
        assert start == column.dictionary_page_offset and header[1][1] == 2
        assert [header[7][1][i][1] for i in (1, 2)] == [len(words), 0]
        assert [word for (word,) in struct.iter_unpack("<i", body)] == words

        data_start, header, body_start, body = data
        assert data_start == column.data_page_offset
        assert data_start == dict_body + len(words) * 4
        assert body_start + len(body) == start + column.total_compressed_size
        if page_version == "1.0":
            assert header[1][1] == 0
            assert [header[5][1][i][1] for i in (1, 2, 3, 4)] == [len(group), 8, 3, 3]
            level_start, level_stop = 4, 4 + struct.unpack_from("<I", body)[0]
        else:
            assert header[1][1] == 3
            info = header[8][1]
            assert [info[i][1] for i in (1, 2, 3, 4, 6, 7)] == [
                len(group), group.count(None), len(group), 8, 0, False]
            level_start, level_stop = 0, info[5][1]
        levels = body[level_start:level_stop]
        mask = [day is not None for day in group]
        assert len(levels) == 2 and levels[0] == 3
        assert [(levels[1] >> i) & 1 for i in range(len(group))] == mask
        refs = body[level_stop:]
        assert len(refs) == 4 and refs[:2] == b"\x02\x03"
        packed = int.from_bytes(refs[2:], "little")
        indices = [(packed >> (2 * i)) & 3 for i in range(sum(mask))]
        assert indices == [words.index(day) for day in group if day is not None]
        seen.append({"span": [start, body_start + len(body)], "dictionary_body_start": dict_body,
                     "data_frame_start": data_start, "first_packed_index": body_start + level_stop + 2,
                     "signed_dictionary": words, "validity": mask, "present_indices": indices,
                     "signed_slots": group})
    return seen


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

    producer = runpy.run_path(str(ROOT / "scripts/parquet-timestamp-dictionary-oracle/check.py"))
    selected = runpy.run_path(str(ROOT / "scripts/parquet-date-selected-leaf-oracle/check.py"))
    ipc = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    source_reader = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))["lean_bytes"]
    predecessor = json.loads((ROOT / "scripts/parquet-date-selected-leaf-oracle/fixtures.json").read_text())
    seen = {key: predecessor[key] for key in
            ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift", "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]

    originals = {profile: produce(pa, pq, profile) for profile in ("1.0", "2.0")}
    cases = {profile: inspect(pa, pq, wire, profile, producer["frames"], producer["THRIFT"])
             for profile, wire in originals.items()}
    late = cases["2.0"][2]
    offset = late["first_packed_index"]
    original = originals["2.0"]
    assert original[offset] & 3 == 0 and len(late["signed_dictionary"]) == 3
    bad = original[:offset] + bytes([original[offset] | 3]) + original[offset + 1:]
    reader = pq.ParquetFile(pa.BufferReader(bad))
    assert [read_group(pa, reader, i) for i in (0, 1)] == GROUPS[:2]
    try:
        read_group(pa, reader, 2)
    except (pa.ArrowException, OSError):
        pass
    else:
        raise AssertionError("PyArrow admitted the absent dictionary index")

    fallback = produce(pa, pq, "2.0", groups=[list(range(24))],
                       dictionary_pagesize_limit=8, write_batch_size=4, data_page_size=24)
    fallback_column = pq.ParquetFile(pa.BufferReader(fallback)).metadata.row_group(0).column(ORDINAL)
    fallback_frames = list(producer["frames"](fallback, fallback_column))
    fallback_page = next(i for i, entry in enumerate(fallback_frames[1:], 1) if entry[1][8][1][4][1] == 0)
    plain = produce(pa, pq, "1.0", dictionary=False)
    crc = produce(pa, pq, "1.0", write_page_checksum=True)
    compressed = produce(pa, pq, "2.0", compression="GZIP")
    cause = f"(.references 1 {late['data_frame_start']} (.outOfBounds 3))"
    controls = {
        "late_absent_index": (bad, ORDINAL, f"(.source (.groupFailure 2 {cause}))", "{}",
                              "{ ipc := { batches := 0 } }"),
        "plain_fallback": (fallback, ORDINAL, f"(.source (.groupFailure 0 (.dataEncoding {fallback_page} 0)))",
                           "{}", "{}"),
        "plain_without_dictionary": (plain, ORDINAL, "(.source (.groupFailure 0 .missingDictionary))", "{}", "{}"),
        "compressed": (compressed, ORDINAL, "(.source (.groupFailure 0 (.chunk .columnCodec)))", "{}", "{}"),
        "crc": (crc, ORDINAL, "(.source (.groupFailure 0 (.chunk .crcUnsupported)))", "{}", "{}"),
        "entry_budget": (original, ORDINAL, "(.source (.groupFailure 0 (.chunk .entryLimit)))",
                         "{ maxEntries := 2 }", "{}"),
        "unannotated_neighbor": (original, 0, "(.source (.openFailure (.annotation .missingAnnotation)))", "{}", "{}"),
    }

    seen["cases"] = {}
    seen["controls"] = {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-dictionary-") as temporary:
        folder = Path(temporary)
        commands = []
        outputs = {}
        for profile, wire in originals.items():
            path = folder / (profile + ".arrows")
            metadata = cases[profile]
            bounds = [tuple(group["span"]) for group in metadata]
            entries = [group["signed_dictionary"] for group in metadata]
            commands.append(f"#eval readBack {source_reader(wire)} {ORDINAL} {json.dumps(NAME, ensure_ascii=False)} "
                            f"{selected['lean_groups'](GROUPS)} {bounds} {entries} {json.dumps(str(path))}")
            commands.append(f"#guard plainRefuses {source_reader(wire)} {ORDINAL}")
            seen["cases"][profile] = {"parquet": fingerprint(wire), "selected_ordinal": ORDINAL,
                                      "field": NAME, "nullable": True, "groups": metadata}
            outputs[profile] = path
        for label, (wire, ordinal, error, limits, output) in controls.items():
            commands.append(f"#guard rejects {source_reader(wire)} {ordinal} {error} {limits} {output}")
            seen["controls"][label] = {"parquet": fingerprint(wire), "selected_ordinal": ordinal,
                                       "error": error, "dictionary_limits": limits, "output_limits": output}
        seen["controls"]["late_absent_index"]["edited_index_octet"] = offset
        commands.append(f"#guard keepsPrefix {source_reader(bad)} {ORDINAL} 2 "
                        f"{selected['lean_groups'](GROUPS[:2])} {cause}")

        driver = folder / "Oracle.lean"
        driver.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
        schema = pa.schema([pa.field(NAME, pa.date32())])
        for profile, path in outputs.items():
            wire = path.read_bytes()
            ipc["observe"](pa, wire, schema, GROUPS)
            seen["cases"][profile]["lean_ipc"] = fingerprint(wire)

    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(seen, indent=2)
    print(f"PASS {len(originals)} selected DATE dictionary readbacks, "
          f"{sum(map(len, cases.values()))} chunk-local dictionaries, and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
