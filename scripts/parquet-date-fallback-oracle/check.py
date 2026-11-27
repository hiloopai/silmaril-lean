"""Pin genuine PyArrow DATE fallback and independently observe its IPC readback."""

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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Fallback/Tests.lean"
ORDINAL = 1
NAME = "日付"
MIN_DAY, MAX_DAY = -(2**31), 2**31 - 1
GROUPS = [
    [MIN_DAY, None, -11, MAX_DAY] + [None if i % 5 == 2 else -100 + i for i in range(20)],
    [-17, MAX_DAY, None, MIN_DAY] + [None if i % 5 == 3 else 200 + i for i in range(20)],
]
SETTINGS = {"dictionary_pagesize_limit": 8, "write_batch_size": 4, "data_page_size": 24}


def fingerprint(wire):
    return {"bytes": len(wire), "sha256": sha256(wire).hexdigest()}


def produce(pa, pq, page_version):
    schema = pa.schema([pa.field("plain_int32", pa.int32(), nullable=False), pa.field(NAME, pa.date32())])
    with pa.BufferOutputStream() as sink:
        with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version,
                              compression="NONE", use_dictionary=[NAME], write_statistics=False,
                              store_schema=False, **SETTINGS) as writer:
            for group in GROUPS:
                values = pa.array(group, type=pa.int32()).view(pa.date32())
                writer.write_table(pa.Table.from_arrays([pa.array(range(len(group)), type=pa.int32()), values],
                                                       schema=schema))
        return sink.getvalue().to_pybytes()


def inspect(pa, pq, wire, page_version, frames, hybrid, read_group, thrift):
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    assert parquet.schema_arrow.field(ORDINAL) == pa.field(NAME, pa.date32())
    assert str(parquet.schema.column(0).logical_type) == "None"
    assert [read_group(pa, parquet, i) for i in range(parquet.num_row_groups)] == GROUPS
    kind = thrift["TType"]
    footer_size = struct.unpack_from("<I", wire, len(wire) - 8)[0]
    reader = thrift["TCompactProtocol"](thrift["TMemoryBuffer"](wire[-8 - footer_size:-8]))
    leaf = thrift["list_field"](thrift["read_struct"](reader), 2)[ORDINAL + 1]
    assert leaf[1] == (kind.I32, 1) and leaf[3] == (kind.I32, 1) and leaf[6] == (kind.I32, 6)
    assert leaf[10] == (kind.STRUCT, {6: (kind.STRUCT, {})})

    observations, raw_pages = [], []
    for index, rows in enumerate(GROUPS):
        column = parquet.metadata.row_group(index).column(ORDINAL)
        assert column.compression == "UNCOMPRESSED" and column.num_values == len(rows)
        assert column.encodings == ("PLAIN", "RLE", "RLE_DICTIONARY")
        dictionary, *data = frames(wire, column)
        start, header, dictionary_body, payload = dictionary
        assert start == column.dictionary_page_offset and header[1][1] == 2
        entries = [word for word, in struct.iter_unpack("<i", payload)]
        assert [header[7][1][i][1] for i in (1, 2)] == [len(entries), 0]
        assert data[0][0] == column.data_page_offset

        cursor, pages = 0, []
        for offset, header, body_start, body in data:
            v1 = page_version == "1.0"
            assert header[1][1] == (0 if v1 else 3)
            info = header[5 if v1 else 8][1]
            count = info[1][1]
            slots = rows[cursor:cursor + count]
            cursor += count
            if v1:
                assert [info[i][1] for i in (3, 4)] == [3, 3]
                level_start, level_end = 4, 4 + struct.unpack_from("<I", body)[0]
                encoding = info[2][1]
            else:
                assert [info[i][1] for i in (2, 3, 6, 7)] == [slots.count(None), count, 0, False]
                level_start, level_end = 0, info[5][1]
                encoding = info[4][1]
            validity = hybrid(body[level_start:level_end], 1, count)
            assert validity == [int(day is not None) for day in slots]
            scalars = body[level_end:]
            values = [day for day in slots if day is not None]
            if encoding == 8:
                indices = hybrid(scalars[1:], scalars[0], len(values))
                assert [entries[i] for i in indices] == values
                assert entries == list(dict.fromkeys(values))
            else:
                assert encoding == 0
                assert [word for word, in struct.iter_unpack("<i", scalars)] == values
                indices = None
            pages.append({"tag": encoding, "header": offset, "payload": [body_start, body_start + len(body)],
                          "validity": validity, "indices": indices, "signed_slots": slots})
        assert cursor == len(rows)
        assert [page["tag"] for page in pages] == [8, 0, 0, 0]
        assert [len(page["signed_slots"]) for page in pages] == [4, 8, 8, 4]
        stop = start + column.total_compressed_size
        assert pages[-1]["payload"][1] == stop
        observations.append({"span": [start, stop], "dictionary_header": start,
                             "dictionary_payload": [dictionary_body, data[0][0]],
                             "signed_dictionary": entries, "data": pages})
        raw_pages.append(data)
    return observations, raw_pages


def truncate_last_plain(wire, last, thrift):
    offset, header, start, payload = last
    kind = thrift["TType"]
    assert header[8][1][4][1] == 0
    end = start + len(payload)
    footer_size = struct.unpack_from("<I", wire, len(wire) - 8)[0]
    assert end == len(wire) - 8 - footer_size
    changed_header = {**header, 2: (kind.I32, len(payload) - 1), 3: (kind.I32, len(payload) - 1)}
    encoded = thrift["encode"](changed_header)
    assert len(encoded) == start - offset
    partial = wire[:offset] + encoded + payload[:-1] + wire[end:]

    def shrink(metadata):
        group = thrift["list_field"](metadata, 4)[1]
        column = thrift["column_metadata"](metadata, group=1, column=ORDINAL)
        for fields, keys in ((group, (2, 6)), (column, (6, 7))):
            for key in keys:
                field_type, size = fields[key]
                fields[key] = field_type, size - 1

    return thrift["rewrite_footer"](partial, shrink)


def change_tag(wire, frame, tag, thrift):
    offset, header, start, _ = frame
    struct_type, data = header[8]
    changed = {**header, 8: (struct_type, {**data, 4: (thrift["TType"].I32, tag)})}
    encoded = thrift["encode"](changed)
    assert len(encoded) == start - offset
    return wire[:offset] + encoded + wire[start:]


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

    precedent = runpy.run_path(str(ROOT / "scripts/parquet-date-dictionary-oracle/check.py"))
    timestamp = runpy.run_path(str(ROOT / "scripts/parquet-timestamp-dictionary-oracle/check.py"))
    hybrid = runpy.run_path(str(ROOT / "scripts/parquet-timestamp-snappy-dictionary-oracle/check.py"))["hybrid"]
    selected = runpy.run_path(str(ROOT / "scripts/parquet-date-selected-leaf-oracle/check.py"))
    source_reader = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))["lean_bytes"]
    ipc = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    pins = json.loads((ROOT / "scripts/parquet-date-dictionary-oracle/fixtures.json").read_text())
    seen = {k: pins[k] for k in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift",
                                "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == seen["pyarrow"]
    assert version("thrift") == seen["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == seen["lean_toolchain"]
    seen["producer_settings"] = SETTINGS

    thrift = timestamp["THRIFT"]
    files = {profile: produce(pa, pq, profile) for profile in ("1.0", "2.0")}
    inspected = {profile: inspect(pa, pq, wire, profile, timestamp["frames"], hybrid,
                                  precedent["read_group"], thrift)
                 for profile, wire in files.items()}
    v2 = files["2.0"]
    v2_pages = inspected["2.0"][1]
    last = v2_pages[1][-1]
    truncated = truncate_last_plain(v2, last, thrift)
    opened = pq.ParquetFile(pa.BufferReader(truncated))
    assert precedent["read_group"](pa, opened, 0) == GROUPS[0]
    try:
        precedent["read_group"](pa, opened, 1)
    except (pa.ArrowException, OSError):
        pass
    else:
        raise AssertionError("PyArrow admitted the truncated signed PLAIN suffix")
    first = v2_pages[0][0]
    reentry = v2_pages[0][2]
    dictionary_only = precedent["produce"](pa, pq, "2.0")
    assert fingerprint(dictionary_only) == pins["cases"]["2.0"]["parquet"]
    plain_only = precedent["produce"](pa, pq, "1.0", dictionary=False)
    compressed = precedent["produce"](pa, pq, "2.0", compression="GZIP")
    cause = f"(.plain {len(v2_pages[1])} {last[0]} (.plain .truncated))"
    cap = "{ ipc := { batches := 0 } }"
    controls = {
        "late_truncated_plain": (truncated, f"(.source (.groupFailure 1 {cause}))", cap),
        "plain_before_references": (change_tag(v2, first, 0, thrift),
                                    f"(.source (.groupFailure 0 (.prefixEncoding 1 {first[0]} 0)))", "{}"),
        "dictionary_reentry": (change_tag(v2, reentry, 8, thrift),
                               f"(.source (.groupFailure 0 (.suffixEncoding 3 {reentry[0]} 8)))", "{}"),
        "dictionary_only": (dictionary_only, "(.source (.groupFailure 0 .missingPlain))", "{}"),
        "plain_only": (plain_only, "(.source (.groupFailure 0 (.dictionary .missingDictionary)))", "{}"),
        "compressed": (compressed, "(.source (.groupFailure 0 (.dictionary (.chunk .columnCodec))))", "{}"),
        "output_budget": (v2, "(.writer (.writer (.limit .batches)))", cap),
    }

    seen["cases"], seen["controls"] = {}, {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-fallback-") as temporary:
        folder = Path(temporary)
        outputs, commands = {}, []
        for profile, wire in files.items():
            groups = inspected[profile][0]
            bounds = [tuple(group["span"]) for group in groups]
            offsets = [[group["dictionary_header"], *[page["header"] for page in group["data"]]] for group in groups]
            tags = [[page["tag"] for page in group["data"]] for group in groups]
            path = folder / (profile + ".arrows")
            commands += [f"#eval readBack {source_reader(wire)} {ORDINAL} {json.dumps(NAME, ensure_ascii=False)} "
                         f"{selected['lean_groups'](GROUPS)} {bounds} {offsets} {tags} {json.dumps(str(path))}",
                         f"#guard olderProfilesRefuse {source_reader(wire)} {ORDINAL} 2 "
                         f"{json.dumps(NAME, ensure_ascii=False)}"]
            seen["cases"][profile] = {"parquet": fingerprint(wire), "selected_ordinal": ORDINAL,
                                      "field": NAME, "nullable": True, "groups": groups}
            outputs[profile] = path

        for label, (wire, error, output) in controls.items():
            commands.append(f"#guard rejects {source_reader(wire)} {ORDINAL} {error} {output}")
            seen["controls"][label] = {"parquet": fingerprint(wire), "error": error, "output_limits": output}
        seen["controls"]["late_truncated_plain"]["header_offset"] = last[0]
        commands.append(f"#guard keepsPrefix {source_reader(truncated)} {ORDINAL} 1 "
                        f"{selected['lean_groups'](GROUPS[:1])} {cause}")

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
    print(f"PASS {len(files)} genuine selected DATE fallback readbacks, "
          f"{sum(len(case[0]) for case in inspected.values())} mixed chunks, and {len(controls)} typed controls")


if __name__ == "__main__":
    main()
