"""Compare strict codec-0 TIMESTAMP V2 dispatch with pinned PyArrow and Thrift."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile

import pyarrow as pa
from thrift.Thrift import TType

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FALLBACK = runpy.run_path(str(HERE.parent / "parquet-timestamp-uncompressed-fallback-v2-oracle/check.py"))
REFERENCES = FALLBACK["LITERAL"]
PLAIN = FALLBACK["PLAIN"]
THRIFT, MIXED, RAW_FRAMES = (FALLBACK[name] for name in ("THRIFT", "MIXED", "RAW_FRAMES"))
OPEN, READ, ASSEMBLE, BAD, VERIFY_IPC = (PLAIN[name] for name in ("OPEN", "READ", "ASSEMBLE", "BAD", "VERIFY_IPC"))
CRC = FALLBACK["CRC"]
SPLICE = FALLBACK["SPLICE"]
FRAMES = PLAIN["FRAMES"]
MODES = ("plain", "references", "fallback")


def populations(nullable):
    short = PLAIN["DICT"]["GROUPS"]
    first, last = FALLBACK["BASE"]["PRIOR"]["groups"]()
    batch = FALLBACK["BATCH"]
    sparse = [None] * batch
    sparse[2], sparse[-1] = FALLBACK["MIN"], FALLBACK["MAX"]
    populations = (short, short[1:] + short[:1], [first, sparse + first[-batch:] + first[batch:2 * batch], last])
    return populations if nullable else tuple(
        [[0 if slot is None else slot for slot in group] for group in groups] for groups in populations)


def observe_frames(wire, group):
    metadata = THRIFT["column_metadata"](MIXED["metadata"](wire), group, 1)
    assert metadata[4][1] == 0
    start, stop = MIXED["column_extent"](metadata)
    if 11 in metadata:
        assert start == metadata[11][1]
    else:
        assert start == metadata[9][1]
    frames = list(FRAMES(wire, start, stop))
    assert frames and frames[-1][2] + len(frames[-1][3]) == stop
    if 11 in metadata:
        assert frames[0][1][1][1] == 2
    data = frames[1:] if 11 in metadata else frames
    assert data and data[0][0] == metadata[9][1]
    tags = [frame[1][8][1][4][1] for frame in data]
    profile = "fallback" if 11 in metadata and 0 in tags else "references" if 11 in metadata else "plain"
    assert all(frame[1][1][1] == 3 for frame in data)
    return profile, frames


def producers():
    cases, wires = {}, {}
    for revision, field in (
        ("utc", pa.field("ticks", pa.timestamp("ns", "UTC"))),
        ("local", pa.field("ticks", pa.timestamp("us"), nullable=False)),
    ):
        groups = populations(field.nullable)
        checksum = field.nullable
        for profile, rows in zip(MODES, groups, strict=True):
            name = f"native_{revision}_{profile}"
            if profile == "fallback":
                wires[name] = FALLBACK["produce"](field, rows, checksum=checksum)
                FALLBACK["inspect"](wires[name], field, rows, checksum)
            elif profile == "references":
                wires[name] = PLAIN["produce"](field, rows, checksum=checksum, dictionary=True)
                REFERENCES["inspect"](wires[name], field, rows, checksum)
            else:
                wires[name] = PLAIN["produce"](field, rows, checksum=checksum)
                PLAIN["inspect"](wires[name], field, rows, checksum)
            cases[name] = field, [profile] * len(rows), rows

        selection = [(f"native_{revision}_{profile}", ordinal)
                     for profile, ordinal in zip(MODES * 2, (0, 1, 2, 2, 0, 1), strict=True)]
        name = f"assembled_{revision}"
        wires[name] = ASSEMBLE([(wires[source], index) for source, index in selection])
        expected = [cases[source][2][index] for source, index in selection]
        cases[name] = field, list(MODES * 2), expected
        parquet = OPEN(wires[name])
        assert parquet.schema_arrow.field(1).equals(field) and parquet.num_row_groups == len(expected)
        assert [READ(parquet, index) for index in range(len(expected))] == expected
        for group, (source, index) in enumerate(selection):
            original_profile, original = observe_frames(wires[source], index)
            copied_profile, copied = observe_frames(wires[name], group)
            assert copied_profile == original_profile == cases[name][1][group]
            original_stop = original[-1][2] + len(original[-1][3])
            copied_stop = copied[-1][2] + len(copied[-1][3])
            assert wires[name][copied[0][0]:copied_stop] == wires[source][original[0][0]:original_stop]
        print(f"{name}: independently read six original chunks in order {cases[name][1]}")
    return wires, cases


def fixtures():
    wires, cases = producers()
    wire = wires["assembled_utc"]
    utc, _, rows = cases["assembled_utc"]
    _, plain = observe_frames(wire, 3)
    _, reference = observe_frames(wire, 4)
    _, fallback = observe_frames(wire, 5)
    wires["mutated_plain_crc"], plain_crc = CRC(wire, plain[0])
    wires["mutated_dictionary_crc"], dict_crc = CRC(wire, reference[0])
    wires["mutated_reference_crc"], refs_crc = CRC(wire, reference[1])
    wires["mutated_fallback_crc"], fallback_crc = CRC(wire, fallback[2])
    wires["mutated_competing_crc"], _ = CRC(wires["mutated_plain_crc"], fallback[2])
    for name, group in (("mutated_plain_crc", 3), ("mutated_dictionary_crc", 4),
                        ("mutated_reference_crc", 4), ("mutated_fallback_crc", 5), ("mutated_competing_crc", 3)):
        BAD(wires[name], rows, group, "CRC")

    wires["mutated_reentry"] = SPLICE["retag"](wire, fallback[-1], 8)
    wires["mutated_early_header"] = SPLICE["retag"](wire, fallback[1], 5)
    assert observe_frames(wires["mutated_early_header"], 5)[0] == "fallback"
    wires["mutated_reference_header"] = SPLICE["retag"](wire, reference[1], 5)
    assert observe_frames(wires["mutated_reference_header"], 4)[0] == "references"

    wires["native_v1_component"] = FALLBACK["produce"](utc, rows[5:], checksum=True, pages="1.0")
    wires["assembled_v1"] = ASSEMBLE([(wire, i) for i in range(5)] + [(wires["native_v1_component"], 0)])
    parquet = OPEN(wires["assembled_v1"])
    assert [READ(parquet, index) for index in range(6)] == rows
    _, *v1_pages = RAW_FRAMES(wires["assembled_v1"], parquet.metadata.row_group(5).column(1))
    assert all(page[1][1][1] == 0 for page in v1_pages)
    assert [page[1][5][1][2][1] for page in v1_pages] == [8, 0, 0]

    _, first_fallback = observe_frames(wire, 2)
    def shift_data_offset(footer):
        chunk = THRIFT["column_metadata"](footer, 2, 1)
        assert chunk[9][1] == first_fallback[1][0]
        chunk[9] = TType.I64, chunk[9][1] + 1

    wires["mutated_data_offset"] = THRIFT["rewrite_footer"](wire, shift_data_offset)
    meta = MIXED["metadata"](wire)
    first_reference = THRIFT["column_metadata"](meta, 1, 1)
    chunk_cap = first_reference[7][1]
    assert chunk_cap < THRIFT["column_metadata"](meta, 2, 1)[7][1]

    wires["native_snappy_dictionary"] = FALLBACK["BASE"]["produce"](utc, rows[5:], checksum=True)
    wires["native_snappy_plain"] = PLAIN["produce"](utc, rows[3:4], checksum=True, codec="SNAPPY")
    evidence = [*plain_crc, *dict_crc, *refs_crc, *fallback_crc, fallback[-1][0], fallback[1][0], reference[1][0],
                first_fallback[1][0], v1_pages[0][0], chunk_cap]
    return wires, cases, evidence


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-uncompressed-dispatch-v2-") as temporary:
        output = Path(temporary)
        for name, wire in wires.items():
            (output / f"{name}.parquet").write_bytes(wire)
        for name, (_, profiles, rows) in cases.items():
            lines = [",".join([profile, *("null" if val is None else str(val) for val in group)])
                     for profile, group in zip(profiles, rows, strict=True)]
            (output / f"{name}.txt").write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(cases)
        for name, (field, _, rows) in cases.items():
            VERIFY_IPC((output / f"{name}.arrows").read_bytes(), field, rows)


if __name__ == "__main__":
    main()
