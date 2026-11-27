"""Check original Snappy/GZIP V1 dictionary frames and actual Lean-emitted IPC."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile
import zlib

import pyarrow as pa
from thrift.Thrift import TType

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREVIOUS = runpy.run_path(str(HERE.parent / "parquet-timestamp-scalar-dictionary-oracle/check.py"))
SCALAR = PREVIOUS["SCALAR"]
THRIFT, OPEN, READ, HYBRID, CRC, BAD, VERIFY_IPC = (
    PREVIOUS[name] for name in ("THRIFT", "OPEN", "READ", "HYBRID", "CRC", "BAD", "VERIFY_IPC")
)
frames_at = PREVIOUS["frames_at"]
CODECS = {**SCALAR["BASE_CODECS"], 2: PREVIOUS["COMPRESSED"]["gzip_body"]}


def inspect_v1(wire, field, groups, codec, fallback):
    parquet = PREVIOUS["check_footer"](wire, field, groups)
    for index, ticks in enumerate(groups):
        metadata, frames = frames_at(wire, index)
        assert metadata[1][1] == 2 and metadata[4][1] == codec and metadata[5][1] == len(ticks)
        assert THRIFT["list_field"](metadata, 2) == [0, 3, 8]
        assert 10 not in metadata and metadata[11][1] == frames[0][0]
        assert metadata[9][1] == frames[1][0]
        assert sum(payload - offset + header[2][1] for offset, header, payload, _ in frames) == metadata[6][1]
        expanded = []
        for _, header, _, stored in frames:
            assert header[3][1] == len(stored) and zlib.crc32(stored) == header[4][1] % 2**32
            raw = CODECS[codec](stored, header[2][1])
            assert len(raw) == header[2][1]
            expanded.append(raw)
        dictionary = frames[0][1]
        assert dictionary[1][1] == 2 and dictionary[7][1][2][1] == 0
        entries = [tick for tick, in struct.iter_unpack("<q", expanded[0])]
        assert len(entries) == dictionary[7][1][1][1]
        cursor, tags, references = 0, [], []
        for (_, header, _, _), raw in zip(frames[1:], expanded[1:], strict=True):
            assert header[1][1] == 0
            data = header[5][1]
            count, tag, definitions, repetitions = (data[i][1] for i in range(1, 5))
            assert definitions == repetitions == 3
            page, cursor = ticks[cursor:cursor + count], cursor + count
            assert len(page) == count
            if field.nullable:
                size, = struct.unpack_from("<I", raw)
                assert len(raw) >= 4 + size
                assert HYBRID(raw[4:4 + size], 1, count) == [int(tick is not None) for tick in page]
                raw = raw[4 + size:]
            else:
                assert None not in page
            present = [tick for tick in page if tick is not None]
            if tag == 8:
                observed = [entries[slot] for slot in HYBRID(raw[1:], raw[0], len(present))]
                references.extend(observed)
            else:
                assert tag == 0 and len(raw) == 8 * len(present)
                observed = [tick for tick, in struct.iter_unpack("<q", raw)]
            assert observed == present
            tags.append(tag)
        assert tags == ([8, 0, 0, 0] if fallback else [8, 8, 8, 8])
        assert entries == list(dict.fromkeys(references)) and cursor == len(ticks)
        assert READ(parquet, index) == ticks
        print(f"V1 group {index}, codec {codec}, original offsets {[f[0] for f in frames]}, tags {tags}")


def combine_versions(v1, v2):
    """Keep a V1 dictionary and first data frame, then copy its V2 counterpart's remaining frames."""
    footer, target = SCALAR["metadata"](v1, 0)
    _, first = frames_at(v1, 0)
    _, second = frames_at(v2, 0)
    assert first[0][3] == second[0][3]
    assert [frame[1][5][1][1][1] for frame in first[1:]] == [frame[1][8][1][1][1] for frame in second[1:]]
    origins = [(v1, frame) for frame in first[:2]] + [(v2, frame) for frame in second[2:]]
    frame_bytes = [source[offset:payload + len(stored)] for source, (offset, _, payload, stored) in origins]
    group, = THRIFT["list_field"](footer, 4)
    start, stop = SCALAR["MIXED"]["column_extent"](target)
    assert stop == len(v1) - 8 - struct.unpack_from("<I", v1, len(v1) - 8)[0]
    decoded = sum(payload - offset + header[2][1] for _, (offset, header, payload, _) in origins)
    for tag, size, group_tag in ((6, decoded, 2), (7, sum(map(len, frame_bytes)), 6)):
        if group_tag in group:
            group[group_tag] = TType.I64, group[group_tag][1] - target[tag][1] + size
        target[tag] = TType.I64, size
    encoded = THRIFT["encode"](footer)
    assembled = v1[:start] + b"".join(frame_bytes) + encoded + struct.pack("<I", len(encoded)) + b"PAR1"
    metadata, frames = frames_at(assembled, 0)
    assert metadata[11][1] == frames[0][0] and metadata[9][1] == frames[1][0]
    for (offset, header, payload, stored), source in zip(frames, frame_bytes, strict=True):
        assert assembled[offset:payload + len(stored)] == source
        assert zlib.crc32(stored) == header[4][1] % 2**32
    return assembled


def fixtures():
    utc = pa.field("ticks", pa.timestamp("ns", "UTC"))
    local = pa.field("ticks", pa.timestamp("us"), nullable=False)
    raw = SCALAR["BSS"]["timestamp_groups"]()
    rows = [raw[0], raw[2]]
    required = [[0 if tick is None else tick for tick in group] for group in rows]
    wires, cases = {}, {}

    def dictionary(name, field, groups, codec, fallback, page):
        wire = PREVIOUS["produce_dictionary"](field, groups, codec, fallback, pages=f"{page}.0")
        params = (wire, field, groups, PREVIOUS["CODECS"][codec], fallback)
        if page == 1:
            inspect_v1(*params)
        else:
            PREVIOUS["inspect_dictionary"](*params, CODECS)
        branch = f"{codec}_{page}_{'fallback' if fallback else 'references'}"
        wires[name], cases[name] = wire, (field, groups, [branch] * len(groups))

    for codec in ("snappy", "gzip"):
        for fallback in (False, True):
            dictionary(f"native_{codec}_{'fallback' if fallback else 'references'}", utc, rows, codec, fallback, 1)
    dictionary("native_local_gzip_fallback", local, required, "gzip", True, 1)
    dictionary("native_gzip_v2", utc, rows, "gzip", True, 2)
    dictionary("native_snappy_v2", utc, rows, "snappy", False, 2)

    scalar = SCALAR["produce"](utc, [rows[0]], "2.0", "SNAPPY", checksum=True, encoding="DELTA_BINARY_PACKED")
    SCALAR["inspect"](scalar, utc, [rows[0]], [{5}])
    wires["native_scalar"], cases["native_scalar"] = scalar, (utc, [rows[0]], ["scalar"])

    origins = [("native_scalar", 0), ("native_snappy_references", 1), ("native_gzip_fallback", 0),
               ("native_gzip_v2", 1), ("native_snappy_v2", 0), ("native_snappy_fallback", 0),
               ("native_gzip_references", 1)]
    mixed = SCALAR["ASSEMBLE_GROUPS"]([(wires[name], i) for name, i in origins])
    mixed_rows = [cases[name][1][i] for name, i in origins]
    modes = [cases[name][2][i] for name, i in origins]
    captures = []
    for index, (name, group) in enumerate(origins):
        assert SCALAR["chunk_bytes"](mixed, index) == SCALAR["chunk_bytes"](wires[name], group)
        assert READ(OPEN(mixed), index) == mixed_rows[index]
        metadata, frames = frames_at(mixed, index)
        assert metadata[9][1] == frames[int(11 in metadata)][0]
        if 11 in metadata:
            assert metadata[11][1] == frames[0][0]
        captures.append(frames)
    wires["assembled_mixed"], cases["assembled_mixed"] = mixed, (utc, mixed_rows, modes)

    wires["mutated_v1_crc"], crc = CRC(mixed, captures[5][2])
    wires["mutated_competing_crc"], _ = CRC(wires["mutated_v1_crc"], captures[6][0])
    wires["mutated_dictionary_crc"], dict_crc = CRC(mixed, captures[6][0])
    BAD(wires["mutated_v1_crc"], mixed_rows, 5, "CRC")
    BAD(wires["mutated_dictionary_crc"], mixed_rows, 6, "CRC")
    wires["mutated_advertised_tag_2"] = SCALAR["footer_tags"](mixed, 5, [0, 2, 3, 8])
    assert SCALAR["chunk_bytes"](wires["mutated_advertised_tag_2"], 5) == SCALAR["chunk_bytes"](mixed, 5)

    v1 = PREVIOUS["produce_dictionary"](utc, [rows[0]], "snappy", True, pages="1.0")
    v2 = PREVIOUS["produce_dictionary"](utc, [rows[0]], "snappy", True, pages="2.0")
    versions = combine_versions(v1, v2)
    hybrid = SCALAR["ASSEMBLE_GROUPS"]([(mixed, i) for i in range(5)] + [(versions, 0)])
    assert [READ(OPEN(hybrid), i) for i in range(6)] == mixed_rows[:6]
    assert SCALAR["chunk_bytes"](hybrid, 5) == SCALAR["chunk_bytes"](versions, 0)
    _, hybrid_frames = frames_at(hybrid, 5)
    assert [frame[1][1][1] for frame in hybrid_frames] == [2, 0, 3, 3, 3]
    wires["assembled_mixed_versions"] = hybrid
    return wires, cases, [*crc, *dict_crc, hybrid_frames[2][0]]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-dictionary-v1-groups-") as folder:
        output = Path(folder)
        for name, wire in wires.items():
            (output / f"{name}.parquet").write_bytes(wire)
        for name, (_, rows, modes) in cases.items():
            lines = [mode + "," + ",".join("null" if tick is None else str(tick) for tick in group)
                     for mode, group in zip(modes, rows, strict=True)]
            (output / f"{name}.txt").write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(cases)
        for name, (field, rows, _) in cases.items():
            VERIFY_IPC((output / f"{name}.arrows").read_bytes(), field, rows)


if __name__ == "__main__":
    main()
