"""Compare checked codec-0 and Zstandard dictionary V1 with independent native readers."""

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

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WITH_V1 = runpy.run_path(str(HERE.parent / "parquet-timestamp-dictionary-v1-groups-oracle/check.py"))
PREVIOUS, SCALAR = WITH_V1["PREVIOUS"], WITH_V1["SCALAR"]
THRIFT, OPEN, READ, CRC, BAD, VERIFY_IPC = (
    WITH_V1[name] for name in ("THRIFT", "OPEN", "READ", "CRC", "BAD", "VERIFY_IPC")
)
frames_at = WITH_V1["frames_at"]
TType = SCALAR["TType"]


def fixtures():
    compressed = PREVIOUS["COMPRESSED"]
    frame_extent = compressed["DATE_ZSTD"]["frame_extent"]()
    codecs = {**WITH_V1["CODECS"],
              6: lambda stored, size: compressed["zstd_body"](frame_extent, stored, size)}
    utc = pa.field("ticks", pa.timestamp("ns", "UTC"))
    local = pa.field("ticks", pa.timestamp("us"), nullable=False)
    raw = SCALAR["BSS"]["timestamp_groups"]()
    rows = [raw[0], raw[2]]
    required = [[0 if tick is None else tick for tick in row] for row in rows]
    wires, cases = {}, {}

    def dictionary(name, field, groups, codec, fallback, page):
        wire = PREVIOUS["produce_dictionary"](field, groups, codec, fallback, pages=f"{page}.0")
        mode = "fallback" if fallback else "references"
        print(name)
        inspect = WITH_V1["inspect_v1"] if page == 1 else PREVIOUS["inspect_dictionary"]
        inspect(wire, field, groups, PREVIOUS["CODECS"][codec], fallback, codecs)
        wires[name], cases[name] = wire, (field, groups, [f"{codec}_{page}_{mode}"] * len(groups))

    for codec in ("none", "zstd"):
        for mode in ("references", "fallback"):
            dictionary(f"native_{codec}_{mode}", utc, rows, codec, mode == "fallback", 1)
    dictionary("native_local_zstd_fallback", local, required, "zstd", True, 1)
    dictionary("native_none_v2", utc, [rows[0]], "none", False, 2)
    dictionary("native_zstd_v2", utc, [rows[0]], "zstd", True, 2)
    dictionary("native_snappy_v1", utc, [rows[0]], "snappy", True, 1)
    dictionary("native_gzip_v1", utc, [rows[1]], "gzip", False, 1)

    scalar = SCALAR["produce"](utc, [rows[0]], "1.0", "ZSTD", checksum=True, encoding="BYTE_STREAM_SPLIT")
    SCALAR["inspect"](scalar, utc, [rows[0]], [{9}], codecs=codecs)
    wires["native_scalar"], cases["native_scalar"] = scalar, (utc, [rows[0]], ["scalar"])

    origins = [("native_scalar", 0), ("native_none_v2", 0), ("native_zstd_references", 0),
               ("native_snappy_v1", 0), ("native_none_references", 1), ("native_gzip_v1", 0),
               ("native_zstd_v2", 0), ("native_none_fallback", 1), ("native_zstd_fallback", 1)]
    mixed = SCALAR["ASSEMBLE_GROUPS"]([(wires[name], group) for name, group in origins])
    mixed_rows = [cases[name][1][group] for name, group in origins]
    modes = [cases[name][2][group] for name, group in origins]
    parquet = PREVIOUS["check_footer"](mixed, utc, mixed_rows)
    captures = []
    for index, (name, group) in enumerate(origins):
        metadata, frames = frames_at(mixed, index)
        assert SCALAR["chunk_bytes"](mixed, index) == SCALAR["chunk_bytes"](wires[name], group)
        assert metadata[9][1] == frames[int(11 in metadata)][0]
        if 11 in metadata:
            assert metadata[11][1] == frames[0][0]
        assert READ(parquet, index) == mixed_rows[index]
        captures.append(frames)
    wires["assembled_mixed"], cases["assembled_mixed"] = mixed, (utc, mixed_rows, modes)

    wires["mutated_late_literal_crc"], literal = CRC(mixed, captures[7][2])
    wires["mutated_late_zstd_crc"], zstd = CRC(mixed, captures[8][2])
    wires["mutated_late_zstd_dictionary_crc"], dictionary = CRC(mixed, captures[8][0])
    wires["mutated_competing_crc"], _ = CRC(wires["mutated_late_literal_crc"], captures[8][2])
    for name, index in (("mutated_late_literal_crc", 7), ("mutated_late_zstd_crc", 8),
                        ("mutated_late_zstd_dictionary_crc", 8), ("mutated_competing_crc", 7)):
        BAD(wires[name], mixed_rows, index, "CRC")
    wires["mutated_actual_tag_2"] = SCALAR["GZIP"]["rewrite_header"](
        mixed, captures[7][1], lambda header: header[5][1].update({2: (TType.I32, 2)}))

    expansion = [sum(frame[1][2][1] for frame in captures[group]) for group in (2, 6, 8)]
    assert max(expansion[:2]) < expansion[2]

    v1 = PREVIOUS["produce_dictionary"](utc, [rows[0]], "zstd", True, pages="1.0")
    v2 = PREVIOUS["produce_dictionary"](utc, [rows[0]], "zstd", True, pages="2.0")
    combined = WITH_V1["combine_versions"](v1, v2)
    hybrid = SCALAR["ASSEMBLE_GROUPS"]([(mixed, i) for i in range(6)] + [(combined, 0)])
    assert READ(OPEN(hybrid), 6) == rows[0]
    assert SCALAR["chunk_bytes"](hybrid, 6) == SCALAR["chunk_bytes"](combined, 0)
    _, hybrid_frames = frames_at(hybrid, 6)
    assert [frame[1][1][1] for frame in hybrid_frames] == [2, 0, 3, 3, 3]
    wires["assembled_mixed_versions"] = hybrid
    raw_cap = captures[1][0][1][2][1]
    assert raw_cap < captures[4][0][1][2][1]
    return wires, cases, [*literal, *zstd, *dictionary, captures[7][1][0], hybrid_frames[2][0],
                          max(expansion[:2]), captures[4][0][0], raw_cap]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-all-dictionary-v1-") as folder:
        output = Path(folder)
        for name, wire in wires.items():
            (output / f"{name}.parquet").write_bytes(wire)
        for name, (_, groups, modes) in cases.items():
            lines = [mode + "," + ",".join("null" if tick is None else str(tick) for tick in group)
                     for mode, group in zip(modes, groups, strict=True)]
            (output / f"{name}.txt").write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(cases)
        for name, (field, rows, _) in cases.items():
            VERIFY_IPC((output / f"{name}.arrows").read_bytes(), field, rows)


if __name__ == "__main__":
    main()
