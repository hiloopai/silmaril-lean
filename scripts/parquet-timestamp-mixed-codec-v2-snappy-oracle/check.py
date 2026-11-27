"""Compare three-codec V2 TIMESTAMP assembly against native producers and IPC."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile
import zlib

import pyarrow as pa

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TWO = runpy.run_path(str(HERE.parent / "parquet-timestamp-mixed-codec-v2-oracle/check.py"))
SNAPPY = runpy.run_path(str(HERE.parent / "parquet-timestamp-snappy-dispatch-v2-oracle/check.py"))
ASSEMBLE = TWO["GZIP"]["assemble"]
OPEN, BAD = SNAPPY["OPEN"], SNAPPY["BAD"]
FRAMES, CRC, READ_GROUP, VERIFY_IPC = (TWO[name] for name in ("selected_frames", "CRC", "READ_GROUP", "VERIFY_IPC"))


def inspect(wire, field, sources, rows):
    parquet = OPEN(wire)
    assert parquet.num_row_groups == len(sources) and parquet.schema_arrow.field(1).equals(field)
    seen, captures = set(), []
    for index, ((source, original, codec, profile), ticks) in enumerate(zip(sources, rows, strict=True)):
        metadata, frames = FRAMES(wire, index)
        previous, source_frames = FRAMES(source, original)
        assert metadata[4][1] == previous[4][1] == codec
        assert metadata[5][1] == len(ticks) and len(frames) == len(source_frames)
        assert parquet.metadata.row_group(index).column(1).compression == {1: "SNAPPY", 2: "GZIP", 6: "ZSTD"}[codec]
        for (at, header, body_start, stored), (old_at, old_header, old_body, old_stored) in zip(
                frames, source_frames, strict=True):
            assert (header, body_start - at, stored) == (old_header, old_body - old_at, old_stored)
            assert (4 in header) == field.nullable and len(stored) == header[3][1]
            if 4 in header:
                assert zlib.crc32(stored) == header[4][1] % 2**32
        if profile == "plain":
            assert 11 not in metadata and all(frame[1][1][1] == 3 for frame in frames)
            dictionary, data = None, frames
        else:
            dictionary, *data = frames
            assert dictionary[1][1][1] == 2 and dictionary[1][7][1][2][1] == 0
            assert dictionary[0] == metadata[11][1]
        assert data[0][0] == metadata[9][1] and all(page[1][1][1] == 3 for page in data)
        tags = [page[1][8][1][4][1] for page in data]
        assert tags == sorted(tags, reverse=True)
        assert set(tags) == {"references": {8}, "plain": {0}, "fallback": {8, 0}}[profile]
        assert READ_GROUP(parquet, index) == ticks
        print(f"{field.type} original group {index}: codec {codec}, {profile}, tags {tags}")
        seen.add((codec, profile))
        captures.append((dictionary, data))
    assert seen == {(codec, profile) for codec in (1, 2, 6) for profile in ("plain", "references", "fallback")}
    return captures


def fixtures():
    old_files, old_cases, old_producers, old_evidence = TWO["cases"]()
    old_pins = json.loads((TWO["HERE"] / "fixtures.json").read_text())
    assert old_producers == old_pins["producers"]
    snappy_files, snappy_cases, _ = SNAPPY["fixtures"]()
    snappy_pins = json.loads((SNAPPY["HERE"] / "fixtures.json").read_text())
    files, outputs, observed = {}, {}, {}
    for name in ("utc", "local"):
        mixed = f"mixed_{name}"
        field, old_rows, old_codecs = old_cases[mixed]
        assert sha256(old_files[mixed]).hexdigest() == old_pins["assemblies_and_controls"][mixed]
        native = f"native_{name}"
        snap = f"assembled_{name}"
        for label in (native, snap, f"plain_{name}_producer"):
            assert sha256(snappy_files[label]).hexdigest() == snappy_pins[label]
        snap_field, snap_rows, snap_profiles = snappy_cases[snap]
        assert field.equals(snap_field)

        def from_old(index, profile):
            if name == "local":
                index = 5 - index
            return old_files[mixed], index, old_codecs[index], profile, old_rows[index]

        def from_snappy(index):
            return snappy_files[snap], index, 1, snap_profiles[index], snap_rows[index]

        parts = [from_old(0, "references"), from_snappy(1), from_old(5, "fallback"),
                 from_snappy(3), from_old(2, "fallback"), from_old(1, "plain"),
                 from_snappy(2), from_old(4, "plain"), from_old(3, "references")]
        if name == "local":
            parts.reverse()
        wire = ASSEMBLE([(source, index) for source, index, _, _, _ in parts])
        label = f"assembled_three_{name}"
        rows = [entry[4] for entry in parts]
        files[label] = wire
        outputs[label] = field, rows, [entry[2] for entry in parts]
        observed[label] = inspect(wire, field, [entry[:4] for entry in parts], rows)
        files[f"prior_{name}"] = old_files[mixed]
        outputs[f"prior_{name}"] = old_cases[mixed]
        files[f"snappy_native_{name}"] = snappy_files[native]
        outputs[f"snappy_native_{name}"] = field, snappy_cases[native][1], [1] * len(snappy_cases[native][1])

    for label in ("bad_gzip_crc", "bad_zstd_crc"):
        assert sha256(old_files[label]).hexdigest() == old_pins["assemblies_and_controls"][label]
        files[f"prior_{label}"] = old_files[label]
    good = files["assembled_three_utc"]
    field, rows, _ = outputs["assembled_three_utc"]
    captures = observed["assembled_three_utc"]
    snappy = captures[6][1][1]
    gzip = captures[7][1][0]
    zstd = captures[8][0]
    files["mutated_snappy_crc"], snappy_crc = CRC(good, snappy)
    files["mutated_gzip_crc"], gzip_crc = CRC(good, gzip)
    files["mutated_zstd_crc"], zstd_crc = CRC(good, zstd)
    files["mutated_competing_crc"], _ = CRC(files["mutated_zstd_crc"], snappy)
    for label, index in (("mutated_snappy_crc", 6), ("mutated_gzip_crc", 7),
                         ("mutated_zstd_crc", 8), ("mutated_competing_crc", 6)):
        BAD(files[label], rows, index, "CRC")

    plain_v1 = SNAPPY["DICT"]["produce"](field, rows[6:7], checksum=True, pages="1.0", dictionary=False)
    files["assembled_late_snappy_v1"] = ASSEMBLE([(good, i) for i in range(6)] + [(plain_v1, 0)])
    parquet = OPEN(files["assembled_late_snappy_v1"])
    assert [READ_GROUP(parquet, i) for i in range(7)] == rows[:7]
    metadata, frames = FRAMES(files["assembled_late_snappy_v1"], 6)
    assert metadata[4][1] == 1 and 11 not in metadata and frames[0][1][1][1] == 0

    old = old_files["mixed_utc"]
    _, earlier, _ = old_cases["mixed_utc"]
    uncompressed = SNAPPY["DICT"]["produce"](field, earlier[2:3], checksum=True, codec="NONE", dictionary=False)
    files["prior_unsupported"] = ASSEMBLE([(old, 0), (old, 1), (uncompressed, 0)])
    assert FRAMES(files["prior_unsupported"], 2)[0][4][1] == 0
    assert [READ_GROUP(OPEN(files["prior_unsupported"]), i) for i in range(3)] == earlier[:3]
    return files, outputs, [*snappy_crc, *gzip_crc, *zstd_crc, *old_evidence[:6]]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, outputs, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-mixed-codec-v2-snappy-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / f"{name}.parquet").write_bytes(wire)
        for name, (_, rows, codecs) in outputs.items():
            lines = [str(codec) + "," + ",".join("null" if val is None else str(val) for val in group)
                     for codec, group in zip(codecs, rows, strict=True)]
            (output / f"{name}.txt").write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(outputs)
        for name, (field, rows, _) in outputs.items():
            VERIFY_IPC((output / f"{name}.arrows").read_bytes(), field, rows)


if __name__ == "__main__":
    main()
