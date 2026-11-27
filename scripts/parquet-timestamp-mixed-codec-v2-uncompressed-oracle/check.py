"""Compare strict four-codec TIMESTAMP V2 dispatch against pinned producers."""

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
from thrift.Thrift import TType

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
THREE = runpy.run_path(str(HERE.parent / "parquet-timestamp-mixed-codec-v2-snappy-oracle/check.py"))
ZERO = runpy.run_path(str(HERE.parent / "parquet-timestamp-uncompressed-dispatch-v2-oracle/check.py"))
FRAMES, CRC, READ_GROUP, VERIFY_IPC, ASSEMBLE, OPEN, BAD = (
    THREE[name] for name in ("FRAMES", "CRC", "READ_GROUP", "VERIFY_IPC", "ASSEMBLE", "OPEN", "BAD"))
THRIFT = ZERO["THRIFT"]
CODECS = {0: "UNCOMPRESSED", 1: "SNAPPY", 2: "GZIP", 6: "ZSTD"}
PROFILES = {"plain": {0}, "references": {8}, "fallback": {8, 0}}


def pins(corpus):
    return json.loads((corpus["HERE"] / "fixtures.json").read_text())


def stored_chunk(wire, frames):
    _, _, last_body, last_stored = frames[-1]
    return wire[frames[0][0]:last_body + len(last_stored)]


def inspect(wire, field, origins, rows):
    parquet = OPEN(wire)
    assert parquet.num_row_groups == len(origins) and parquet.schema_arrow.field(1).equals(field)
    seen, captures = set(), []
    for index, ((source, group), ticks) in enumerate(zip(origins, rows, strict=True)):
        metadata, frames = FRAMES(wire, index)
        prior_metadata, prior = FRAMES(source, group)
        codec = metadata[4][1]
        assert codec == prior_metadata[4][1] and metadata[5][1] == len(ticks)
        column = parquet.metadata.row_group(index).column(1)
        assert column.compression == CODECS[codec]
        chunk = stored_chunk(wire, frames)
        assert chunk == stored_chunk(source, prior)
        assert len(chunk) == column.total_compressed_size == metadata[7][1]
        if 11 in metadata:
            dictionary, *data = frames
            assert dictionary[0] == metadata[11][1] == column.dictionary_page_offset
            assert dictionary[1][1][1] == 2 and dictionary[1][7][1][2][1] == 0
        else:
            dictionary, data = None, frames
        assert data[0][0] == metadata[9][1] == column.data_page_offset
        assert all(frame[1][1][1] == 3 for frame in data)
        tags = [frame[1][8][1][4][1] for frame in data]
        profile = "plain" if dictionary is None else "fallback" if 0 in tags else "references"
        assert tags == sorted(tags, reverse=True) and set(tags) == PROFILES[profile]
        for _, header, _, stored in frames:
            assert (4 in header) == field.nullable and len(stored) == header[3][1]
            if 4 in header:
                assert zlib.crc32(stored) == header[4][1] % 2**32
            if codec == 0:
                assert len(stored) == header[2][1]
        assert READ_GROUP(parquet, index) == ticks
        seen.add((codec, profile))
        captures.append((dictionary, data))
        print(f"{field.type} group {index}: original codec {codec}, {profile}, tags {tags}")
    assert seen == {(codec, profile) for codec in CODECS for profile in PROFILES}
    return captures


def fixtures():
    old_files, old_outputs, old_evidence = THREE["fixtures"]()
    assert {name: sha256(wire).hexdigest() for name, wire in old_files.items()} == pins(THREE)
    zero_wires, zero_cases = ZERO["producers"]()
    zero_pins = pins(ZERO)
    assert all(sha256(wire).hexdigest() == zero_pins[name] for name, wire in zero_wires.items())

    files, outputs, observed = {}, {}, {}
    for kind in ("utc", "local"):
        prior = f"assembled_three_{kind}"
        original = old_files[prior]
        field, prior_rows, prior_codecs = old_outputs[prior]
        files[f"previous_{kind}"] = original
        outputs[f"previous_{kind}"] = field, prior_rows, prior_codecs
        parts = [(original, index, ticks, codec)
                 for index, (ticks, codec) in enumerate(zip(prior_rows, prior_codecs, strict=True))]
        for mode, index, position in (("plain", 0, 2), ("references", 1, 6), ("fallback", 2, 9)):
            name = f"native_{kind}_{mode}"
            selected_field, profiles, rows = zero_cases[name]
            assert field.equals(selected_field) and profiles[index] == mode
            files[name], outputs[name] = zero_wires[name], (field, rows, [0] * len(rows))
            parts.insert(position, (zero_wires[name], index, rows[index], 0))
        origins = [(wire, index) for wire, index, _, _ in parts]
        rows = [part[2] for part in parts]
        name = f"assembled_four_{kind}"
        files[name] = ASSEMBLE(origins)
        outputs[name] = field, rows, [part[3] for part in parts]
        observed[name] = inspect(files[name], field, origins, rows)

    good = files["assembled_four_utc"]
    _, rows, codecs = outputs["assembled_four_utc"]
    frames = observed["assembled_four_utc"]
    assert codecs[8:] == [1, 0, 2, 6]
    files["mutated_snappy_crc"], snappy = CRC(good, frames[8][1][1])
    files["mutated_uncompressed_crc"], uncompressed = CRC(good, frames[9][1][1])
    files["mutated_gzip_crc"], gzip = CRC(good, frames[10][1][0])
    files["mutated_zstd_crc"], zstd = CRC(good, frames[11][0])
    files["mutated_competing_crc"], _ = CRC(files["mutated_uncompressed_crc"], frames[8][1][1])
    for name, group in (("mutated_snappy_crc", 8), ("mutated_uncompressed_crc", 9),
                        ("mutated_gzip_crc", 10), ("mutated_zstd_crc", 11), ("mutated_competing_crc", 8)):
        BAD(files[name], rows, group, "CRC")

    for codec in ("snappy", "gzip", "zstd"):
        files[f"previous_bad_{codec}_crc"] = old_files[f"mutated_{codec}_crc"]
    files["previous_late_snappy_v1"] = old_files["assembled_late_snappy_v1"]

    def unknown_codec(footer):
        selected = THRIFT["column_metadata"](footer, 6, 1)
        assert selected[4] == (TType.I32, 1)
        selected[4] = TType.I32, 7

    original = files["previous_utc"]
    files["previous_unknown_codec"] = THRIFT["rewrite_footer"](original, unknown_codec)
    assert FRAMES(files["previous_unknown_codec"], 6)[0][4][1] == 7
    assert FRAMES(files["previous_unknown_codec"], 6)[1] == FRAMES(original, 6)[1]
    return files, outputs, [*snappy, *uncompressed, *gzip, *zstd, *old_evidence[:9]]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, outputs, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-mixed-codec-v2-uncompressed-") as temporary:
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
