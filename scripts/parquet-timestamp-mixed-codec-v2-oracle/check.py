"""Check mixed GZIP/Zstandard TIMESTAMP V2 using original PyArrow chunks."""

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
import pyarrow.parquet as pq

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
GZIP = runpy.run_path(str(HERE.parent / "parquet-timestamp-gzip-dispatch-v2-oracle/check.py"))
ZSTD = runpy.run_path(str(HERE.parent / "parquet-timestamp-zstd-dispatch-v2-oracle/check.py"))
THRIFT, MIXED = GZIP["THRIFT"], GZIP["MIXED"]
CRC, READ_GROUP, VERIFY_IPC = (GZIP["GZIP"][name] for name in ("corrupt_frame_crc", "read_group", "verify_ipc"))


def selected_frames(wire, group, column=1):
    metadata = THRIFT["column_metadata"](MIXED["metadata"](wire), group, column)
    start, stop = MIXED["column_extent"](metadata)
    return metadata, list(GZIP["frames"](wire, start, stop))


def inspect_assembly(wire, field, parts, rows):
    native = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert native.num_row_groups == len(parts) and native.schema_arrow.field(1).equals(field)
    captures = []
    for index, ((source, original, codec, profile), slots) in enumerate(zip(parts, rows, strict=True)):
        metadata, frames = selected_frames(wire, index)
        source_metadata, source_frames = selected_frames(source, original)
        assert metadata[4] == source_metadata[4] and metadata[4][1] == codec
        assert len(frames) == len(source_frames) and metadata[5][1] == len(slots)
        name = {2: "GZIP", 6: "ZSTD"}[codec]
        assert native.metadata.row_group(index).column(1).compression == name
        assert READ_GROUP(native, index) == slots
        for assembled, old in zip(frames, source_frames, strict=True):
            assert (assembled[1], assembled[2] - assembled[0], assembled[3]) == (old[1], old[2] - old[0], old[3])
        if codec == 6:
            assert native.metadata.row_group(index).column(0).compression == "UNCOMPRESSED"
        dictionary = frames[0] if profile != "plain" else None
        data = frames[1:] if dictionary is not None else frames
        if dictionary is not None:
            assert dictionary[1][1][1] == 2 and dictionary[1][7][1][2][1] == 0
            assert dictionary[0] == metadata[11][1]
        else:
            assert 11 not in metadata
        assert all(frame[1][1][1] == 3 for frame in data) and data[0][0] == metadata[9][1]
        tags = [frame[1][8][1][4][1] for frame in data]
        assert tags == sorted(tags, reverse=True)
        assert set(tags) == {"plain": {0}, "references": {8}, "fallback": {8, 0}}[profile]
        print(f"{field.type} group {index}: codec {codec}, {profile}, original tags {tags}")
        captures.append((dictionary, data))
    return captures


def assert_bad_crc(wire, group, rows, column="ticks"):
    source = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert [READ_GROUP(source, before) for before in range(group)] == rows[:group]
    try:
        source.read_row_group(group, columns=[column], use_threads=False)
    except (pa.ArrowException, OSError) as error:
        assert "crc" in str(error).lower(), str(error)
    else:
        raise AssertionError("PyArrow accepted damaged stored data")


def cases():
    gzip_files, gzip_cases, _ = GZIP["positives"]()
    zstd_files, zstd_cases, _ = ZSTD["fixtures"]()
    gzip_pins = json.loads((GZIP["HERE"] / "fixtures.json").read_text())
    zstd_pins = json.loads((ZSTD["HERE"] / "fixtures.json").read_text())
    outputs, wires, originals, picked, captures = {}, {}, {}, {}, {}
    for name in ("utc", "local"):
        g_native = f"native_{name}"
        g_plain = f"plain_{name}_producer"
        for codec, files, pins in (("gzip", gzip_files, gzip_pins), ("zstd", zstd_files, zstd_pins)):
            for key in (g_native, g_plain):
                value = sha256(files[key]).hexdigest()
                assert value == pins[key]
                originals[f"{codec}_{key}"] = value
        field, gzip_rows, _, _ = gzip_cases[g_native]
        z_field, zstd_rows, _, _ = zstd_cases[g_native]
        assert field.equals(z_field)
        gzip_plain = gzip_cases[f"assembled_{name}"][1][1]
        zstd_plain = zstd_cases[f"assembled_{name}"][1][1]
        with_rows = [
            (gzip_files[g_native], 0, 2, "references", gzip_rows[0]),
            (zstd_files[g_plain], 0, 6, "plain", zstd_plain),
            (gzip_files[g_native], 1, 2, "fallback", gzip_rows[1]),
            (zstd_files[g_native], 2, 6, "references", zstd_rows[2]),
            (gzip_files[g_plain], 0, 2, "plain", gzip_plain),
            (zstd_files[g_native], 3, 6, "fallback", zstd_rows[3]),
        ]
        if name == "local":
            with_rows.reverse()
        parts = [entry[:4] for entry in with_rows]
        rows = [entry[4] for entry in with_rows]
        wire = GZIP["assemble"]([(source, ordinal) for source, ordinal, _, _ in parts])
        label = f"mixed_{name}"
        wires[label] = wire
        outputs[label] = field, rows, [part[2] for part in parts]
        captures[label] = inspect_assembly(wire, field, parts, rows)
        picked[name] = parts

    good = wires["mixed_utc"]
    field, rows, codecs = outputs["mixed_utc"]
    gzip_ref = captures["mixed_utc"][2][1][0]
    zstd_dict = captures["mixed_utc"][3][0]
    wires["bad_gzip_crc"], gzip_evidence = CRC(good, gzip_ref)
    wires["bad_zstd_crc"], zstd_evidence = CRC(good, zstd_dict)
    wires["competing_crc"], _ = CRC(wires["bad_zstd_crc"], gzip_ref)
    for name, index in (("bad_gzip_crc", 2), ("bad_zstd_crc", 3), ("competing_crc", 2)):
        assert_bad_crc(wires[name], index, rows)
    _, decoy = selected_frames(good, 1, 0)
    wires["damaged_decoy"], _ = CRC(good, decoy[0])
    assert_bad_crc(wires["damaged_decoy"], 1, rows, "decoy")
    decoy_file = pq.ParquetFile(pa.BufferReader(wires["damaged_decoy"]), page_checksum_verification=True)
    assert [READ_GROUP(decoy_file, i) for i in range(len(rows))] == rows
    outputs["damaged_decoy"] = field, rows, codecs

    first = [(source, index) for source, index, _, _ in picked["utc"][:2]]
    snappy = GZIP["produce"](field, rows[2:3], dictionary=False, checksum=True, codec="SNAPPY")
    wires["late_snappy"] = GZIP["assemble"](first + [(snappy, 0)])
    assert selected_frames(wires["late_snappy"], 2)[0][4][1] == 1
    gzip_v1 = GZIP["produce"](field, rows[2:3], dictionary=False, checksum=True, page_version="1.0")
    zstd_v1 = ZSTD["PLAIN"]["produce"](field, rows[2:3], checksum=True, pages="1.0")
    v1_evidence = []
    for label, source, codec in (("late_gzip_v1", gzip_v1, 2), ("late_zstd_v1", zstd_v1, 6)):
        wires[label] = GZIP["assemble"](first + [(source, 0)])
        metadata, original = selected_frames(wires[label], 2)
        assert original[0][1][1][1] == 0 and metadata[4][1] == codec
        v1_evidence.append(original[0][0])
    for label in ("late_snappy", "late_gzip_v1", "late_zstd_v1"):
        parquet = pq.ParquetFile(pa.BufferReader(wires[label]), page_checksum_verification=True)
        assert [READ_GROUP(parquet, i) for i in range(3)] == rows[:3]
    return wires, outputs, originals, [*gzip_evidence, *zstd_evidence, *v1_evidence]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires, outputs, originals, evidence = cases()
    hashes = {"producers": originals, "assemblies_and_controls": {name: sha256(wire).hexdigest()
                                                                for name, wire in wires.items()}}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), json.dumps(hashes, indent=2)

    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-mixed-codec-v2-") as temporary:
        output = Path(temporary)
        for name, wire in wires.items():
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
