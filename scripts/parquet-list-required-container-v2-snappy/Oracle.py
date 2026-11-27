"""Pinned PyArrow Snappy V2 required LIST and checked controls."""

from copy import deepcopy
from hashlib import sha256
from io import BytesIO
import os
from pathlib import Path
import runpy
import struct
import subprocess
import sys
import zlib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
v2 = runpy.run_path(str(HERE.parent / "parquet-list-required-container-v2" / "Oracle.py"))
pa, pq, SCHEMA, metadata, frame_at, hybrid, replace_last = (
    v2[key] for key in ("pa", "pq", "SCHEMA", "metadata", "frame_at", "hybrid", "replace_last")
)
GROUPS = [v2["GROUPS"][0], [[None, None], [], [7] * 72 + [None] + [-2147483648] * 32, [2147483647]]]


def crc(body):
    return struct.unpack("<i", struct.pack("<I", zlib.crc32(body)))[0]


def produce(path, checksums):
    values = pa.array(sum(GROUPS, []), type=SCHEMA.field(0).type)
    pq.write_table(pa.table({"items": values}, schema=SCHEMA), path,
                   compression="SNAPPY", use_dictionary=False, data_page_version="2.0",
                   write_statistics=False, write_page_checksum=checksums, row_group_size=4)
    return path.read_bytes()


def inspect(label, raw, checksums, default_flag=False):
    footer_at, meta = metadata(raw)
    assert meta[3] == 8
    assert meta[2] == [{3: 0, 4: b"schema", 5: 1},
                       {3: 0, 4: b"items", 5: 1, 6: 3, 10: {3: {}}},
                       {3: 2, 4: b"list", 5: 1}, {1: 1, 3: 1, 4: b"element"}]
    reader = pq.ParquetFile(BytesIO(raw), page_checksum_verification=True)
    assert reader.schema_arrow == SCHEMA and reader.num_row_groups == len(GROUPS)
    assert reader.schema.column(0).max_repetition_level == 1
    assert reader.schema.column(0).max_definition_level == 2
    print(f"{label} SHA-256 {sha256(raw).hexdigest()}, footer [{footer_at}, {len(raw) - 8})")
    end, pages = 4, []
    for index, (group, expected) in enumerate(zip(meta[4], GROUPS, strict=True)):
        [chunk] = group[1]
        col = chunk[3]
        start = col[9]
        assert start == end and col[1] == 1 and set(col[2]) == {0, 3}
        assert col[3] == [b"items", b"list", b"element"] and col[4] == 1 and 11 not in col
        end = start + col[7]
        frame = frame_at(raw, start, end)
        h = frame.header[8]
        assert frame.header[1] == 3 and h[4] == 0
        assert col[6] == group[2] == frame.payload - frame.offset + frame.header[2]
        assert frame.header.get(4) == (crc(frame.body) if checksums else None)
        assert (7 not in h) == (default_flag and index == 1)
        assert h.get(7, True) == (index == 1)
        rep_end = frame.payload + h[6]
        def_end = rep_end + h[5]
        assert frame.payload <= rep_end <= def_end <= end <= footer_at
        reps = hybrid(raw[frame.payload:rep_end], 1, h[1])
        defs = hybrid(raw[rep_end:def_end], 2, h[1])
        suffix = raw[def_end:end]
        physical_bytes = frame.header[2] - h[5] - h[6]
        expanded = pa.Codec("snappy").decompress(suffix, physical_bytes).to_pybytes() if h.get(7, True) else suffix
        assert len(expanded) == physical_bytes
        values = [value for (value,) in struct.iter_unpack("<i", expanded)]
        assert reps[0] == 0 and reps.count(0) == h[3] == group[3] == len(expected)
        assert h[1] == col[5] == len(reps) == len(defs)
        assert h[2] == defs.count(0) + defs.count(1) and len(values) == h[1] - h[2] == defs.count(2)
        rows, ordered = [], iter(values)
        for r, d in zip(reps, defs, strict=True):
            if r == 0:
                rows.append([])
            else:
                assert d > 0 and rows[-1]
            if d > 0:
                rows[-1].append(None if d == 1 else next(ordered))
        assert rows == expected == reader.read_row_group(index)[0].to_pylist()
        print(f"  group {index} page 0 @{start}, crc {frame.header.get(4, 'absent')}, "
              f"slots/rows/nulls {h[1]}/{h[3]}/{h[2]}, flag {h.get(7, 'default true')}, "
              f"rep [{frame.payload}, {rep_end}), def [{rep_end}, {def_end}), "
              f"suffix [{def_end}, {end}) -> {len(expanded)} raw bytes")
        pages.append((frame, def_end))
    assert end == footer_at
    return pages


def controls(raw, pages):
    for label, group, mutate_level in (("raw-crc", 0, False), ("level-crc", 1, True), ("snappy-crc", 1, False)):
        frame, def_end = pages[group]
        offset = frame.payload if mutate_level else def_end
        changed = bytearray(raw)
        changed[offset] ^= 128
        assert crc(changed[frame.payload:frame.stop]) != frame.header[4]
        reader = pq.ParquetFile(BytesIO(changed), page_checksum_verification=True)
        if group:
            assert reader.read_row_group(0)[0].to_pylist() == GROUPS[0]
        try:
            reader.read_row_group(group)
        except OSError as error:
            assert "CRC" in str(error)
        else:
            raise AssertionError("expected stored CRC mismatch")
        yield "mutated", label, bytes(changed), group, frame.offset

    frame, def_end = pages[1]
    for label in ("header-rows", "header-nulls", "header-slots", "raw-flag", "bad-snappy"):
        header, body = deepcopy(frame.header), frame.body
        h = header[8]
        if label == "header-rows":
            h[3] -= 1
        elif label == "header-nulls":
            h[2] -= 1
        elif label == "header-slots":
            h[1] += 1
        elif label == "raw-flag":
            h[7] = False
        else:
            level_bytes = def_end - frame.payload
            body = body[:level_bytes] + bytes([255]) * (len(body) - level_bytes)
            header[4] = crc(body)
        changed = replace_last(raw, frame, header, body)
        parsed = frame_at(changed, frame.offset, metadata(changed)[0])
        assert parsed.header == header and parsed.header[4] == crc(parsed.body)
        yield "assembled", label, changed, 1, frame.offset


def check_ipc(driver, source):
    output = source.with_suffix(".arrows")
    subprocess.run([*driver, "write", str(source), str(output)], cwd=ROOT, check=True)
    wire = output.read_bytes()
    with pa.ipc.open_stream(wire) as reader:
        assert reader.schema == SCHEMA
        assert [batch.column(0).to_pylist() for batch in reader] == GROUPS
    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert [m.type for m in messages] == ["schema", "record batch", "record batch"]
    assert all(m.metadata_version == pa.ipc.MetadataVersion.V5 for m in messages)
    eos = sum(8 + m.metadata.size + (m.body.size if m.body else 0) for m in messages)
    assert wire[eos:] == bytes.fromhex("ff ff ff ff 00 00 00 00")
    print(f"{output.name} SHA-256 {sha256(wire).hexdigest()}, exact EOS [{eos}, {len(wire)})")


def run(out, generate):
    out = out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    print(f"PyArrow {pa.__version__}")
    crc_path = out / "native-required-v2-snappy-crc.parquet"
    plain_path = out / "native-required-v2-snappy-no-crc.parquet"
    native = produce(crc_path, True)
    pages = inspect(crc_path.name, native, True)
    inspect(plain_path.name, produce(plain_path, False), False)

    tail = pages[1][0]
    header = deepcopy(tail.header)
    assert header[8].pop(7) is True
    default_path = out / "assembled-default-flag-v2-snappy.parquet"
    default_path.write_bytes(replace_last(native, tail, header, tail.body))
    inspect(default_path.name, default_path.read_bytes(), True, default_flag=True)
    if generate:
        return

    for path in (crc_path, plain_path):
        assert path.read_bytes() == (ROOT / "data/parquet-list-required-container-v2-snappy" / path.name).read_bytes()
    driver = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
              "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
    for path in (crc_path, plain_path, default_path):
        check_ipc(driver, path)
    for provenance, label, changed, group, offset in controls(native, pages):
        path = out / f"{provenance}-{label}.parquet"
        path.write_bytes(changed)
        print(f"{path.name} SHA-256 {sha256(changed).hexdigest()}")
        cmd = [*driver, "refuse", label, str(path), str(group), str(offset)]
        print(subprocess.check_output(cmd, cwd=ROOT, text=True).strip())


if __name__ == "__main__":
    run(Path(sys.argv[1]), sys.argv[2:] == ["generate"])
