"""Native multipage Snappy V2 required LIST, independent wire trace and controls."""

from copy import deepcopy
from hashlib import sha256
from io import BytesIO
import os
from pathlib import Path
import runpy
import struct
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
snappy = runpy.run_path(str(HERE.parent / "parquet-list-required-container-v2-snappy" / "Oracle.py"))
multi = runpy.run_path(str(HERE.parent / "parquet-list-required-container-v2-multi" / "Oracle.py"))
pa, pq, SCHEMA, metadata, hybrid, replace_last, crc = (
    snappy[key] for key in ("pa", "pq", "SCHEMA", "metadata", "hybrid", "replace_last", "crc")
)
frame_at = multi["frame_at"]
GROUPS = [snappy["GROUPS"][0], [[None, None], [], [2147483647], [7] * 72 + [None] + [-2147483648] * 32]]


def produce(path, checksums):
    values = pa.array(sum(GROUPS, []), type=SCHEMA.field(0).type)
    pq.write_table(pa.table({"items": values}, schema=SCHEMA), path, compression="SNAPPY", use_dictionary=False,
                   data_page_version="2.0", write_statistics=False, write_page_checksum=checksums,
                   row_group_size=4, write_batch_size=1, data_page_size=1, max_rows_per_page=2)
    return path.read_bytes()


def inspect(label, raw, checksums, default_flag=False):
    footer_at, meta = metadata(raw)
    assert meta[3] == 8
    assert meta[2] == [{3: 0, 4: b"schema", 5: 1},
                       {3: 0, 4: b"items", 5: 1, 6: 3, 10: {3: {}}},
                       {3: 2, 4: b"list", 5: 1}, {1: 1, 3: 1, 4: b"element"}]
    reader = pq.ParquetFile(BytesIO(raw), page_checksum_verification=True)
    assert reader.schema_arrow == SCHEMA and reader.num_row_groups == 2
    assert reader.schema.column(0).max_repetition_level == 1
    assert reader.schema.column(0).max_definition_level == 2
    print(f"{label} SHA-256 {sha256(raw).hexdigest()}, footer [{footer_at}, {len(raw) - 8})")
    end, frames = 4, []
    for ordinal, (group, expected) in enumerate(zip(meta[4], GROUPS, strict=True)):
        [chunk] = group[1]
        col = chunk[3]
        cursor = col[9]
        assert col[1] == 1 and set(col[2]) == {0, 3}
        assert col[3] == [b"items", b"list", b"element"] and col[4] == 1 and 11 not in col
        assert cursor == end
        end = cursor + col[7]
        assert end <= footer_at
        rows, headers, expanded_total = [], [], 0
        while cursor < end:
            frame = frame_at(raw, cursor, end)
            h = frame.header[8]
            assert frame.header[1] == 3 and h[4] == 0
            assert frame.header.get(4) == (crc(frame.body) if checksums else None)
            compressed = ordinal == 1 and len(headers) == 2
            assert (7 not in h) == (default_flag and compressed) and h.get(7, True) == compressed
            rep_end = frame.payload + h[6]
            def_end = rep_end + h[5]
            assert frame.payload <= rep_end <= def_end <= frame.stop
            reps = hybrid(raw[frame.payload:rep_end], 1, h[1])
            defs = hybrid(raw[rep_end:def_end], 2, h[1])
            suffix = raw[def_end:frame.stop]
            physical = frame.header[2] - h[5] - h[6]
            expanded = pa.Codec("snappy").decompress(suffix, physical).to_pybytes() if compressed else suffix
            assert len(expanded) == physical
            scalars = [value for (value,) in struct.iter_unpack("<i", expanded)]
            assert h[1] == len(reps) == len(defs)
            assert reps[0] == 0 and reps.count(0) == h[3]
            assert h[2] == defs.count(0) + defs.count(1)
            assert len(scalars) == defs.count(2) == h[1] - h[2]
            page_rows, ordered = [], iter(scalars)
            for r, d in zip(reps, defs, strict=True):
                if r == 0:
                    page_rows.append([])
                else:
                    assert r == 1 and d > 0 and page_rows[-1]
                if d > 0:
                    page_rows[-1].append(None if d == 1 else next(ordered))
            assert len(page_rows) == h[3]
            print(f"  group {ordinal} page {len(headers)} @{cursor}, crc {frame.header.get(4, 'absent')}, "
                  f"slots/rows/nulls {h[1]}/{h[3]}/{h[2]}, flag {h.get(7, 'default true')}, "
                  f"rep [{frame.payload}, {rep_end}), def [{rep_end}, {def_end}), "
                  f"suffix [{def_end}, {frame.stop}) -> {len(expanded)} raw bytes")
            frames.append((frame, rep_end, def_end))
            headers.append(h)
            rows.extend(page_rows)
            expanded_total += frame.payload - cursor + frame.header[2]
            cursor = frame.stop
        assert cursor == end and len(headers) == 3 and expanded_total == col[6] == group[2]
        assert sum(h[1] for h in headers) == col[5] == [7, 109][ordinal]
        assert sum(h[3] for h in headers) == group[3] == 4
        assert sum(h[2] for h in headers) == [3, 4][ordinal]
        assert rows == expected == reader.read_row_group(ordinal)[0].to_pylist()
    assert end == footer_at
    return frames


def controls(raw, frames):
    for label, page, level in (("raw-crc", 1, False), ("level-crc", 2, True), ("snappy-crc", 2, False)):
        frame, _, def_end = frames[3 + page]
        changed = bytearray(raw)
        changed[frame.payload if level else def_end] ^= 128
        assert crc(changed[frame.payload:frame.stop]) != frame.header[4]
        reader = pq.ParquetFile(BytesIO(changed), page_checksum_verification=True)
        assert reader.read_row_group(0)[0].to_pylist() == GROUPS[0]
        try:
            reader.read_row_group(1)
        except OSError as error:
            assert "CRC" in str(error)
        else:
            raise AssertionError("expected original stored CRC mismatch")
        yield "mutated", label, bytes(changed), page, frame.offset

    changed = bytearray(raw)
    for frame, _, def_end in frames[-2:]:
        changed[def_end] ^= 128
        assert crc(changed[frame.payload:frame.stop]) != frame.header[4]
    yield "mutated", "two-crcs", bytes(changed), 1, frames[-2][0].offset

    frame, rep_end, def_end = frames[-1]
    for label in ("page-rows", "page-nulls", "page-slots", "raw-flag", "bad-snappy", "bad-level", "late-continuation"):
        header, body = deepcopy(frame.header), frame.body
        h = header[8]
        if label == "page-rows":
            h[3] = 0
        elif label == "page-nulls":
            h[2] = 0
        elif label == "page-slots":
            h[1] += 1
        elif label == "raw-flag":
            h[7] = False
        elif label == "bad-snappy":
            level_bytes = def_end - frame.payload
            body = body[:level_bytes] + bytes([255]) * (len(body) - level_bytes)
        elif label == "bad-level":
            body = bytes([body[0] ^ 128]) + body[1:]
        else:
            rep_bytes = rep_end - frame.payload
            assert body[0] == 3 and body[1] & 1 == 0
            body = bytes([body[0], body[1] | 1]) + body[2:]
            assert hybrid(body[:rep_bytes], 1, h[1]) == [1] * h[1]
        header[4] = crc(body)
        changed = replace_last(raw, frame, header, body)
        parsed = frame_at(changed, frame.offset, metadata(changed)[0])
        assert parsed.header == header and parsed.header[4] == crc(parsed.body)
        yield "assembled", label, changed, 2, frame.offset


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
    crc_path = out / "native-required-v2-snappy-multi-crc.parquet"
    plain_path = out / "native-required-v2-snappy-multi-no-crc.parquet"
    native = produce(crc_path, True)
    frames = inspect(crc_path.name, native, True)
    inspect(plain_path.name, produce(plain_path, False), False)
    if generate:
        return
    for path in (crc_path, plain_path):
        assert path.read_bytes() == (ROOT / "data" / HERE.name / path.name).read_bytes()

    tail = frames[-1][0]
    header = deepcopy(tail.header)
    assert header[8].pop(7) is True
    default_path = out / "assembled-default-flag.parquet"
    default_path.write_bytes(replace_last(native, tail, header, tail.body))
    inspect(default_path.name, default_path.read_bytes(), True, default_flag=True)
    driver = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
              "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
    for path in (crc_path, plain_path, default_path):
        check_ipc(driver, path)
    for provenance, label, changed, page, offset in controls(native, frames):
        path = out / f"{provenance}-{label}.parquet"
        path.write_bytes(changed)
        print(f"{path.name} SHA-256 {sha256(changed).hexdigest()}")
        cmd = [*driver, "refuse", label, str(path), str(page), str(offset)]
        print(subprocess.check_output(cmd, cwd=ROOT, text=True).strip())


if __name__ == "__main__":
    run(Path(sys.argv[1]), sys.argv[2:] == ["generate"])
