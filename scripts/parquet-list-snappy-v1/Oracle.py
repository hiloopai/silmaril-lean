"""Reproduce native PyArrow pages and a separately assembled Snappy continuation."""

from copy import deepcopy
from dataclasses import dataclass
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
fixture = runpy.run_path(str(HERE.parent / "parquet-list-to-ipc" / "Fixtures.py"))
pa, pq, metadata, parse, page, footer, compact = (
    fixture[key] for key in ("pa", "pq", "metadata", "parse", "page", "footer", "compact")
)
level_helpers = runpy.run_path(str(HERE.parent / "parquet-list-continuation" / "Oracle.py"))
section = level_helpers["section"]
SNAPPY = pa.Codec("snappy")
SCHEMA = pa.schema([pa.field("items", pa.list_(pa.field("element", pa.int32())))])
NATIVE = [[None, [], [-(1 << 31)] * 7 + [None], [(1 << 31) - 1, None]],
          [None, [], [-7, None], [0, None]]]
CONTINUED = [NATIVE[0], [None, [], [-7, None, 0, None]]]


@dataclass
class Frame:
    offset: int
    payload: int
    stop: int
    header: dict
    body: bytes


def checksum(body):
    crc = zlib.crc32(body)
    return crc if crc < 1 << 31 else crc - (1 << 32)


def produce(path, checksums):
    values = pa.array([row for group in NATIVE for row in group], type=SCHEMA.field(0).type)
    pq.write_table(pa.table({"items": values}, schema=SCHEMA), path, compression="SNAPPY",
                   use_dictionary=False, data_page_version="1.0", write_statistics=False,
                   write_page_checksum=checksums, row_group_size=4, write_batch_size=1,
                   max_rows_per_page=1, data_page_size=1)
    return path.read_bytes()


def page_frames(source, meta, footer_start):
    result = []
    next_chunk = 4
    for group in meta[4]:
        [chunk] = group[1]
        column = chunk[3]
        assert column[1] == 1 and column[3] == [b"items", b"list", b"element"] and column[4] == 1
        cursor, stop = column[9], column[9] + column[7]
        assert cursor == next_chunk and cursor < stop <= footer_start
        next_chunk = stop
        frames = []
        while cursor < stop:
            header, length = parse(source[cursor:stop], page)
            payload = cursor + length
            end = payload + header[3]
            assert payload < end <= stop
            assert header[1] == 0 and set(header).issubset({1, 2, 3, 4, 5})
            assert header[5] == {1: header[5][1], 2: 0, 3: 3, 4: 3}
            frames.append(Frame(cursor, payload, end, header, source[payload:end]))
            cursor = end
        assert sum(frame.header[5][1] for frame in frames) == column[5]
        result.append(frames)
    assert next_chunk == footer_start
    return result


def wire(frame):
    body = SNAPPY.decompress(frame.body, frame.header[2]).to_pybytes()
    count = frame.header[5][1]
    reps, at, rep_value = section(body, 0, 1, count)
    defs, at, _ = section(body, at, 2, count)
    values = [value for (value,) in struct.iter_unpack("<i", body[at:])]
    return body, rep_value, reps, defs, values


def altered(source, replacements, removed_row):
    """Reserialize only the supported footer fields and replace selected frames."""
    footer_start, original = metadata(source)
    meta = deepcopy(original)
    data = bytearray(b"PAR1")
    if removed_row is not None:
        meta[3] -= 1
        meta[4][removed_row][3] -= 1
    for ordinal, (group, frames) in enumerate(zip(meta[4], page_frames(source, original, footer_start), strict=True)):
        [chunk] = group[1]
        column = chunk[3]
        column[9] = len(data)
        expanded = 0
        for index, frame in enumerate(frames):
            new_body = replacements.get((ordinal, index))
            if new_body is None:
                header_size = frame.payload - frame.offset
                data.extend(source[frame.offset:frame.stop])
            else:
                header = {**frame.header, 3: len(new_body), 4: checksum(new_body)}
                encoded = compact(page, header)
                header_size = len(encoded)
                data.extend(encoded + new_body)
            expanded += header_size + frame.header[2]
        column[6] = expanded
        column[7] = len(data) - column[9]
        group[2] = expanded
    raw_footer = compact(footer, meta)
    return bytes(data) + raw_footer + struct.pack("<I", len(raw_footer)) + b"PAR1"


def inspect(label, source, expected, checksums, continued):
    footer_start, meta = metadata(source)
    assert meta[2] == [{3: 0, 4: b"schema", 5: 1},
                       {3: 1, 4: b"items", 5: 1, 6: 3, 10: {3: {}}},
                       {3: 2, 4: b"list", 5: 1}, {1: 1, 3: 1, 4: b"element"}]
    assert meta[3] == sum(map(len, expected))
    reader = pq.ParquetFile(BytesIO(source), page_checksum_verification=True)
    assert reader.schema_arrow == SCHEMA
    assert reader.num_row_groups == len(expected)
    assert [reader.read_row_group(i, use_threads=False)[0].to_pylist()
            for i in range(reader.num_row_groups)] == expected
    frames = page_frames(source, meta, footer_start)
    print(f"{label} SHA-256 {sha256(source).hexdigest()}, footer [{footer_start}, {len(source) - 8})")
    for group, pages in enumerate(frames):
        assert len(pages) == 4 and meta[4][group][3] == len(expected[group])
        for index, (frame, row) in enumerate(zip(pages, NATIVE[group], strict=True)):
            if row:
                rep = [int(index > 0) for index in range(len(row))]
                defs = [2 if value is None else 3 for value in row]
                values = [value for value in row if value is not None]
            else:
                rep, defs, values = [0], [0 if row is None else 1], []
            if continued and group == 1 and index == 3:
                rep[0] = 1
            assert frame.header.get(4) == (checksum(frame.body) if checksums else None)
            assert wire(frame)[2:] == (rep, defs, values)
            print(f"  group {group} page {index} [{frame.offset}, {frame.stop}), payload @{frame.payload}, "
                  f"{frame.header[3]} -> {frame.header[2]}, CRC {frame.header.get(4)}, "
                  f"reps {rep}, defs {defs}, PLAIN {values}")
    print(f"  rows {expected}")
    assert frames[0][2].header[3] < frames[0][2].header[2]
    return frames


def make(output):
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    output.mkdir(parents=True, exist_ok=True)
    native = produce(output / "native-crc-v1.parquet", True)
    frames = inspect("native-crc-v1.parquet", native, NATIVE, True, False)
    optional = produce(output / "native-no-crc-v1.parquet", False)
    inspect("native-no-crc-v1.parquet", optional, NATIVE, False, False)
    last = frames[1][3]
    body, rep_value, *_ = wire(last)
    assert body[rep_value] == 2
    continued = body[:rep_value] + bytes([3]) + body[rep_value + 1:]
    authored = altered(native, {(1, 3): SNAPPY.compress(continued).to_pybytes()}, removed_row=1)
    (output / "assembled-continuation-v1.parquet").write_bytes(authored)
    inspect("assembled-continuation-v1.parquet", authored, CONTINUED, True, True)

    # Change a late stored byte and leave its original checksum and headers intact.
    damaged = bytearray(native)
    damaged[last.payload] ^= 0x80
    (output / "mutated-crc-v1.parquet").write_bytes(damaged)
    damaged_meta = metadata(bytes(damaged))
    assert damaged_meta == metadata(native)
    assert checksum(damaged[last.payload:last.stop]) != last.header[4]
    reader = pq.ParquetFile(BytesIO(damaged), page_checksum_verification=True)
    assert reader.read_row_group(0, use_threads=False)[0].to_pylist() == NATIVE[0]
    try:
        reader.read_row_group(1, use_threads=False)
    except OSError as error:
        assert "CRC" in str(error)
    else:
        raise AssertionError("expected the stored CRC to fail")

    # Preserve the early frames and replace the final member and checksum.
    malformed = altered(native, {(1, 3): b"\x80"}, removed_row=None)
    (output / "assembled-malformed-v1.parquet").write_bytes(malformed)
    stop, meta = metadata(malformed)
    bad = page_frames(malformed, meta, stop)[1][3]
    assert bad.header[4] == checksum(bad.body)
    try:
        SNAPPY.decompress(bad.body, bad.header[2])
    except OSError as error:
        assert "Corrupt snappy compressed data" in str(error)
    else:
        raise AssertionError("expected the malformed raw Snappy member to fail")

    # A syntactically valid repeated element is illegal at a group boundary.
    first = frames[1][0]
    initial_body = wire(first)[0]
    first_rep = wire(first)[1]
    first_def = section(initial_body, 0, 1, 1)[1]
    def_value = section(initial_body, first_def, 2, 1)[2]
    new_body = bytearray(initial_body)
    new_body[first_rep] = 1
    new_body[def_value] = 2
    leading = altered(native, {(1, 0): SNAPPY.compress(bytes(new_body)).to_pybytes()}, removed_row=None)
    (output / "assembled-leading-v1.parquet").write_bytes(leading)
    return frames


def run(directory):
    directory = directory.resolve()
    frames = make(directory)
    driver = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
              "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
    for name, rows in (("native-crc-v1", NATIVE), ("native-no-crc-v1", NATIVE),
                       ("assembled-continuation-v1", CONTINUED)):
        source = directory / f"{name}.parquet"
        assert source.read_bytes() == (ROOT / "data/parquet-list-snappy-v1" / source.name).read_bytes()
        output = directory / f"{name}.arrows"
        subprocess.run([*driver, "write", str(source), str(output)], cwd=ROOT, check=True)
        ipc = output.read_bytes()
        with pa.ipc.open_stream(ipc) as reader:
            assert reader.schema == SCHEMA
            batches = list(reader)
            assert [batch.column(0).to_pylist() for batch in batches] == rows
            for batch in batches:
                batch.validate(full=True)
        messages = list(pa.ipc.MessageReader.open_stream(ipc))
        assert [m.type for m in messages] == ["schema", "record batch", "record batch"]
        assert all(m.metadata_version == pa.ipc.MetadataVersion.V5 for m in messages)
        used = sum(8 + m.metadata.size + (m.body.size if m.body else 0) for m in messages)
        assert ipc[used:] == bytes.fromhex("ff ff ff ff 00 00 00 00")
        print(f"{output.name} SHA-256 {sha256(ipc).hexdigest()}, EOS [{used}, {len(ipc)}), rows {rows}")
    last_offset = frames[1][3].offset
    remaining_cap = sum(frame.header[2] for group in frames for frame in group) - 1
    controls = [("crc", "mutated-crc-v1", last_offset, 0),
                ("payload", "assembled-malformed-v1", last_offset, 0),
                ("leading", "assembled-leading-v1", frames[1][0].offset, 0),
                ("budget", "native-crc-v1", last_offset, remaining_cap)]
    for label, name, offset, cap in controls:
        source = directory / f"{name}.parquet"
        print(f"{label} control SHA-256 {sha256(source.read_bytes()).hexdigest()}")
        verdict = subprocess.check_output(
            [*driver, "refuse", label, str(source), str(offset), str(cap)], cwd=ROOT, text=True
        )
        print(verdict.strip())


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--fixtures":
        make(Path(sys.argv[2]))
    else:
        run(Path(sys.argv[1]))
