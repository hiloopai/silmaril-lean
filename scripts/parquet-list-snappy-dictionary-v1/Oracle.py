"""Pinned native PyArrow Snappy RLE_DICTIONARY V1 LIST files and controls."""

from copy import deepcopy
from hashlib import sha256
from io import BytesIO
import os
from pathlib import Path
import runpy
import struct
import subprocess
import sys

from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
v2 = runpy.run_path(str(HERE.parent / "parquet-list-snappy-v2" / "Oracle.py"))
pa, pq, Frame, checksum, SNAPPY, SCHEMA, compact_header, read_fields = (
    v2[name] for name in ("pa", "pq", "Frame", "checksum", "SNAPPY", "SCHEMA", "compact_header", "read_fields")
)
wire = runpy.run_path(str(HERE.parent / "parquet-list-to-ipc" / "Fixtures.py"))
record, items, i64, parse, compact = (wire[name] for name in ("record", "items", "i64", "parse", "compact"))
column = record({**wire["column_metadata"][1], 11: i64})
chunk = record({**wire["chunk"][1], 3: column})
footer = {**wire["footer"], 4: items(record({**wire["group"][1], 1: items(chunk)}))}
FIRST = [None, [], [-7, None, -7, (1 << 31) - 1], [-(1 << 31), (1 << 31) - 1, -(1 << 31)]]
SECOND = [[], None, [None, 8, 8], [-11, -11, 8, None]]
NO_ENTRIES = [None, [], [None], [None, None]]
ROWS = [FIRST, SECOND]


def metadata(raw):
    assert raw[:4] == raw[-4:] == b"PAR1"
    end = len(raw) - 8
    size = struct.unpack_from("<I", raw, end)[0]
    start = end - size
    meta, used = parse(raw[start:end], footer)
    assert used == size
    return start, meta


def produce(path, groups, checksums):
    entries = pa.array([row for group in groups for row in group], type=SCHEMA.field(0).type)
    pq.write_table(pa.table({"items": entries}, schema=SCHEMA), path, compression="SNAPPY",
                   data_page_version="1.0", use_dictionary=True, write_statistics=False,
                   write_page_checksum=checksums, row_group_size=4, write_batch_size=1,
                   data_page_size=1, max_rows_per_page=1)
    return path.read_bytes()


def frames_at(raw, start, meta):
    cursor = 4
    result = []
    for group in meta[4]:
        [chunk] = group[1]
        c = chunk[3]
        assert c[1] == 1 and c[3] == [b"items", b"list", b"element"] and c[4] == 1
        assert c[11] == cursor and c[2] == [0, 3, 8]
        stop = cursor + c[7]
        frames = []
        expanded = 0
        while cursor < stop:
            transport = TMemoryBuffer(raw[cursor:stop])
            header = read_fields(TCompactProtocol(transport), (5, 7, 8))
            payload = cursor + transport.cstringio_buf.tell()
            end = payload + header[3]
            assert cursor < payload < end <= stop <= start
            assert header[1] == (0 if frames else 2)
            frames.append(Frame(cursor, payload, end, header, raw[payload:end]))
            expanded += payload - cursor + header[2]
            cursor = end
        assert frames[1].offset == c[9] and expanded == c[6] == group[2]
        assert sum(frame.header[5][1] for frame in frames[1:]) == c[5]
        result.append(frames)
    assert cursor == start
    return result


def hybrid(raw, width, expected):
    values = []
    cursor = 0
    while cursor < len(raw):
        header, shift = 0, 0
        while True:
            digit = raw[cursor]
            cursor += 1
            header |= (digit & 127) << shift
            if digit < 128:
                break
            shift += 7
        count = header >> 1
        assert count > 0
        if header & 1:
            size = count * width
            assert cursor + size <= len(raw)
            word = int.from_bytes(raw[cursor:cursor + size], "little")
            values.extend((word >> (n * width)) & ((1 << width) - 1) for n in range(count * 8))
        else:
            size = (width + 7) // 8
            assert cursor + size <= len(raw)
            value = int.from_bytes(raw[cursor:cursor + size], "little")
            assert value < 1 << width and len(values) + count <= expected
            values.extend([value] * count)
        cursor += size
    assert expected <= len(values) < expected + 8 and all(x == 0 for x in values[expected:])
    return values[:expected]


def data_sections(frame):
    assert frame.header[1] == 0
    count = frame.header[5][1]
    body = SNAPPY.decompress(frame.body, frame.header[2]).to_pybytes()
    rep_size = struct.unpack_from("<I", body)[0]
    at = 4 + rep_size
    def_size = struct.unpack_from("<I", body, at)[0]
    end = at + 4 + def_size
    repetitions = hybrid(body[4:at], 1, count)
    definitions = hybrid(body[at + 4:end], 2, count)
    return repetitions, definitions, body[:end], body[end:]


def expected_entries(rows):
    words = (value for row in rows if row for value in row if value is not None)
    return list(dict.fromkeys(words))


def inspect(label, raw, groups, checksums):
    start, meta = metadata(raw)
    assert meta[3] == sum(map(len, groups))
    assert meta[2] == [{3: 0, 4: b"schema", 5: 1},
                       {3: 1, 4: b"items", 5: 1, 6: 3, 10: {3: {}}},
                       {3: 2, 4: b"list", 5: 1}, {1: 1, 3: 1, 4: b"element"}]
    frames = frames_at(raw, start, meta)
    reader = pq.ParquetFile(BytesIO(raw), page_checksum_verification=True)
    assert reader.schema_arrow == SCHEMA and reader.num_row_groups == len(groups)
    assert [reader.read_row_group(index, use_threads=False)[0].to_pylist()
            for index in range(reader.num_row_groups)] == groups
    print(f"{label} SHA-256 {sha256(raw).hexdigest()}, footer [{start}, {len(raw) - 8})")
    saw_repeat = False
    saw_empty_page = False
    for group, (pages, expected) in enumerate(zip(frames, groups, strict=True)):
        assert len(pages) == 6
        for frame in pages:
            assert frame.header.get(4) == (checksum(frame.body) if checksums else None)
        dictionary = pages[0]
        body = SNAPPY.decompress(dictionary.body, dictionary.header[2]).to_pybytes()
        entries = [value for (value,) in struct.iter_unpack("<i", body)]
        assert dictionary.header[7] == {1: len(entries), 2: 0, 3: False}
        assert entries == expected_entries(expected)
        assert dictionary.header[2] == 4 * len(entries)
        print(f"  group {group} dictionary @{dictionary.offset} payload [{dictionary.payload}, {dictionary.stop}), signed {entries}")
        rows = []
        for index, frame in enumerate(pages[1:], start=1):
            count = frame.header[5][1]
            assert frame.header[5] == {1: count, 2: 8, 3: 3, 4: 3}
            repetitions, definitions, _, suffix = data_sections(frame)
            width, *runs = suffix
            indices = hybrid(bytes(runs), width, definitions.count(3))
            assert all(i < len(entries) for i in indices)
            saw_repeat |= len(set(indices)) < len(indices)
            saw_empty_page |= count == 0
            ordered = iter(entries[i] for i in indices)
            for repetition, definition in zip(repetitions, definitions, strict=True):
                if repetition == 0:
                    rows.append(None if definition == 0 else [])
                if definition >= 2:
                    rows[-1].append(None if definition == 2 else next(ordered))
            print(f"  group {group} page {index} header @{frame.offset} payload [{frame.payload}, {frame.stop}), "
                  f"reps {repetitions}, defs {definitions}, width {width}, indices {indices}")
        assert rows == expected
        assert meta[4][group][3] == len(rows)
    assert saw_repeat and saw_empty_page
    return frames


def assembled(source, replacement, data_offset_delta=0):
    start, meta = metadata(source)
    frames = frames_at(source, start, meta)
    meta = deepcopy(meta)
    data = bytearray(b"PAR1")
    offsets = []
    for ordinal, (group, pages) in enumerate(zip(meta[4], frames, strict=True)):
        col = group[1][0][3]
        col[11] = len(data)
        expanded = 0
        for index, page in enumerate(pages):
            if index == 1:
                col[9] = len(data) + (data_offset_delta if ordinal == 1 else 0)
            if ordinal == 1:
                offsets.append(len(data))
            if (ordinal, index) in replacement:
                header, body = replacement[(ordinal, index)]
                packed = compact_header(header)
                data += packed + body
                expanded += len(packed) + header[2]
            else:
                data += source[page.offset:page.stop]
                expanded += page.payload - page.offset + page.header[2]
        col[6], col[7], group[2] = expanded, len(data) - col[11], expanded
    packed = compact(footer, meta)
    return bytes(data) + packed + struct.pack("<I", len(packed)) + b"PAR1", offsets


def make(out):
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    out.mkdir(parents=True, exist_ok=True)
    print(f"PyArrow {pa.__version__}")
    native = produce(out / "native-crc-v1.parquet", ROWS, True)
    frames = inspect("native-crc-v1.parquet", native, ROWS, True)
    optional = produce(out / "native-no-crc-empty-dictionary-v1.parquet", ROWS + [NO_ENTRIES], False)
    inspect("native-no-crc-empty-dictionary-v1.parquet", optional, ROWS + [NO_ENTRIES], False)
    controls = []
    last = frames[1][5]
    for name, index in (("dictionary-crc", 0), ("data-crc", 5)):
        page = frames[1][index]
        changed = bytearray(native)
        changed[page.payload] ^= 0x80
        assert checksum(changed[page.payload:page.stop]) != page.header[4]
        reader = pq.ParquetFile(BytesIO(changed), page_checksum_verification=True)
        assert reader.read_row_group(0, use_threads=False)[0].to_pylist() == FIRST
        try:
            reader.read_row_group(1, use_threads=False)
        except OSError as error:
            assert "CRC" in str(error)
        else:
            raise AssertionError("expected late CRC rejection")
        controls.append((name, f"mutated-{name}", changed, index, page.offset))

    _, defs, prefix, _ = data_sections(last)
    assert defs.count(3) == 3
    bad_indices = bytes([2, 3, 6, 0])
    assert hybrid(bad_indices[1:], 2, 3) == [2, 1, 0]
    payload = SNAPPY.compress(prefix + bad_indices).to_pybytes()
    header = {**last.header, 2: len(prefix + bad_indices), 3: len(payload), 4: checksum(payload)}
    raw, offsets = assembled(native, {(1, 5): (header, payload)})
    controls.append(("index", "assembled-index", raw, 5, offsets[5]))

    dictionary = frames[1][0]
    count_header = deepcopy(dictionary.header)
    count_header[7][1] += 1
    raw, offsets = assembled(native, {(1, 0): (count_header, dictionary.body)})
    controls.append(("dictionary-count", "assembled-dictionary-count", raw, 0, offsets[0]))

    other = deepcopy(last.header)
    other[5][2] = 0
    raw, offsets = assembled(native, {(1, 5): (other, last.body)})
    controls.append(("plain-tag", "assembled-plain-tag", raw, 5, offsets[5]))

    raw, offsets = assembled(native, {}, data_offset_delta=1)
    controls.append(("data-offset", "assembled-data-offset", raw, 1, offsets[1]))

    budget = sum(frame.header[2] for group in frames for frame in group) - 1
    return controls, frames, budget


def run(out):
    out = out.resolve()
    controls, frames, budget = make(out)
    driver = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
              "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
    for name, rows in (("native-crc-v1", ROWS), ("native-no-crc-empty-dictionary-v1", ROWS + [NO_ENTRIES])):
        source = out / f"{name}.parquet"
        assert source.read_bytes() == (ROOT / "data/parquet-list-snappy-dictionary-v1" / source.name).read_bytes()
        output = out / f"{name}.arrows"
        subprocess.run([*driver, "write", str(source), str(output)], cwd=ROOT, check=True)
        ipc = output.read_bytes()
        with pa.ipc.open_stream(ipc) as reader:
            assert reader.schema == SCHEMA
            assert [batch.column(0).to_pylist() for batch in reader] == rows
        messages = list(pa.ipc.MessageReader.open_stream(ipc))
        assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(rows)
        assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
        eos = sum(8 + message.metadata.size + (message.body.size if message.body else 0) for message in messages)
        assert ipc[eos:] == bytes.fromhex("ff ff ff ff 00 00 00 00")
        print(f"{output.name} SHA-256 {sha256(ipc).hexdigest()}, EOS [{eos}, {len(ipc)})")
    for label, name, raw, index, offset in controls:
        source = out / f"{name}.parquet"
        source.write_bytes(raw)
        print(f"{source.name} SHA-256 {sha256(raw).hexdigest()}")
        verdict = subprocess.check_output(
            [*driver, "refuse", label, str(source), str(index), str(offset), "0"], cwd=ROOT, text=True
        )
        print(verdict.strip())
    verdict = subprocess.check_output(
        [*driver, "refuse", "budget", str(out / "native-crc-v1.parquet"),
         "5", str(frames[1][5].offset), str(budget)], cwd=ROOT, text=True
    )
    print(verdict.strip())


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--fixtures":
        make(Path(sys.argv[2]))
    else:
        run(Path(sys.argv[1]))
