"""Pinned native PyArrow Snappy dictionary V2 LIST files and labeled controls."""

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
v1 = runpy.run_path(str(HERE.parent / "parquet-list-snappy-dictionary-v1" / "Oracle.py"))
pa, pq, Frame, SNAPPY, SCHEMA, checksum, metadata, footer, compact, compact_header, read_fields, hybrid, expected_entries = (
    v1[name] for name in ("pa", "pq", "Frame", "SNAPPY", "SCHEMA", "checksum", "metadata", "footer",
                         "compact", "compact_header", "read_fields", "hybrid", "expected_entries")
)
FIRST = v1["FIRST"]
SECOND = [[], None, [None, 8, 8], [-11, 8] * 256 + [None, 8]]
NO_ENTRIES = v1["NO_ENTRIES"]
ROWS = [FIRST, SECOND]


def produce(path, groups, checksums):
    values = pa.array([row for group in groups for row in group], type=SCHEMA.field(0).type)
    pq.write_table(pa.table({"items": values}, schema=SCHEMA), path, compression="SNAPPY",
                   use_dictionary=True, data_page_version="2.0", write_statistics=False,
                   write_page_checksum=checksums, row_group_size=4, write_batch_size=1,
                   data_page_size=1, max_rows_per_page=1)
    return path.read_bytes()


def frames_at(raw, start, meta):
    cursor = 4
    result = []
    for group in meta[4]:
        [chunk] = group[1]
        column = chunk[3]
        assert column[1] == 1 and column[3] == [b"items", b"list", b"element"] and column[4] == 1
        assert column[11] == cursor and column[2] == [0, 3, 8]
        stop = cursor + column[7]
        pages = []
        expanded = 0
        while cursor < stop:
            reader = TMemoryBuffer(raw[cursor:stop])
            header = read_fields(TCompactProtocol(reader), (7, 8))
            payload = cursor + reader.cstringio_buf.tell()
            end = payload + header[3]
            assert cursor < payload < end <= stop <= start
            assert header[1] == (3 if pages else 2)
            pages.append(Frame(cursor, payload, end, header, raw[payload:end]))
            expanded += payload - cursor + header[2]
            cursor = end
        assert pages[1].offset == column[9] and expanded == column[6] == group[2]
        assert sum(frame.header[8][1] for frame in pages[1:]) == column[5]
        result.append(pages)
    assert cursor == start
    return result


def data_sections(frame):
    assert frame.header[1] == 3 and frame.header[8][4] == 8
    h = frame.header[8]
    rep, defs = h[6], h[5]
    end = rep + defs
    assert end <= min(frame.header[2], frame.header[3])
    repetitions = hybrid(frame.body[:rep], 1, h[1])
    definitions = hybrid(frame.body[rep:end], 2, h[1])
    expected = frame.header[2] - end
    suffix = frame.body[end:]
    if h.get(7, True):
        suffix = SNAPPY.decompress(suffix, expected).to_pybytes()
    assert len(suffix) == expected and suffix
    return repetitions, definitions, frame.body[:end], suffix


def inspect(label, raw, groups, checksums, absent_flag=False):
    start, meta = metadata(raw)
    assert meta[3] == sum(map(len, groups))
    assert meta[2] == [{3: 0, 4: b"schema", 5: 1},
                       {3: 1, 4: b"items", 5: 1, 6: 3, 10: {3: {}}},
                       {3: 2, 4: b"list", 5: 1}, {1: 1, 3: 1, 4: b"element"}]
    frames = frames_at(raw, start, meta)
    reader = pq.ParquetFile(BytesIO(raw), page_checksum_verification=True)
    assert reader.schema_arrow == SCHEMA and reader.num_row_groups == len(groups)
    assert [reader.read_row_group(i, use_threads=False)[0].to_pylist() for i in range(len(groups))] == groups
    print(f"{label} SHA-256 {sha256(raw).hexdigest()}, footer [{start}, {len(raw) - 8})")
    flags, saw_empty, saw_repeat = set(), False, False
    for group, (pages, expected) in enumerate(zip(frames, groups, strict=True)):
        assert len(pages) == 6
        assert all(p.header.get(4) == (checksum(p.body) if checksums else None) for p in pages)
        dictionary = pages[0]
        words = SNAPPY.decompress(dictionary.body, dictionary.header[2]).to_pybytes()
        entries = [value for (value,) in struct.iter_unpack("<i", words)]
        assert dictionary.header[7] == {1: len(entries), 2: 0, 3: False}
        assert entries == expected_entries(expected) and len(words) == dictionary.header[2] == 4 * len(entries)
        print(f"  group {group} dictionary @{dictionary.offset} payload [{dictionary.payload}, {dictionary.stop}), signed {entries}")
        rows = []
        for index, frame in enumerate(pages[1:], 1):
            h = frame.header[8]
            repetitions, definitions, levels, suffix = data_sections(frame)
            width, *runs = suffix
            indices = hybrid(bytes(runs), width, h[1] - h[2])
            assert not repetitions or repetitions[0] == 0
            assert repetitions.count(0) == h[3] and definitions.count(3) == len(indices)
            assert all(i < len(entries) for i in indices)
            assert (7 not in h) == (absent_flag and (group, index) == (1, 5))
            flags.add(h.get(7, True))
            saw_empty |= h[1] == 0
            saw_repeat |= len(indices) != len(set(indices))
            values = iter(entries[i] for i in indices)
            for repetition, definition in zip(repetitions, definitions, strict=True):
                if repetition == 0:
                    rows.append(None if definition == 0 else [])
                if definition >= 2:
                    rows[-1].append(None if definition == 2 else next(values))
            tail = "…" if len(indices) > 8 else ""
            print(f"  group {group} page {index} @{frame.offset}, rep [{frame.payload}, {frame.payload + h[6]}), "
                  f"def [{frame.payload + h[6]}, {frame.payload + len(levels)}), "
                  f"indices [{frame.payload + len(levels)}, {frame.stop}) -> {len(suffix)} bytes, "
                  f"flag {h.get(7, 'default true')}, slots {h[1]}, rows {h[3]}, nulls {h[2]}, "
                  f"width {width}, indices {indices[:8]}{tail}")
        assert rows == expected and len(rows) == meta[4][group][3]
    assert flags == {True, False} and saw_empty and saw_repeat
    return frames


def replace_last(raw, frame, header, body):
    footer_at, meta = metadata(raw)
    assert frame.stop == footer_at and len(meta[4]) == 2 and header[3] == len(body)
    packed_header = compact_header(header)
    group = meta[4][1]
    column = group[1][0][3]
    header_delta = len(packed_header) - (frame.payload - frame.offset)
    column[7] += header_delta + header[3] - frame.header[3]
    column[6] += header_delta + header[2] - frame.header[2]
    group[2] = column[6]
    packed_footer = compact(footer, meta)
    return raw[:frame.offset] + packed_header + body + packed_footer + struct.pack("<I", len(packed_footer)) + b"PAR1"


def make(out):
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    print(f"PyArrow {pa.__version__}")
    native = produce(out / "native-crc-v2.parquet", ROWS, True)
    frames = inspect("native-crc-v2.parquet", native, ROWS, True)
    optional = produce(out / "native-no-crc-empty-dictionary-v2.parquet", ROWS + [NO_ENTRIES], False)
    inspect("native-no-crc-empty-dictionary-v2.parquet", optional, ROWS + [NO_ENTRIES], False)

    last = frames[1][5]
    header = deepcopy(last.header)
    assert header[8].pop(7) is True
    default = replace_last(native, last, header, last.body)
    (out / "assembled-default-v2.parquet").write_bytes(default)
    inspect("assembled-default-v2.parquet", default, ROWS, True, absent_flag=True)

    _, _, levels, suffix = data_sections(last)
    controls = []
    for label, page, offset in (("dictionary-crc", 0, frames[1][0].payload),
                                ("levels-crc", 5, last.payload),
                                ("indices-crc", 5, last.payload + len(levels))):
        selected = frames[1][page]
        damaged = bytearray(native)
        damaged[offset] ^= 0x80
        assert checksum(damaged[selected.payload:selected.stop]) != selected.header[4]
        reference = pq.ParquetFile(BytesIO(damaged), page_checksum_verification=True)
        assert reference.read_row_group(0, use_threads=False)[0].to_pylist() == FIRST
        try:
            reference.read_row_group(1, use_threads=False)
        except OSError as error:
            assert "CRC" in str(error)
        else:
            raise AssertionError("expected late stored CRC failure")
        controls.append((label, f"mutated-{label}", damaged, page, selected.offset))

    for label in ("geometry", "continued", "page-rows", "page-nulls", "index", "plain-tag"):
        header, body = deepcopy(last.header), last.body
        h = header[8]
        if label == "geometry":
            h[5] = header[3] + 1
        elif label == "continued":
            assert body[:2] == bytes([3, 254])
            body = body[:1] + bytes([255]) + body[2:]
            header[4] = checksum(body)
        elif label == "page-rows":
            h[3] = 2
        elif label == "page-nulls":
            h[2] = 0
        elif label == "plain-tag":
            h[4] = 0
        else:
            actual = hybrid(suffix[1:], suffix[0], h[1] - h[2])
            assert len(actual) == 513
            actual[0] = 2
            word = sum(value << (2 * i) for i, value in enumerate(actual))
            bad = bytes([2, 0x83, 1]) + word.to_bytes(65 * 2, "little")
            assert hybrid(bad[1:], 2, len(actual)) == actual
            body = levels + SNAPPY.compress(bad).to_pybytes()
            header[2], header[3], header[4] = len(levels) + len(bad), len(body), checksum(body)
        controls.append((label, f"assembled-{label}", replace_last(native, last, header, body), 5, last.offset))
    budget = sum(frame.header[2] for group in frames for frame in group) - 1
    return controls, last, budget


def run(out):
    out = out.resolve()
    controls, last, budget = make(out)
    driver = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
              "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
    for name, rows in (("native-crc-v2", ROWS), ("native-no-crc-empty-dictionary-v2", ROWS + [NO_ENTRIES]),
                       ("assembled-default-v2", ROWS)):
        source = out / f"{name}.parquet"
        assert source.read_bytes() == (ROOT / "data/parquet-list-snappy-dictionary-v2" / source.name).read_bytes()
        output = out / f"{name}.arrows"
        subprocess.run([*driver, "write", str(source), str(output)], cwd=ROOT, check=True)
        ipc = output.read_bytes()
        with pa.ipc.open_stream(ipc) as reader:
            assert reader.schema == SCHEMA
            assert [batch.column(0).to_pylist() for batch in reader] == rows
        messages = list(pa.ipc.MessageReader.open_stream(ipc))
        assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(rows)
        assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
        eos = sum(8 + m.metadata.size + (m.body.size if m.body else 0) for m in messages)
        assert ipc[eos:] == bytes.fromhex("ff ff ff ff 00 00 00 00")
        print(f"{output.name} SHA-256 {sha256(ipc).hexdigest()}, EOS [{eos}, {len(ipc)})")
    for label, name, raw, index, offset in controls:
        source = out / f"{name}.parquet"
        source.write_bytes(raw)
        print(f"{source.name} SHA-256 {sha256(raw).hexdigest()}")
        result = subprocess.check_output(
            [*driver, "refuse", label, str(source), str(index), str(offset), "0"], cwd=ROOT, text=True
        )
        print(result.strip())
    result = subprocess.check_output(
        [*driver, "refuse", "budget", str(out / "native-crc-v2.parquet"), "5", str(last.offset), str(budget)],
        cwd=ROOT, text=True
    )
    print(result.strip())


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--fixtures":
        make(Path(sys.argv[2]))
    else:
        run(Path(sys.argv[1]))
