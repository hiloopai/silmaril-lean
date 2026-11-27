"""Compare checked Parquet-to-IPC conversion with pinned PyArrow and Thrift."""

from hashlib import sha256
from io import BytesIO
import os
from pathlib import Path
import struct
import subprocess
import sys

from Fixtures import NATIVE, ROOT, main as fixtures, metadata, pa, page, parse, pq

HERE = Path(__file__).resolve().parent
CONTINUED = ROOT / "data/parquet-list-continuation/authored-continuation-v1.parquet"
FIRST = [None, [], [None], [-7, None, 0], [9, None]]
SECOND = [[10, None], None, [], [None, -(1 << 31)], [(1 << 31) - 1, None]]
EOS = bytes.fromhex("ff ff ff ff 00 00 00 00")
DRIVER = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
          "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]


def leading_rep(body):
    count = struct.unpack_from("<I", body)[0]
    # Each nonempty fixture section is a singleton run or one packed group.
    assert count == 2 and body[4] in (2, 3)
    return body[5] & 1


def inspect_parquet(path, name, expected, repetitions):
    data = path.read_bytes()
    start, meta = metadata(data)
    outer = name.encode()
    assert meta[2][1:] == [{3: 1, 4: outer, 5: 1, 6: 3, 10: {3: {}}},
                           {3: 2, 4: b"list", 5: 1},
                           {1: 1, 3: 1, 4: b"element"}]
    reader = pq.ParquetFile(BytesIO(data))
    assert reader.num_row_groups == len(expected) and meta[3] == sum(map(len, expected))
    assert [reader.read_row_group(i, use_threads=False)[0].to_pylist()
            for i in range(reader.num_row_groups)] == expected
    print(f"{path.name} SHA-256 {sha256(data).hexdigest()}, footer @{start}, {len(expected)} groups")
    for group_index, (group, rows, reps) in enumerate(zip(meta[4], expected, repetitions, strict=True)):
        [chunk] = group[1]
        column = chunk[3]
        assert group[3] == len(rows) and column[1] == 1 and column[3] == [outer, b"list", b"element"]
        assert column[4] == 0
        cursor, end = column[9], column[9] + column[7]
        assert 4 <= cursor < end <= start
        frames, slots, firsts = [], 0, []
        while cursor < end:
            header, size = parse(data[cursor:end], page)
            assert header[1] == 0 and 4 not in header and header[2] == header[3]
            assert [header[5][tag] for tag in (2, 3, 4)] == [0, 3, 3]
            body_start = cursor + size
            stop = body_start + header[3]
            assert cursor < stop <= end
            frames.append((cursor, stop))
            count = header[5][1]
            body = data[body_start:stop]
            if count == 0:
                assert body == bytes(8)
                firsts.append(None)
            else:
                firsts.append(leading_rep(body))
            slots += count
            cursor = stop
        assert cursor == end and slots == column[5] and firsts == reps
        print(f"  group {group_index}: {len(rows)} rows, {slots} slots, frames {frames}, first repetitions {firsts}")


def inspect_ipc(path, name, expected):
    source = path.read_bytes()
    with pa.ipc.open_stream(source) as stream:
        field = pa.field(name, pa.list_(pa.field("element", pa.int32(), nullable=True)), nullable=True)
        assert stream.schema == pa.schema([field])
        batches = list(stream)
    assert [batch.column(0).to_pylist() for batch in batches] == expected
    counts = []
    for batch, rows in zip(batches, expected, strict=True):
        batch.validate(full=True)
        assert batch.num_rows == len(rows)
        children = [value for row in rows if row is not None for value in row]
        assert batch.column(0).values.to_pylist() == children
        counts.append(len(children))
    messages = list(pa.ipc.MessageReader.open_stream(source))
    assert [msg.type for msg in messages] == ["schema"] + ["record batch"] * len(expected)
    assert all(msg.metadata_version == pa.ipc.MetadataVersion.V5 for msg in messages)
    offset = 0
    for msg in messages:
        size = msg.metadata.size
        assert struct.unpack_from("<II", source, offset) == (0xFFFFFFFF, size)
        offset += 8 + size + (msg.body.size if msg.body else 0)
    assert source[offset:] == EOS
    print(f"  IPC SHA-256 {sha256(source).hexdigest()}, child totals {counts}, EOS [{offset}, {len(source)})")
    print(f"  IPC batches {expected}")


def run(output):
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    output = output.resolve()
    generated = output / "sources"
    fixtures(generated)
    print(f"PyArrow {pa.__version__}")
    for name in ("no-groups", "empty-framed-group"):
        stored = ROOT / "data/parquet-list-to-ipc" / f"{name}.parquet"
        assert stored.read_bytes() == (generated / stored.name).read_bytes()
    cases = [
        (NATIVE, "samples", [FIRST, SECOND], [[0], [0]]),
        (CONTINUED, "items", [[None, [], [11, None, 22, None]]], [[0, 0, 0, 1]]),
        (generated / "no-groups.parquet", "samples", [], []),
        (generated / "empty-framed-group.parquet", "samples", [FIRST, [], SECOND], [[0], [None], [0]]),
    ]
    for path, field, batches, reps in cases:
        inspect_parquet(path, field, batches, reps)
        destination = output / f"{path.stem}.arrows"
        subprocess.run([*DRIVER, "write", str(path), str(destination)], cwd=ROOT, check=True)
        inspect_ipc(destination, field, batches)

    native = NATIVE.read_bytes()
    start, meta = metadata(native)
    page_at = meta[4][1][1][0][3][9]
    head, header_size = parse(native[page_at:start], page)
    body_start = page_at + header_size
    assert page_at == 48 and (body_start + 5, native[body_start + 5]) == (72, 0xa2)
    damaged = bytearray(native)
    damaged[72] |= 1
    assert metadata(damaged) == (start, meta) and parse(damaged[page_at:start], page) == (head, header_size)
    assert leading_rep(damaged[body_start:start]) == 1
    late = generated / "late-corruption.parquet"
    late.write_bytes(damaged)
    for mode, path in (("late", late), ("unframed", generated / "unframed-empty.parquet")):
        print(f"{path.name} SHA-256 {sha256(path.read_bytes()).hexdigest()}")
        text = subprocess.check_output([*DRIVER, mode, str(path)], cwd=ROOT, text=True)
        print(text.strip())


if __name__ == "__main__":
    run(Path(sys.argv[1]))
