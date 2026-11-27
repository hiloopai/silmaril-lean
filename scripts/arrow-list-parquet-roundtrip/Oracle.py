"""Check PyArrow IPC -> Lean Parquet -> Lean IPC with PyArrow and Thrift."""

from hashlib import sha256
from io import BytesIO
import os
from pathlib import Path
import runpy
import struct
import subprocess
import sys

from Fixtures import FIELD, main as fixtures, pa

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
o = runpy.run_path(str(HERE.parent / "parquet-list-writer" / "Oracle.py"))
pq, metadata, parse, page, wire, take_levels = (o[n] for n in ("pq", "metadata", "parse", "page", "wire", "take_levels"))
EOS = bytes.fromhex("ff ff ff ff 00 00 00 00")
DRIVER = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
          "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
MIXED = [[None, [], [-7, None, 0], [None]], [], [[], [-(1 << 31), (1 << 31) - 1]]]


def ipc(path, name, child, expected):
    source = path.read_bytes()
    schema = pa.schema([pa.field(name, pa.list_(pa.field(child, pa.int32(), nullable=True)), nullable=True)])
    with pa.ipc.open_stream(source) as reader:
        assert reader.schema == schema
        batches = list(reader)
    assert [batch.column(0).to_pylist() for batch in batches] == expected
    for batch in batches:
        batch.validate(full=True)
    messages = list(pa.ipc.MessageReader.open_stream(source))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(expected)
    assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
    offset = 0
    for message in messages:
        size = message.metadata.size
        assert struct.unpack_from("<II", source, offset) == (0xFFFFFFFF, size)
        offset += 8 + size + (message.body.size if message.body else 0)
    assert source[offset:] == EOS
    children = [len(batch.column(0).values) for batch in batches]
    return children, offset, len(source)


def parquet(path, name, expected):
    source = path.read_bytes()
    start, footer = metadata(source)
    outer = name.encode()
    assert footer[1] == 1 and footer[3] == sum(map(len, expected))
    assert footer[2] == [{4: b"schema", 5: 1},
                         {3: 1, 4: outer, 5: 1, 6: 3, 10: {3: {}}},
                         {3: 2, 4: b"list", 5: 1},
                         {1: 1, 3: 1, 4: b"element"}]
    reader = pq.ParquetFile(BytesIO(source))
    assert reader.schema_arrow.equals(pa.schema([
        pa.field(name, pa.list_(pa.field("element", pa.int32(), nullable=True)), nullable=True),
    ]))
    assert reader.num_row_groups == len(expected)
    assert [reader.read_row_group(i, use_threads=False)[0].to_pylist()
            for i in range(reader.num_row_groups)] == expected
    print(f"  Parquet SHA-256 {sha256(source).hexdigest()}, footer [{start}, {len(source) - 8})")
    offset = 4
    for ordinal, (group, rows) in enumerate(zip(footer[4], expected, strict=True)):
        [chunk] = group[1]
        column = chunk[3]
        reps, defs, values = wire(rows)
        assert group[3] == len(rows) and column[5] == len(reps)
        assert column[1] == 1 and column[2] == [0, 3]
        assert column[3] == [outer, b"list", b"element"] and column[4] == 0
        assert column[9] == offset
        stop = offset + column[7]
        assert offset < stop <= start
        header, used = parse(source[offset:stop], page)
        body = source[offset + used:stop]
        assert column[6] == column[7] == group[2] and header == {
            1: 0, 2: len(body), 3: len(body), 5: {1: len(reps), 2: 0, 3: 3, 4: 3},
        }
        defs_at = take_levels(body, 0, reps)
        values_at = take_levels(body, defs_at, defs)
        assert body[values_at:] == struct.pack("<" + "i" * len(values), *values)
        print(f"  group {ordinal}: frame [{offset}, {stop}), {len(rows)} rows, reps {reps}, defs {defs}, PLAIN {values}")
        offset = stop
    assert offset == start


def run(output):
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    output = output.resolve()
    generated = output / "sources"
    fixtures(generated)
    for name in ("schema-only.arrows", "empty-batch.arrows", "noncanonical-child.arrows"):
        assert (generated / name).read_bytes() == (ROOT / "data/arrow-list-parquet-roundtrip" / name).read_bytes()
    native = ROOT / "data/arrow-list-int32-stream/nullable-list-int32.arrows"
    print(f"PyArrow {pa.__version__}")
    for source, name, expected in [
        (native, "items", MIXED),
        (generated / "schema-only.arrows", FIELD, []),
        (generated / "empty-batch.arrows", FIELD, [[]]),
    ]:
        raw = source.read_bytes()
        children, eos, length = ipc(source, name, "element", expected)
        print(f"{source.name} SHA-256 {sha256(raw).hexdigest()}, {name}/element, children {children}, EOS [{eos}, {length})")
        written = output / f"{source.stem}.parquet"
        returned = output / f"{source.stem}-returned.arrows"
        subprocess.run([*DRIVER, "write", str(source), str(written), str(returned)], cwd=ROOT, check=True)
        parquet(written, name, expected)
        restored, eos, length = ipc(returned, name, "element", expected)
        assert restored == [sum(len(row) for row in batch if row is not None) for batch in expected]
        print(f"  returned IPC SHA-256 {sha256(returned.read_bytes()).hexdigest()}, children {restored}, EOS [{eos}, {length})")
        print(f"  ordered nullable batches {expected}")

    wrong = generated / "noncanonical-child.arrows"
    ipc(wrong, FIELD, "item", [[None, [], [None]], [[-7, None, 9]]])
    late = generated / "late-canonical.arrows"
    late.write_bytes(native.read_bytes()[:-9])
    late_wrong = generated / "late-noncanonical.arrows"
    late_wrong.write_bytes(wrong.read_bytes()[:-9])
    for mode, source in (("child", wrong), ("late", late), ("late-child", late_wrong)):
        print(f"{source.name} SHA-256 {sha256(source.read_bytes()).hexdigest()}")
        answer = subprocess.check_output([*DRIVER, "refuse", mode, str(source)], cwd=ROOT, text=True)
        print(answer.strip())


if __name__ == "__main__":
    run(Path(sys.argv[1]))
