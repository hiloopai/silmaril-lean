"""Read the native LIST writer output with pinned PyArrow and Apache Thrift."""

from hashlib import sha256
from io import BytesIO
import os
from pathlib import Path
import runpy
import struct
import subprocess
import sys

HERE = Path(__file__).resolve().parent
o = runpy.run_path(str(HERE.parent / "parquet-list-to-ipc" / "Fixtures.py"))
pa, pq, parse, metadata, page = (o[name] for name in ("pa", "pq", "parse", "metadata", "page"))
FIELD = "résultats"
FIRST = [None, [], [None], [-7, None, 0], [9, None]]
SECOND = [[-(1 << 31), None, (1 << 31) - 1], None, []]


def wire(rows):
    reps, defs, values = [], [], []
    for row in rows:
        if row is None or row == []:
            reps.append(0)
            defs.append(0 if row is None else 1)
        else:
            for index, slot in enumerate(row):
                reps.append(int(index != 0))
                defs.append(2 if slot is None else 3)
                if slot is not None:
                    values.append(slot)
    return reps, defs, values


def take_levels(body, offset, expected):
    count = struct.unpack_from("<I", body, offset)[0]
    start = offset + 4
    stop = start + count
    assert body[start:stop] == bytes(octet for level in expected for octet in (2, level))
    return stop


def check(path, expected):
    data = path.read_bytes()
    assert data.startswith(b"PAR1") and data.endswith(b"PAR1")
    start, footer = metadata(data)
    outer = FIELD.encode()
    assert footer[2] == [{4: b"schema", 5: 1},
                         {3: 1, 4: outer, 5: 1, 6: 3, 10: {3: {}}},
                         {3: 2, 4: b"list", 5: 1},
                         {1: 1, 3: 1, 4: b"element"}]
    assert footer[1] == 1 and footer[3] == sum(map(len, expected))
    reader = pq.ParquetFile(BytesIO(data))
    schema = pa.schema([pa.field(FIELD, pa.list_(pa.field("element", pa.int32(), nullable=True)), nullable=True)])
    assert reader.schema_arrow.equals(schema)
    assert reader.num_row_groups == len(expected) and reader.metadata.num_rows == footer[3]
    assert [reader.read_row_group(index, use_threads=False)[0].to_pylist()
            for index in range(reader.num_row_groups)] == expected
    print(f"{path.name}, SHA-256 {sha256(data).hexdigest()}, footer [{start}, {len(data) - 8}), rows {footer[3]}")
    offset = 4
    for index, (group, rows) in enumerate(zip(footer[4], expected, strict=True)):
        [chunk] = group[1]
        column = chunk[3]
        reps, defs, values = wire(rows)
        assert chunk[2] == 0 and column[1] == 1 and column[2] == [0, 3]
        assert column[3] == [outer, b"list", b"element"]
        assert column[4] == 0 and column[5] == len(reps)
        assert column[9] == offset and column[6] == column[7] == group[2]
        assert group[3] == len(rows)
        stop = offset + column[7]
        assert offset < stop <= start
        header, header_size = parse(data[offset:stop], page)
        body_at = offset + header_size
        assert header == {1: 0, 2: stop - body_at, 3: stop - body_at,
                          5: {1: len(reps), 2: 0, 3: 3, 4: 3}}
        body = data[body_at:stop]
        definition_at = take_levels(body, 0, reps)
        scalars_at = take_levels(body, definition_at, defs)
        assert body[scalars_at:] == struct.pack("<" + "i" * len(values), *values)
        print(f"  group {index} frames [{offset}, {stop}), body @{body_at}, {len(rows)} rows, {len(reps)} slots")
        print(f"  reps {reps}, defs {defs}, PLAIN {values}, rows {rows}")
        offset = stop
    assert offset == start


def main(output):
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    output = output.resolve()
    output.mkdir(exist_ok=True, parents=True)
    cases = [("mixed", [FIRST, [], SECOND]), ("schema-only", []), ("empty-group", [[]])]
    paths = [output / (name + ".parquet") for name, _ in cases]
    subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                    "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), *map(str, paths)],
                   cwd=HERE.parents[1], check=True)
    print(f"PyArrow {pa.__version__}")
    for path, (_, batches) in zip(paths, cases, strict=True):
        check(path, batches)


if __name__ == "__main__":
    main(Path(sys.argv[1]))
