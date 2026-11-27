"""Produce the native multi-page file and check the Lean reader independently."""

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
prior = runpy.run_path(str(HERE.parent / "parquet-list-required-container-v2" / "Oracle.py"))
pa, pq, SCHEMA, GROUPS, read_fields, hybrid, replace_levels = (
    prior[key] for key in ("pa", "pq", "SCHEMA", "GROUPS", "read_fields", "hybrid", "replace_levels")
)
Frame, metadata, replace_last, compact, footer, check_ipc = (
    prior[key] for key in ("Frame", "metadata", "replace_last", "compact", "footer", "check_ipc")
)


def produce(path):
    values = pa.array(sum(GROUPS, []), type=SCHEMA.field(0).type)
    pq.write_table(pa.table({"items": values}, schema=SCHEMA), path, compression="NONE", use_dictionary=False,
                   data_page_version="2.0", write_statistics=False, row_group_size=4, write_batch_size=1,
                   data_page_size=1, max_rows_per_page=2)
    return path.read_bytes()


def frame_at(raw, start, bound):
    transport = TMemoryBuffer(raw[start:bound])
    header = read_fields(TCompactProtocol(transport), (8,))
    payload = start + transport.cstringio_buf.tell()
    stop = payload + header[3]
    assert start < payload <= stop <= bound
    return Frame(start, payload, stop, header, raw[payload:stop])


def inspect(raw):
    footer_at, meta = metadata(raw)
    assert meta[3] == 8
    assert meta[2] == [{3: 0, 4: b"schema", 5: 1},
                       {3: 0, 4: b"items", 5: 1, 6: 3, 10: {3: {}}},
                       {3: 2, 4: b"list", 5: 1}, {1: 1, 3: 1, 4: b"element"}]
    reader = pq.ParquetFile(BytesIO(raw))
    assert reader.schema_arrow == SCHEMA and reader.num_row_groups == 2
    assert reader.schema.column(0).max_repetition_level == 1
    assert reader.schema.column(0).max_definition_level == 2
    print(f"native-required-v2-multi.parquet SHA-256 {sha256(raw).hexdigest()}, "
          f"footer [{footer_at}, {len(raw) - 8})")
    end, frames = 4, []
    for ordinal, (group, expected) in enumerate(zip(meta[4], GROUPS, strict=True)):
        [chunk] = group[1]
        col = chunk[3]
        cursor = col[9]
        assert col[1] == 1 and set(col[2]) == {0, 3}
        assert col[3] == [b"items", b"list", b"element"] and col[4] == 0 and 11 not in col
        assert cursor == end and col[6] == col[7] == group[2]
        end = cursor + col[7]
        assert end <= footer_at
        rows, headers = [], []
        while cursor < end:
            frame = frame_at(raw, cursor, end)
            h = frame.header[8]
            assert frame.header == {1: 3, 2: len(frame.body), 3: len(frame.body), 8: h}
            assert h[4] == 0 and h[7] is False
            rep_end = frame.payload + h[6]
            def_end = rep_end + h[5]
            assert frame.payload <= rep_end <= def_end <= frame.stop
            reps = hybrid(raw[frame.payload:rep_end], 1, h[1])
            defs = hybrid(raw[rep_end:def_end], 2, h[1])
            scalars = [value for (value,) in struct.iter_unpack("<i", raw[def_end:frame.stop])]
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
            print(f"  group {ordinal} page {len(headers)} @{cursor}, slots {h[1]}, rows {h[3]}, "
                  f"zero-value slots {h[2]}, rep [{frame.payload}, {rep_end}) {reps}, "
                  f"def [{rep_end}, {def_end}) {defs}, scalar [{def_end}, {frame.stop}) {scalars}")
            headers.append(h)
            frames.append((frame, rep_end, reps))
            rows.extend(page_rows)
            cursor = frame.stop
        assert cursor == end and len(headers) == 3
        assert sum(h[1] for h in headers) == col[5] == 7
        assert sum(h[3] for h in headers) == group[3] == 4
        assert sum(h[2] for h in headers) == [3, 4][ordinal]
        assert rows == expected == reader.read_row_group(ordinal)[0].to_pylist()
    assert end == footer_at
    return frames


def controls(raw, frames):
    frame, rep_end, reps = frames[-1]
    for label in ("page-rows", "page-nulls", "page-slots", "short-plain", "long-plain"):
        header, body = deepcopy(frame.header), frame.body
        h = header[8]
        if label == "page-rows":
            h[3] = 0
        elif label == "page-nulls":
            h[2] = 1
        elif label == "page-slots":
            h[1] += 1
        else:
            body = body[:-4] if label == "short-plain" else body + bytes(4)
            header[2] = header[3] = len(body)
        changed = replace_last(raw, frame, header, body)
        actual = frame_at(changed, frame.offset, metadata(changed)[0])
        assert actual.header == header and actual.body == body
        yield f"assembled-{label}", label, frame.offset, changed

    for label in ("group-rows", "group-slots"):
        start, meta = metadata(raw)
        if label == "group-rows":
            meta[3] -= 1
            meta[4][1][3] -= 1
        else:
            meta[4][1][1][0][3][5] += 1
        rebuilt = compact(footer, meta)
        changed = raw[:start] + rebuilt + struct.pack("<I", len(rebuilt)) + b"PAR1"
        assert metadata(changed) == (start, meta)
        yield f"assembled-{label}", label, frame.offset, changed

    changed = replace_levels(raw, frame.payload, rep_end, [1] + reps[1:], 1)
    assert hybrid(changed[frame.payload:rep_end], 1, len(reps)) == [1]
    yield "mutated-late-continuation", "late-continuation", frame.offset, changed

    earlier, earlier_rep_end, earlier_reps = frames[-2]
    changed = replace_levels(changed, earlier.payload, earlier_rep_end, [1] + earlier_reps[1:], 1)
    yield "mutated-two-continuations", "first-of-two", earlier.offset, changed

    page, rep_end, reps = frames[-3]
    def_end = rep_end + page.header[8][5]
    assert reps == [0, 1, 0] and hybrid(raw[rep_end:def_end], 2, len(reps)) == [1, 1, 0]
    changed = replace_levels(raw, rep_end, def_end, [0, 1, 1], 2)
    yield "mutated-continue-empty", "continue-empty", page.offset, changed


def run(out, generate):
    out = out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    print(f"PyArrow {pa.__version__}")
    path = out / "native-required-v2-multi.parquet"
    native = produce(path)
    frames = inspect(native)
    if generate:
        return
    assert native == (ROOT / "data" / HERE.name / path.name).read_bytes()
    driver = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
              "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
    check_ipc(driver, path)
    for filename, label, offset, changed in controls(native, frames):
        control = out / f"{filename}.parquet"
        control.write_bytes(changed)
        print(f"{control.name} SHA-256 {sha256(changed).hexdigest()}")
        command = [*driver, "refuse", label, str(control), str(offset)]
        print(subprocess.check_output(command, cwd=ROOT, text=True).strip())


if __name__ == "__main__":
    run(Path(sys.argv[1]), sys.argv[2:] == ["generate"])
