"""Native PyArrow required LIST V2 input plus Thrift-checked controls."""

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
v1 = runpy.run_path(str(HERE.parent / "parquet-list-required-container" / "Oracle.py"))
v2 = runpy.run_path(str(HERE.parent / "parquet-list-snappy-dictionary-v2" / "Oracle.py"))
pa, pq, SCHEMA, GROUPS, read_fields, hybrid, replace_levels = (
    v1[key] for key in ("pa", "pq", "SCHEMA", "GROUPS", "read_fields", "hybrid", "replace_levels")
)
Frame, metadata, replace_last, compact, footer = (
    v2[key] for key in ("Frame", "metadata", "replace_last", "compact", "footer")
)


def produce(path):
    values = pa.array(sum(GROUPS, []), type=SCHEMA.field(0).type)
    pq.write_table(pa.table({"items": values}, schema=SCHEMA), path, compression="NONE", use_dictionary=False,
                   data_page_version="2.0", write_statistics=False, row_group_size=4)
    return path.read_bytes()


def frame_at(raw, start, stop):
    transport = TMemoryBuffer(raw[start:stop])
    header = read_fields(TCompactProtocol(transport), (8,))
    payload = start + transport.cstringio_buf.tell()
    assert start < payload <= stop and payload + header[3] == stop
    return Frame(start, payload, stop, header, raw[payload:stop])


def inspect(label, raw, default_flag=False):
    footer_at, meta = metadata(raw)
    assert meta[3] == 8
    assert meta[2] == [{3: 0, 4: b"schema", 5: 1},
                       {3: 0, 4: b"items", 5: 1, 6: 3, 10: {3: {}}},
                       {3: 2, 4: b"list", 5: 1}, {1: 1, 3: 1, 4: b"element"}]
    reader = pq.ParquetFile(BytesIO(raw))
    assert reader.schema_arrow == SCHEMA and reader.num_row_groups == 2
    assert reader.schema.column(0).max_repetition_level == 1
    assert reader.schema.column(0).max_definition_level == 2
    print(f"{label} SHA-256 {sha256(raw).hexdigest()}, footer [{footer_at}, {len(raw) - 8})")
    end, pages = 4, []
    for ordinal, (group, expected) in enumerate(zip(meta[4], GROUPS, strict=True)):
        [chunk] = group[1]
        col = chunk[3]
        start = col[9]
        assert col[1] == 1 and set(col[2]) == {0, 3}
        assert col[3] == [b"items", b"list", b"element"] and col[4] == 0 and 11 not in col
        assert start == end and col[6] == col[7] == group[2]
        end = start + col[7]
        assert end <= footer_at
        frame = frame_at(raw, start, end)
        h = frame.header[8]
        assert frame.header == {1: 3, 2: len(frame.body), 3: len(frame.body), 8: h} and h[4] == 0
        assert (7 not in h) == (default_flag and ordinal == 1)
        assert h.get(7, True) == (default_flag and ordinal == 1)
        rep_end = frame.payload + h[6]
        def_end = rep_end + h[5]
        assert frame.payload <= rep_end <= def_end <= end
        reps = hybrid(raw[frame.payload:rep_end], 1, h[1])
        defs = hybrid(raw[rep_end:def_end], 2, h[1])
        scalars = [value for (value,) in struct.iter_unpack("<i", raw[def_end:end])]
        assert h[1] == col[5] == len(reps) == len(defs)
        assert reps[0] == 0 and reps.count(0) == h[3] == group[3] == len(expected)
        assert h[2] == defs.count(0) + defs.count(1)
        assert len(scalars) == defs.count(2) == h[1] - h[2]
        rows, ordered = [], iter(scalars)
        for r, d in zip(reps, defs, strict=True):
            if r == 0:
                rows.append([])
            else:
                assert d > 0 and rows[-1]
            if d > 0:
                rows[-1].append(None if d == 1 else next(ordered))
        assert rows == expected == reader.read_row_group(ordinal)[0].to_pylist()
        print(f"  group {ordinal} page 0 @{start}, slots {h[1]}, rows {h[3]}, zero-value slots {h[2]}, "
              f"is_compressed {h.get(7, 'default true')}, rep [{frame.payload}, {rep_end}) {reps}, "
              f"def [{rep_end}, {def_end}) {defs}, scalar [{def_end}, {end}) {scalars}")
        pages.append((frame, rep_end, def_end, reps, defs))
    assert end == footer_at
    return pages


def controls(raw, last):
    frame, rep_end, def_end, reps, defs = last
    for label in ("header-rows", "header-nulls", "header-slots", "level-geometry", "short-plain", "long-plain"):
        header, body = deepcopy(frame.header), frame.body
        h = header[8]
        if label == "header-rows":
            h[3] -= 1
        elif label == "header-nulls":
            h[2] -= 1
        elif label == "header-slots":
            h[1] += 1
        elif label == "level-geometry":
            h[5] = len(body) + 1
        else:
            body = body[:-4] if label == "short-plain" else body + bytes(4)
            header[2] = header[3] = len(body)
        changed = replace_last(raw, frame, header, body)
        assert frame_at(changed, frame.offset, metadata(changed)[0]).header == header
        yield f"assembled-{label}", label, changed

    start, meta = metadata(raw)
    meta[3] -= 1
    meta[4][1][3] -= 1
    rebuilt = compact(footer, meta)
    changed = raw[:start] + rebuilt + struct.pack("<I", len(rebuilt)) + b"PAR1"
    assert metadata(changed) == (start, meta)
    yield "assembled-group-rows", "group-rows", changed

    changed = replace_levels(raw, frame.payload, rep_end, [1] + reps[1:], 1)
    yield "mutated-leading-continuation", "leading-continuation", changed
    changed = replace_levels(raw, rep_end, def_end, [3] + defs[1:], 2)
    yield "mutated-definition-3", "definition-3", changed


def check_ipc(driver, path):
    output = path.with_suffix(".arrows")
    subprocess.run([*driver, "write", str(path), str(output)], cwd=ROOT, check=True)
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
    native_path = out / "native-required-v2.parquet"
    native = produce(native_path)
    pages = inspect(native_path.name, native)
    frame = pages[1][0]
    header = deepcopy(frame.header)
    assert header[8].pop(7) is False
    default_path = out / "assembled-default-flag-v2.parquet"
    default_path.write_bytes(replace_last(native, frame, header, frame.body))
    inspect(default_path.name, default_path.read_bytes(), default_flag=True)
    if generate:
        return
    assert native == (ROOT / "data/parquet-list-required-container-v2" / native_path.name).read_bytes()
    driver = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
              "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
    for path in (native_path, default_path):
        check_ipc(driver, path)
    for name, label, changed in controls(native, pages[1]):
        path = out / f"{name}.parquet"
        path.write_bytes(changed)
        print(f"{path.name} SHA-256 {sha256(changed).hexdigest()}")
        cmd = [*driver, "refuse", label, str(path), str(frame.offset)]
        print(subprocess.check_output(cmd, cwd=ROOT, text=True).strip())


if __name__ == "__main__":
    run(Path(sys.argv[1]), sys.argv[2:] == ["generate"])
