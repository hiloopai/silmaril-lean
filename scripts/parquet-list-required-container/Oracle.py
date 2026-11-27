"""Pinned required-parent Parquet LIST and native Arrow differential."""

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
prior = runpy.run_path(str(HERE.parent / "parquet-list-snappy-dictionary-v1" / "Oracle.py"))
pa, pq, metadata, read_fields, hybrid = (prior[name] for name in ("pa", "pq", "metadata", "read_fields", "hybrid"))
LIST = pa.list_(pa.field("element", pa.int32(), nullable=True))
SCHEMA = pa.schema([pa.field("items", LIST, nullable=False)])
GROUPS = [[[], [None], [-2147483648, None, 2147483647], [7, 7]],
          [[None, None], [], [-7, None, 0], [2147483647]]]


def produce(path, nullable):
    schema = SCHEMA if not nullable else pa.schema([pa.field("items", LIST, nullable=True)])
    groups = GROUPS if not nullable else [[None, *GROUPS[0][1:]], GROUPS[1]]
    values = pa.array(sum(groups, []), type=LIST)
    pq.write_table(pa.table({"items": values}, schema=schema), path, compression="NONE", use_dictionary=False,
                   data_page_version="1.0", write_statistics=False, row_group_size=4)
    parquet = pq.ParquetFile(path)
    assert parquet.schema_arrow == schema
    assert parquet.schema.column(0).max_definition_level == 2 + nullable
    assert parquet.schema.column(0).max_repetition_level == 1
    assert [parquet.read_row_group(i)[0].to_pylist() for i in range(2)] == groups
    return path.read_bytes()


def inspect(raw):
    footer_at, meta = metadata(raw)
    assert meta[3] == 8
    assert meta[2] == [{3: 0, 4: b"schema", 5: 1},
                       {3: 0, 4: b"items", 5: 1, 6: 3, 10: {3: {}}},
                       {3: 2, 4: b"list", 5: 1}, {1: 1, 3: 1, 4: b"element"}]
    print(f"native-required.parquet SHA-256 {sha256(raw).hexdigest()}, footer [{footer_at}, {len(raw) - 8})")
    end, pages = 4, []
    for ordinal, (group, expected) in enumerate(zip(meta[4], GROUPS, strict=True)):
        [chunk] = group[1]
        col = chunk[3]
        start = col[9]
        assert col[1] == 1 and col[2] == [3, 0] and col[3] == [b"items", b"list", b"element"] and col[4] == 0
        assert 11 not in col and start == end
        end = start + col[7]
        assert col[6] == col[7] == group[2] and end <= footer_at
        transport = TMemoryBuffer(raw[start:end])
        header = read_fields(TCompactProtocol(transport), (5,))
        payload = start + transport.cstringio_buf.tell()
        assert header == {1: 0, 2: end - payload, 3: end - payload, 5: {1: col[5], 2: 0, 3: 3, 4: 3}}
        rep = payload + 4
        defs_size_at = rep + struct.unpack_from("<I", raw, payload)[0]
        defs = defs_size_at + 4
        values = defs + struct.unpack_from("<I", raw, defs_size_at)[0]
        reps = hybrid(raw[rep:defs_size_at], 1, col[5])
        definitions = hybrid(raw[defs:values], 2, col[5])
        scalars = [v for (v,) in struct.iter_unpack("<i", raw[values:end])]
        assert reps[0] == 0 and reps.count(0) == group[3] == len(expected)
        assert definitions.count(2) == len(scalars) and all(d <= 2 for d in definitions)
        rows, ordered = [], iter(scalars)
        for r, d in zip(reps, definitions, strict=True):
            if r == 0:
                rows.append([])
            else:
                assert d > 0 and rows[-1]
            if d > 0:
                rows[-1].append(None if d == 1 else next(ordered))
        assert rows == expected
        print(f"  group {ordinal} page 0 @{start}, rep [{rep}, {defs_size_at}) {reps}, "
              f"def [{defs}, {values}) {definitions}, values [{values}, {end}) {scalars}")
        pages.append((start, rep, defs_size_at, defs, values, reps, definitions))
    assert end == footer_at
    return pages


def replace_levels(raw, start, stop, values, width):
    assert 0 < len(values) <= 8
    word = sum(v << (i * width) for i, v in enumerate(values))
    packed = bytes([3]) + word.to_bytes(width, "little")
    assert len(packed) == stop - start
    assert hybrid(packed, width, len(values)) == values
    return raw[:start] + packed + raw[stop:]


def controls(raw, page):
    offset, rep, rep_stop, defs, defs_stop, repetitions, definitions = page
    changed = [3] + definitions[1:]
    yield "definition-3", replace_levels(raw, defs, defs_stop, changed, 2), offset
    changed = repetitions.copy()
    changed[definitions.index(0)] = 1
    yield "empty-continuation", replace_levels(raw, rep, rep_stop, changed, 1), offset
    changed = [1] + repetitions[1:]
    yield "leading-continuation", replace_levels(raw, rep, rep_stop, changed, 1), offset


def run(out, generate):
    out = out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    print(f"PyArrow {pa.__version__}")
    native_path, optional_path = (out / name for name in ("native-required.parquet", "native-optional.parquet"))
    native = produce(native_path, False)
    pages = inspect(native)
    optional = produce(optional_path, True)
    print(f"native-optional.parquet SHA-256 {sha256(optional).hexdigest()}")
    if generate:
        return
    driver = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
              "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
    for path in (native_path, optional_path):
        assert path.read_bytes() == (ROOT / "data/parquet-list-required-container" / path.name).read_bytes()
    ipc_path = out / "lean-required.arrows"
    subprocess.run([*driver, "write", str(native_path), str(ipc_path)], cwd=ROOT, check=True)
    wire = ipc_path.read_bytes()
    with pa.ipc.open_stream(wire) as reader:
        assert reader.schema == SCHEMA
        assert [batch.column(0).to_pylist() for batch in reader] == GROUPS
    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert [m.type for m in messages] == ["schema", "record batch", "record batch"]
    assert all(m.metadata_version == pa.ipc.MetadataVersion.V5 for m in messages)
    eos = sum(8 + m.metadata.size + (m.body.size if m.body else 0) for m in messages)
    assert wire[eos:] == bytes.fromhex("ff ff ff ff 00 00 00 00")
    print(f"lean-required.arrows SHA-256 {sha256(wire).hexdigest()}, exact EOS [{eos}, {len(wire)})")
    for label, changed, offset in controls(native, pages[1]):
        path = out / f"mutated-{label}.parquet"
        path.write_bytes(changed)
        print(f"{path.name} SHA-256 {sha256(changed).hexdigest()}")
        print(subprocess.check_output([*driver, "refuse", label, str(path), str(offset)], cwd=ROOT, text=True).strip())


if __name__ == "__main__":
    run(Path(sys.argv[1]), sys.argv[2:] == ["generate"])
