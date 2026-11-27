"""Pinned native Snappy V2 groups and a labeled all-profile assembly."""

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
fallback = runpy.run_path(str(HERE.parent / "parquet-list-snappy-dictionary-fallback-v2" / "Oracle.py"))
pa, pq, schema, metadata, checksum, mutate_tag = (
    fallback[name] for name in ("pa", "pq", "schema", "metadata", "checksum", "mutate_tag")
)
v2 = fallback["v2"]
Frame, compact, footer, read_fields = (v2[key] for key in ("Frame", "compact", "footer", "read_fields"))
PLAIN = [None, [], [None, -2147483648, 2147483647], [4] * 32]
DICTIONARY = [None, [], [None, -7, -7], [-7], [None], [0, -7], [0] * 16, [None, -7]]
FALLBACK = fallback["ROWS"][0]


def produce(path, groups, dictionary):
    values = pa.array([row for group in groups for row in group], type=schema.field(0).type)
    pq.write_table(pa.table({"items": values}, schema=schema), path,
                   compression="SNAPPY", use_dictionary=dictionary, data_page_version="2.0",
                   write_statistics=False, write_page_checksum=True, row_group_size=8,
                   write_batch_size=1, data_page_size=1, max_rows_per_page=2, dictionary_pagesize_limit=16)
    return path.read_bytes()


def assemble(plain, dictionary_and_fallback):
    plain_footer, plain_meta = metadata(plain)
    dict_footer, dict_meta = metadata(dictionary_and_fallback)
    assert plain_meta[2] == dict_meta[2] and len(plain_meta[4]) == 1 and len(dict_meta[4]) == 2
    shifted = deepcopy(dict_meta[4])
    delta = plain_footer - 4
    for group in shifted:
        [chunk] = group[1]
        assert chunk[2] == 0
        chunk[3][9] += delta
        chunk[3][11] += delta
    meta = {**plain_meta, 3: plain_meta[3] + dict_meta[3], 4: plain_meta[4] + shifted}
    packed = compact(footer, meta)
    return plain[:plain_footer] + dictionary_and_fallback[4:dict_footer] + packed + struct.pack("<I", len(packed)) + b"PAR1"


def inspect(name, raw, groups, tags):
    footer_at, meta = metadata(raw)
    assert meta[3] == sum(map(len, groups)) and len(meta[4]) == len(groups)
    reader = pq.ParquetFile(BytesIO(raw), page_checksum_verification=True)
    assert reader.schema_arrow == schema and reader.num_row_groups == len(groups)
    print(f"{name} SHA-256 {sha256(raw).hexdigest()}, footer [{footer_at}, {len(raw) - 8})")
    cursor, framed = 4, []
    for index, (group, rows, kinds) in enumerate(zip(meta[4], groups, tags, strict=True)):
        [chunk] = group[1]
        col = chunk[3]
        assert col[1] == 1 and col[3] == [b"items", b"list", b"element"] and col[4] == 1
        assert cursor == col.get(11, col[9])
        start = cursor
        stop = start + col[7]
        frames, row_total, slot_total, expanded = [], 0, 0, 0
        while cursor < stop:
            buffer = TMemoryBuffer(raw[cursor:stop])
            header = read_fields(TCompactProtocol(buffer), (7, 8))
            payload = cursor + buffer.cstringio_buf.tell()
            end = payload + header[3]
            assert cursor < payload < end <= stop <= footer_at
            body = raw[payload:end]
            assert header[4] == checksum(body)
            if header[1] == 2:
                assert not frames and 11 in col and header[7][2] == 0
            else:
                assert header[1] == 3
                h = header[8]
                assert h[5] + h[6] <= min(header[2], header[3])
                row_total += h[3]
                slot_total += h[1]
            frames.append(Frame(cursor, payload, end, header, body))
            expanded += payload - cursor + header[2]
            cursor = end
        actual = [p.header[8][4] if p.header[1] == 3 else "dict" for p in frames]
        assert actual == kinds and col[9] == frames[int(actual[0] == "dict")].offset, (actual, kinds, col[9])
        assert row_total == group[3] == len(rows) and slot_total == col[5]
        assert expanded == col[6] == group[2]
        assert reader.read_row_group(index, use_threads=False)[0].to_pylist() == rows
        print(f"  group {index} [{start}, {stop}), tags {actual}, rows {row_total}, slots {slot_total}, "
              f"expanded {sum(p.header[2] for p in frames)}, frame offsets {[p.offset for p in frames]}")
        framed.append(frames)
    assert cursor == footer_at
    return framed


def check_ipc(driver, source, groups):
    out = source.with_suffix(".arrows")
    subprocess.run([*driver, "write", str(source), str(out)], cwd=ROOT, check=True)
    ipc = out.read_bytes()
    with pa.ipc.open_stream(ipc) as reader:
        assert reader.schema == schema
        assert [batch.column(0).to_pylist() for batch in reader] == groups
    messages = list(pa.ipc.MessageReader.open_stream(ipc))
    assert [m.type for m in messages] == ["schema"] + ["record batch"] * len(groups)
    assert all(m.metadata_version == pa.ipc.MetadataVersion.V5 for m in messages)
    eos = sum(8 + m.metadata.size + (m.body.size if m.body else 0) for m in messages)
    assert ipc[eos:] == bytes.fromhex("ff ff ff ff 00 00 00 00")
    print(f"  {out.name} SHA-256 {sha256(ipc).hexdigest()}, exact EOS [{eos}, {len(ipc)})")


def damage_crc(raw, frame):
    data = bytearray(raw)
    data[frame.payload] ^= 0x80
    assert checksum(data[frame.payload:frame.stop]) != frame.header[4]
    return bytes(data)


def controls(raw, frames):
    for label, group, ordinal in (("plain-crc", 0, 2), ("dictionary-crc", 1, 3), ("fallback-plain-crc", 2, 8)):
        frame = frames[group][ordinal]
        yield label, damage_crc(raw, frame), group, ordinal, frame.offset
    group, ordinal = 2, 8
    last = frames[group][ordinal]
    reentry = mutate_tag(raw, last, 8)
    yield "reentry", reentry, group, ordinal, last.offset
    early = frames[group][3]
    yield "early-index-crc-before-reentry", damage_crc(reentry, early), group, 3, early.offset


def run(out, generate):
    out = out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    print(f"PyArrow {pa.__version__}")
    plain_path = out / "native-plain-v2.parquet"
    native_path = out / "native-dictionary-and-fallback-v2.parquet"
    assembled_path = out / "assembled-three-profiles-v2.parquet"
    plain = produce(plain_path, [PLAIN], False)
    native = produce(native_path, [DICTIONARY, FALLBACK], True)
    assembled = assemble(plain, native)
    assembled_path.write_bytes(assembled)
    plain_tags, dict_tags, fallback_tags = [0] * 3, ["dict"] + [8] * 9, ["dict"] + [8] * 5 + [0] * 3
    inspect(plain_path.name, plain, [PLAIN], [plain_tags])
    inspect(native_path.name, native, [DICTIONARY, FALLBACK], [dict_tags, fallback_tags])
    frames = inspect(assembled_path.name, assembled, [PLAIN, DICTIONARY, FALLBACK],
                     [plain_tags, dict_tags, fallback_tags])
    assert assembled[4:metadata(assembled)[0]] == plain[4:metadata(plain)[0]] + native[4:metadata(native)[0]]
    if generate:
        return
    driver = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
              "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
    for source, rows in ((plain_path, [PLAIN]), (native_path, [DICTIONARY, FALLBACK]),
                         (assembled_path, [PLAIN, DICTIONARY, FALLBACK])):
        assert source.read_bytes() == (ROOT / "data/parquet-list-snappy-v2-dispatch" / source.name).read_bytes()
        check_ipc(driver, source, rows)
    for label, damaged, group, ordinal, offset in controls(assembled, frames):
        source = out / f"mutated-{label}.parquet"
        source.write_bytes(damaged)
        print(f"{source.name} SHA-256 {sha256(damaged).hexdigest()}")
        cmd = [*driver, "refuse", label, str(source), str(assembled_path), str(group), str(ordinal), str(offset)]
        print(subprocess.check_output(cmd, cwd=ROOT, text=True).strip())


if __name__ == "__main__":
    run(Path(sys.argv[1]), sys.argv[2:] == ["generate"])
