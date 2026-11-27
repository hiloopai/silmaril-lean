"""Required LIST dictionary producer, independent V2 wire checks and IPC comparator."""

from copy import deepcopy
from hashlib import sha256
from io import BytesIO
import os
from pathlib import Path
import runpy
import struct
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
base = runpy.run_path(str(HERE.parent / "parquet-list-snappy-dictionary-v2" / "Oracle.py"))
required = runpy.run_path(str(HERE.parent / "parquet-list-required-container-v2-snappy-multi" / "Oracle.py"))
pa, pq, SNAPPY, metadata, frames_at, data_sections, checksum, hybrid, expected_entries, replace_last = (
    base[key] for key in ("pa", "pq", "SNAPPY", "metadata", "frames_at", "data_sections", "checksum",
                          "hybrid", "expected_entries", "replace_last")
)
SCHEMA, frame_at = required["SCHEMA"], required["frame_at"]
GROUPS = [required["GROUPS"][0], [[None, None], [], [2147483647], [7, -2147483648] * 52 + [None]]]


def produce(path, checksums=True, dictionary=True):
    values = pa.array(sum(GROUPS, []), type=SCHEMA.field(0).type)
    pq.write_table(pa.table({"items": values}, schema=SCHEMA), path, compression="SNAPPY",
                   use_dictionary=dictionary, data_page_version="2.0", write_statistics=False,
                   write_page_checksum=checksums, row_group_size=4, write_batch_size=1,
                   data_page_size=1, max_rows_per_page=2)
    return path.read_bytes()


def inspect(label, raw, checksums, default_flag=False):
    footer_at, meta = metadata(raw)
    assert meta[3] == 8
    assert meta[2] == [{3: 0, 4: b"schema", 5: 1},
                       {3: 0, 4: b"items", 5: 1, 6: 3, 10: {3: {}}},
                       {3: 2, 4: b"list", 5: 1}, {1: 1, 3: 1, 4: b"element"}]
    frames = frames_at(raw, footer_at, meta)
    assert len(frames) == 2 and [len(chunk) for chunk in frames] == [6, 6]
    reader = pq.ParquetFile(BytesIO(raw), page_checksum_verification=True)
    assert reader.schema_arrow == SCHEMA and reader.num_row_groups == 2
    assert reader.schema.column(0).max_repetition_level == 1
    assert reader.schema.column(0).max_definition_level == 2
    print(f"{label} SHA-256 {sha256(raw).hexdigest()}, footer [{footer_at}, {len(raw) - 8})")
    expanded_file = 0
    for group, (pages, expected) in enumerate(zip(frames, GROUPS, strict=True)):
        assert all(p.header.get(4) == (checksum(p.body) if checksums else None) for p in pages)
        dictionary = pages[0]
        words = SNAPPY.decompress(dictionary.body, dictionary.header[2]).to_pybytes()
        entries = [value for (value,) in struct.iter_unpack("<i", words)]
        assert dictionary.header[7] == {1: len(entries), 2: 0, 3: False}
        assert entries == expected_entries(expected) and len(words) == dictionary.header[2] == 4 * len(entries)
        print(f"  group {group} dictionary @{dictionary.offset}, crc {dictionary.header.get(4, 'absent')}, "
              f"payload [{dictionary.payload}, {dictionary.stop}), signed {entries}")
        rows = []
        for ordinal, page in enumerate(pages[1:], 1):
            h = page.header[8]
            reps, definitions, levels, indices_wire = data_sections(page)
            assert len(reps) == len(definitions) == h[1]
            assert not reps or reps[0] == 0
            assert reps.count(0) == h[3] and definitions.count(0) + definitions.count(1) == h[2]
            width, *runs = indices_wire
            indices = hybrid(bytes(runs), width, h[1] - h[2])
            assert len(indices) == definitions.count(2) and all(i < len(entries) for i in indices)
            compressed = (group, ordinal) == (1, 5)
            assert h.get(7, True) == compressed and (7 not in h) == (compressed and default_flag)
            values = iter(entries[i] for i in indices)
            for rep, definition in zip(reps, definitions, strict=True):
                if rep == 0:
                    rows.append([])
                else:
                    assert rep == 1 and definition > 0 and rows[-1]
                if definition:
                    rows[-1].append(None if definition == 1 else next(values))
            rep_end, def_end = page.payload + h[6], page.payload + len(levels)
            print(f"  group {group} data frame {ordinal} @{page.offset}, crc {page.header.get(4, 'absent')}, "
                  f"slots/rows/nulls {h[1]}/{h[3]}/{h[2]}, flag {h.get(7, 'default true')}, "
                  f"rep [{page.payload}, {rep_end}), def [{rep_end}, {def_end}), "
                  f"indices [{def_end}, {page.stop}) -> {indices_wire.hex()}, width {width}, count {len(indices)}")
        assert rows == expected == reader.read_row_group(group)[0].to_pylist()
        assert sum(p.header[8][3] for p in pages[1:]) == len(rows) == meta[4][group][3]
        assert sum(p.header[8][2] for p in pages[1:]) == [3, 4][group]
        expanded_file += sum(p.header[2] for p in pages)
    print(f"  total expanded page bodies {expanded_file} bytes")
    return frames


def controls(raw, frames, plain):
    group = frames[1]
    for label, ordinal in (("dictionary-crc", 0), ("raw-index-crc", 3), ("compressed-index-crc", 5), ("level-crc", 5)):
        frame = group[ordinal]
        if ordinal == 0 or label == "level-crc":
            offset = frame.payload
        else:
            offset = frame.payload + frame.header[8][5] + frame.header[8][6]
        changed = bytearray(raw)
        changed[offset] ^= 128
        assert checksum(changed[frame.payload:frame.stop]) != frame.header[4]
        reader = pq.ParquetFile(BytesIO(changed), page_checksum_verification=True)
        assert reader.read_row_group(0)[0].to_pylist() == GROUPS[0]
        try:
            reader.read_row_group(1)
        except OSError as error:
            assert "CRC" in str(error)
        else:
            raise AssertionError("expected CRC refusal")
        yield "mutated", label, bytes(changed), ordinal, frame.offset

    tail = group[-1]
    _, _, levels, indices = data_sections(tail)
    for label in ("index-out-of-bounds", "no-index-width", "late-continuation", "page-rows", "page-nulls", "plain-fallback"):
        header, body = deepcopy(tail.header), tail.body
        h = header[8]
        if label == "index-out-of-bounds":
            assert indices[:3] == bytes.fromhex("021b99")
            bad = indices[:2] + bytes([indices[2] | 2]) + indices[3:]
            assert hybrid(bad[1:], bad[0], h[1] - h[2])[0] == 3
            body = levels + SNAPPY.compress(bad).to_pybytes()
        elif label == "no-index-width":
            body = levels
            header[2], h[7] = len(body), False
        elif label == "late-continuation":
            assert body[0] == 3 and body[1] & 1 == 0
            body = bytes([body[0], body[1] | 1]) + body[2:]
            assert hybrid(body[:h[6]], 1, h[1]) == [1] * h[1]
        elif label == "page-rows":
            h[3] = 0
        elif label == "page-nulls":
            h[2] = 0
        else:
            header, body = deepcopy(plain.header), plain.body
            assert header[8][4] == 0 and [header[8][k] for k in (1, 2, 3)] == [h[k] for k in (1, 2, 3)]
        header[3], header[4] = len(body), checksum(body)
        changed = replace_last(raw, tail, header, body)
        parsed = frame_at(changed, tail.offset, metadata(changed)[0])
        assert parsed.header == header and parsed.body == body
        if label == "plain-fallback":
            assert pq.ParquetFile(BytesIO(changed), page_checksum_verification=True).read()[0].to_pylist() == sum(GROUPS, [])
        yield "assembled", label, changed, 5, tail.offset


def write_ipc(driver, source):
    path = source.with_suffix(".arrows")
    subprocess.run([*driver, "write", str(source), str(path)], cwd=ROOT, check=True)
    wire = path.read_bytes()
    with pa.ipc.open_stream(wire) as reader:
        assert reader.schema == SCHEMA
        assert [batch.column(0).to_pylist() for batch in reader] == GROUPS
    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert [m.type for m in messages] == ["schema", "record batch", "record batch"]
    assert all(m.metadata_version == pa.ipc.MetadataVersion.V5 for m in messages)
    eos = sum(8 + m.metadata.size + (m.body.size if m.body else 0) for m in messages)
    assert wire[eos:] == bytes.fromhex("ff ff ff ff 00 00 00 00")
    print(f"{path.name} SHA-256 {sha256(wire).hexdigest()}, exact EOS [{eos}, {len(wire)})")


def run(out, generate):
    out = out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    print(f"PyArrow {pa.__version__}")
    path = out / "native-required-v2-dictionary.parquet"
    no_crc = out / "native-required-v2-dictionary-no-crc.parquet"
    native = produce(path)
    frames = inspect(path.name, native, True)
    inspect(no_crc.name, produce(no_crc, checksums=False), False)
    if generate:
        return
    for source in (path, no_crc):
        assert source.read_bytes() == (ROOT / "data" / HERE.name / source.name).read_bytes()

    tail = frames[-1][-1]
    header = deepcopy(tail.header)
    assert header[8].pop(7) is True
    default_path = out / "assembled-default-flag.parquet"
    default_path.write_bytes(replace_last(native, tail, header, tail.body))
    inspect(default_path.name, default_path.read_bytes(), True, default_flag=True)
    driver = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
              "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
    for source in (path, no_crc, default_path):
        write_ipc(driver, source)

    plain_raw = produce(out / "producer-plain-for-fallback.parquet", dictionary=False)
    footer_at, meta = metadata(plain_raw)
    cursor = meta[4][1][1][0][3][9]
    while cursor < footer_at:
        plain = frame_at(plain_raw, cursor, footer_at)
        cursor = plain.stop
    for provenance, label, changed, ordinal, offset in controls(native, frames, plain):
        control = out / f"{provenance}-{label}.parquet"
        control.write_bytes(changed)
        print(f"{control.name} SHA-256 {sha256(changed).hexdigest()}")
        cmd = [*driver, "refuse", label, str(control), str(ordinal), str(offset)]
        print(subprocess.check_output(cmd, cwd=ROOT, text=True).strip())


if __name__ == "__main__":
    run(Path(sys.argv[1]), sys.argv[2:] == ["generate"])
