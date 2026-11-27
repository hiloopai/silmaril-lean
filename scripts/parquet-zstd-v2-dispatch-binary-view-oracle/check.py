"""Replay the pinned strict Zstandard V2 parents and assemble mixed groups verbatim."""

from copy import deepcopy
from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
from runpy import run_path
from struct import pack
import subprocess
import sys
from zlib import crc32

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = Path(sys.argv[1]).resolve()
OUT.mkdir(parents=True, exist_ok=True)
PHYSICAL = run_path(str(HERE.parent / "parquet-gzip-dictionary-binary-view-oracle/check.py"))
THRIFT = PHYSICAL["THRIFT"]
ORDER = [("dictionary", 0), ("plain", 0), ("fallback", 1), ("dictionary", 2)]


def pinned_parents():
    parents = {}
    for profile in ("plain", "dictionary", "fallback"):
        target = OUT / "parents" / profile
        script = HERE.parent / f"parquet-zstd-v2-{profile}-binary-view-oracle" / "check.py"
        subprocess.run([sys.executable, "-I", str(script), str(target)], cwd=ROOT, check=True)
        parents[profile] = ((target / "v2-crc.parquet").read_bytes(), (target / "v2-crc.arrows").read_bytes())
    return parents


def assemble(parents):
    origins = {name: PHYSICAL["read_footer"](wire) for name, (wire, _) in parents.items()}
    footer = deepcopy(origins["plain"][1])
    assert all(source[2] == footer[2] and source[7] == footer[7] for _, source in origins.values())
    groups, body = [], bytearray(b"PAR1")
    for name, ordinal in ORDER:
        footer_start, origin = origins[name]
        group = deepcopy(THRIFT["list_field"](origin, 4)[ordinal])
        start = group[5][1]
        delta = len(body) - start
        assert 4 <= start < footer_start and 7 not in group
        group[5] = TType.I64, len(body)
        cursor = start
        for chunk in THRIFT["list_field"](group, 1):
            metadata = chunk[3][1]
            assert set(chunk) == {2, 3} and chunk[2][1] == 0
            assert not set(metadata) & {10, 14, 15}
            assert metadata.get(11, metadata[9])[1] == cursor
            cursor += metadata[7][1]
            for key in (9, 11):
                if key in metadata:
                    assert metadata[key][0] == TType.I64
                    metadata[key] = TType.I64, metadata[key][1] + delta
        assert cursor == start + group[6][1] <= footer_start
        body.extend(parents[name][0][start:cursor])
        groups.append(group)
    footer[3] = TType.I64, sum(group[3][1] for group in groups)
    footer[4] = TType.LIST, (TType.STRUCT, groups)
    footer[6] = TType.STRING, b"Assembly of unchanged PyArrow 26.0.1 Zstandard V2 chunks"
    encoded = THRIFT["encode"](footer)
    return bytes(body) + encoded + pack("<I", len(encoded)) + b"PAR1"


def chunks(wire, group):
    for ordinal in range(group.num_columns):
        chunk = group.column(ordinal)
        start = chunk.dictionary_page_offset if chunk.has_dictionary_page else chunk.data_page_offset
        yield wire[start:start + chunk.total_compressed_size]


def selected_groups(wire):
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        return [file.read_row_group(i, columns=["blob"]).column(0).to_pylist() for i in range(file.num_row_groups)]


def inspect(mixed, parents):
    expected, geometry = [], []
    _, footer = PHYSICAL["read_footer"](mixed)
    leaf = THRIFT["list_field"](footer, 2)[2]
    assert leaf[1][1] == 6 and leaf[3][1] == 1 and 6 not in leaf and 10 not in leaf
    with pq.ParquetFile(pa.BufferReader(mixed), page_checksum_verification=True) as file:
        assert file.num_row_groups == len(ORDER)
        for index, (profile, ordinal) in enumerate(ORDER):
            source = parents[profile][0]
            with pq.ParquetFile(pa.BufferReader(source), page_checksum_verification=True) as parent:
                group = file.metadata.row_group(index)
                assert list(chunks(mixed, group)) == list(chunks(source, parent.metadata.row_group(ordinal)))
                rows = parent.read_row_group(ordinal).to_pydict()
                assert file.read_row_group(index).to_pydict() == rows
                expected.append(rows["blob"])
                chunk = group.column(1)
                assert chunk.compression == "ZSTD" and chunk.path_in_schema == "blob"
                assert chunk.has_dictionary_page == (profile != "plain")
                frames = PHYSICAL["frames"](mixed, chunk, True)
                data = frames[int(chunk.has_dictionary_page):]
                assert all(frame.fields[1][1] == 3 for frame in data)
                tags = [frame.fields[8][1][4][1] for frame in data]
                flags = [frame.fields[8][1][7][1] for frame in data]
                assert tags == {"plain": [0, 0, 0], "dictionary": [8] * len(data),
                                "fallback": [8, 8, 8, 0, 0]}[profile]
                geometry.append(frames)
                print(f"Assembled group {index}: {profile}, {len(rows['blob'])} rows, tags {tags}, flags {flags}", flush=True)
    return expected, geometry


def bad_crc(wire, frame):
    changed = wire[:frame.body] + bytes([wire[frame.body] ^ 1]) + wire[frame.body + 1:]
    wanted = frame.fields[4][1] % 2**32
    actual = crc32(changed[frame.body:frame.stop])
    assert wanted != actual
    return changed, wanted, actual


parents = pinned_parents()
cases = {f"native-{profile}": wire for profile, (wire, _) in parents.items()}
mixed = cases["assembled-mixed"] = assemble(parents)
expected, frames = inspect(mixed, parents)
plain, dictionary = frames[1][0], frames[3][0]
cases["assembled-bad-plain-crc"], plain_want, plain_got = bad_crc(mixed, plain)
cases["assembled-bad-dictionary-crc"], dict_want, dict_got = bad_crc(mixed, dictionary)
cases["assembled-double-crc"], _, _ = bad_crc(cases["assembled-bad-plain-crc"], dictionary)

_, _, _, last_dictionary, first_plain, _ = frames[2]
assert last_dictionary.stop == first_plain.header
dict_bytes = mixed[last_dictionary.header:last_dictionary.stop]
plain_bytes = mixed[first_plain.header:first_plain.stop]
revival_offset = last_dictionary.header + len(plain_bytes)
cases["assembled-revival"] = (
    mixed[:last_dictionary.header] + plain_bytes + dict_bytes + mixed[first_plain.stop:])

failures = {"assembled-bad-plain-crc": 1, "assembled-bad-dictionary-crc": 3,
            "assembled-double-crc": 1, "assembled-revival": 2}
for name, failed in failures.items():
    wire = cases[name]
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        assert [file.read_row_group(i, columns=["blob"]).column(0).to_pylist() for i in range(failed)] == expected[:failed]
        if name == "assembled-revival":
            reordered = PHYSICAL["frames"](wire, file.metadata.row_group(failed).column(1), True)
            assert [f.fields[8][1][4][1] for f in reordered[1:]] == [8, 8, 0, 8, 0]
            revived = reordered[4]
            assert revived.header == revival_offset and wire[revived.header:revived.stop] == dict_bytes
        else:
            try:
                file.read_row_group(failed, columns=["blob"])
            except OSError:
                pass
            else:
                raise AssertionError("PyArrow accepted the altered CRC")

for name, wire in cases.items():
    (OUT / f"{name}.parquet").write_bytes(wire)

evidence = [plain.header, dictionary.header, revival_offset, plain_want, plain_got, dict_want, dict_got]
subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                "--run", str(HERE / "Emit.lean"), str(OUT), *map(str, evidence)], cwd=ROOT, check=True)

outputs = ["native-plain", "native-dictionary", "native-fallback", "assembled-mixed"]
for name in outputs:
    output = (OUT / f"{name}.arrows").read_bytes()
    with pa.ipc.open_stream(output) as reader:
        assert reader.schema == pa.schema([pa.field("blob", pa.binary_view())])
        assert [batch.column(0).to_pylist() for batch in reader] == selected_groups(cases[name])
    if name.startswith("native-"):
        assert output == parents[name.removeprefix("native-")][1]

artifacts = [OUT / f"{name}.parquet" for name in cases] + [OUT / f"{name}.arrows" for name in outputs]
pins = {path.name: sha256(path.read_bytes()).hexdigest() for path in artifacts}
print(json.dumps(pins, indent=2), flush=True)
assert pins == json.loads((HERE / "fixtures.json").read_text())
print("PyArrow/Thrift: exact strict parent replay, unchanged assembled chunks and ordered BinaryView IPC")
