"""Check whole-body Snappy V1 frames and original recursive readback."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
SNAPPY = runpy.run_path(str(HERE.parent / "parquet-recursive-v2-snappy-oracle/check.py"))
V2, BRIDGE, SCHEMA, STREAM, CHUNK, THRIFT, MIXED, FRAMES, fingerprints, lst = (
    SNAPPY[key] for key in ("V2", "BRIDGE", "SCHEMA", "STREAM", "CHUNK", "THRIFT", "MIXED",
                            "FRAMES", "fingerprints", "lst")
)
encode, pack_chunks, raw_chunks, replace_page, lean_state = (
    SNAPPY[key] for key in ("encode", "pack_chunks", "raw_chunks", "replace_page", "lean_state")
)
CODEC = pa.Codec("snappy")

CHUNK_CHECK = V2["LEAN"] + """\

private def bodies (file : Bytes) (group column : Nat) (wanted : List (Option Bytes)) : IO Unit := do
  let source ← take (openFile {} file)
  let binding ← take (bindChunk source.schema group column)
  let seen ← take (Parquet.RecursiveSchema.Repeated.Chunk.read {} binding)
  let mut decoded := []
  for page in seen.pages do
    match page.frame.value.kind with
    | .dataV1 _ =>
      let body ← take (readV1Body {} binding.codec file page.frame)
      decoded := some body :: decoded
    | _ => decoded := none :: decoded
  unless decoded.reverse == wanted do throw (IO.userError "original decoded V1 bytes differ")
"""


def decode_v1(header, stored):
    assert header[1][1] == 0
    raw = CODEC.decompress(stored, header[2][1]).to_pybytes()
    assert len(raw) == header[2][1]
    return raw


def encode_v1(header, raw):
    header[2] = TType.I32, len(raw)
    return encode(header, CODEC.compress(raw).to_pybytes())


def authored_continuation(scratch, as_v2=None):
    """Re-encode the previously checked unindexed mid-row split with codec 1."""
    _, _, edits = CHUNK["continuation_fixtures"](scratch)
    original = edits["authored_continuation"]
    frames = SNAPPY["raw_chunks"](original)
    assert list(frames) == [(0, 0)]
    pages = []
    for ordinal, (_, header, _, body) in enumerate(frames[0, 0]):
        if ordinal == as_v2:
            frame = V2["from_v1"](header, body)
            [(_, v2_header, _, v2_body)] = list(FRAMES(frame, 0, len(frame)))
            pages.append(encode(v2_header, v2_body))
        else:
            pages.append(encode_v1(header, body))
    footer = MIXED["metadata"](original)
    leaf = THRIFT["column_metadata"](footer, 0, 0)
    leaf[4] = TType.I32, 1
    return pack_chunks(SCHEMA["pack"](original, footer), {(0, 0): b"".join(pages)})


def controls(wire, location):
    def stored_crc(header, stored):
        return encode(header, stored[:-1] + bytes([stored[-1] ^ 1]), crc=False)

    def decoded_crc(header, stored):
        digest = zlib.crc32(decode_v1(header, stored))
        header[4] = TType.I32, digest if digest < 2**31 else digest - 2**32
        return encode(header, stored, crc=False)

    def malformed(header, _):
        return encode(header, b"\x01")

    def short_output(header, _):
        return encode(header, b"\0")

    def trailing_input(header, stored):
        return encode(header, stored + b"\0")

    def short_value(header, stored):
        return encode_v1(header, decode_v1(header, stored)[:-1])

    def extra_value(header, stored):
        return encode_v1(header, decode_v1(header, stored) + b"\0")

    def slot_overrun(header, stored):
        group, column, _ = location
        total = THRIFT["column_metadata"](MIXED["metadata"](wire), group, column)[5][1]
        header[5][1][1] = TType.I32, total + 1
        return encode(header, stored)

    edited = {edit.__name__: replace_page(wire, location, edit) for edit in
              (stored_crc, decoded_crc, malformed, short_output, trailing_input,
               short_value, extra_value, slot_overrun)}
    footer = MIXED["metadata"](wire)
    leaf = THRIFT["column_metadata"](footer, *location[:2])
    leaf[6] = TType.I64, leaf[6][1] + 1
    edited["footer_total"] = SCHEMA["pack"](wire, footer)
    return edited


def verify(scratch):
    _, samples, _ = SCHEMA["fixtures"]()
    schema, rows = samples["nullable_lists"]
    packet = {"flag": 0, "items": [{"lo": -7, "nested": {"hi": -2**63}}] * 9}
    values = [{"packet": packet, "seq": 2**40}] * 16
    groups = [rows[:3], values + rows[3:]]
    native = SNAPPY["write"](schema, groups, page_version="1.0")
    genuine = {"native": native}
    native_frames = raw_chunks(native)
    assert len(native_frames[1, 0]) > 1 and len(native_frames[1, 1]) != len(native_frames[1, 0])
    target = (1, 0, 0)
    edited = controls(native, target)
    edited["continuation"] = authored_continuation(scratch)
    edited["mixed_boundary"] = authored_continuation(scratch, as_v2=1)
    edited["after_closed_v2"] = authored_continuation(scratch, as_v2=2)
    files = genuine | edited
    for name, wire in files.items():
        (scratch / f"{name}.parquet").write_bytes(wire)

    auth_schema = pq.ParquetFile(pa.BufferReader(files["continuation"])).schema_arrow
    auth_rows = [{"items": item} for item in CHUNK["CONT"]["CONTINUED"]]
    positives = {"native": (schema, groups), "continuation": (auth_schema, [auth_rows]),
                 "mixed_boundary": (auth_schema, [auth_rows])}
    entry = ["public def main (args : List String) : IO Unit := do",
             '  let [folder] := args | throw (IO.userError "expected fixture folder")']
    code, bridge = [CHUNK_CHECK, *entry], [BRIDGE["LEAN"], *entry]
    columns = {}
    frame_count = 0
    for label, (declarations, expected) in positives.items():
        wire = files[label]
        frames = raw_chunks(wire)
        observed = list(V2["capture"](wire, declarations, [row for group in expected for row in group], codec=1))
        frame_count += sum(len(column.pages) for column, _ in observed)
        columns[label] = {(column.group, column.index): column for column, _ in observed}
        for column, spans in observed:
            code.append(CHUNK["check_term"](column, label))
            code.append(f'  spans (← load folder "{label}") {column.group} {column.index} {lst(spans)}')
            bodies = lst(f"(some (Bytes.ofList {list(decode_v1(header, stored))}))" if header[1][1] == 0 else "none"
                         for _, header, _, stored in frames[column.group, column.index])
            code.append(f'  bodies (← load folder "{label}") {column.group} {column.index} {bodies}')
        fields, groups_term, counts = BRIDGE["observed"](wire)
        assert counts == [len(group) for group in expected]
        bridge.append(f'  emit folder "{label}" (← load folder "{label}") {fields} {groups_term}')
    auth = columns["continuation"][0, 0]
    assert auth.pages[-2].after[2] and auth.pages[-1].before[2]
    assert auth.pages[-1].events[0][0] == 1
    assert auth.pages[-1].after[1] == auth.pages[-1].before[1]
    assert not columns["mixed_boundary"][0, 0].pages[2].before[2]

    group, col, ordinal = target
    original = columns["native"][group, col]
    _, header, _, stored = native_frames[group, col][ordinal]
    assert len(stored) < header[2][1]
    path = json.dumps(original.path, ensure_ascii=False)
    address = f"⟨{group}, {col}, {path}⟩"

    def page_error(label, cause, limits="{}"):
        byte = raw_chunks(files[label])[group, col][ordinal][0]
        before = lean_state(original.pages[ordinal].before)
        error = f".page {address} ⟨{ordinal}, {byte}, {before}⟩ ({cause})"
        code.append(f'  refuse (← load folder "{label}") {group} {col} {limits} ({error})')
        return error

    for name in ("stored_crc", "decoded_crc"):
        _, changed, _, body = raw_chunks(files[name])[group, col][ordinal]
        page_error(name, f".checksum (.mismatch {changed[4][1] & 0xffffffff} {zlib.crc32(body)})")
    late = page_error("malformed", ".payload (.malformed .snappy)")
    page_error("short_output", ".payload .outputSizeMismatch")
    page_error("trailing_input", ".payload (.trailingInput .snappy)")
    page_error("short_value", ".plain .truncated")
    page_error("extra_value", ".plain .trailingBytes")
    page_error("slot_overrun", f".slotOverrun {original.slots} {original.slots + 1}")
    page_error("native", ".payload .outputLimit", f"{{ maxBodyBytes := {len(stored)} }}")
    page_error("native", ".checksum .byteLimit", f"{{ maxBodyBytes := {len(stored) - 1} }}")
    total = THRIFT["column_metadata"](MIXED["metadata"](native), group, col)[6][1]
    code.append(f'  refuse (← load folder "footer_total") {group} {col} {{}} '
                f'(.chunk {address} ⟨{original.start}, {original.stop}⟩ (.uncompressedSize {total + 1} {total}))')
    boundary = raw_chunks(files["after_closed_v2"])[0, 0][-1][0]
    slot, row, _ = auth.pages[-1].before
    closed = lean_state((slot, row, False))
    code.append('  refuse (← load folder "after_closed_v2") 0 0 {} '
                f'(.page ⟨0, 0, ["items", "list", "element"]⟩ ⟨3, {boundary}, {closed}⟩ '
                f'(.continuationWithoutList {slot}))')

    terminal = f".readError (.group 1 (.chunk ({late})))"
    bridge.extend([
        BRIDGE["check"]("V1 Snappy late error", 'direct (← load folder "malformed")',
                        BRIDGE["observed"](native, limit=1), terminal),
        BRIDGE["check"]("V1 Snappy projected late error", 'project (← load folder "malformed") []',
                        BRIDGE["observed"](native, positions=[], limit=1), terminal),
        f'  sourceFailure (← load folder "malformed") (.chunk ({late}))',
    ])
    V2["run_lean"](scratch, "Chunk.lean", code)
    V2["run_lean"](scratch, "Bridge.lean", bridge)
    ipc = {}
    for label, (schema, expected) in positives.items():
        wire = (scratch / f"{label}.arrow").read_bytes()
        reader = pa.ipc.open_stream(wire)
        assert reader.schema == schema
        assert [batch.to_pylist() for batch in reader] == expected
        _, cursor = STREAM["metadata"](wire)
        for group in expected:
            frame = STREAM["read_record"](wire, cursor)
            assert frame.rows == len(group)
            cursor = frame.end
        assert wire[cursor:] == STREAM["EOS"]
        ipc[label] = wire
    print(f"Checked {frame_count} original pages, three native IPC streams and twelve typed refusals")
    return {"genuine_parquet": fingerprints(genuine), "labeled_edits": fingerprints(edited),
            "lean_ipc": fingerprints(ipc)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for kind, values in captured.items():
        assert values == pins[kind], f"{kind} fixture pins changed"


if __name__ == "__main__":
    main()
