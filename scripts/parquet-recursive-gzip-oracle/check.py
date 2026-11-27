"""Inspect exactly one RFC 1952 member per compressed V1 body or V2 suffix."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import struct
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
EDIT = runpy.run_path(str(HERE.parent / "parquet-recursive-v2-snappy-oracle/check.py"))
V2, BRIDGE, SCHEMA, STREAM, CHUNK, THRIFT, MIXED, fingerprints, lst = (
    EDIT[key] for key in ("V2", "BRIDGE", "SCHEMA", "STREAM", "CHUNK", "THRIFT", "MIXED",
                          "fingerprints", "lst")
)
encode, raw_chunks, replace_page = (EDIT[key] for key in ("encode", "raw_chunks", "replace_page"))
EMPTY_MEMBER = bytes.fromhex("1f8b080000000000020303000000000000000000")

LEAN = V2["LEAN"] + """\

private def checkedBytes (input : Bytes) (group column : Nat) (wanted : List Bytes) : IO Unit := do
  let source ← take (openFile {} input)
  let binding ← take (bindChunk source.schema group column)
  unless binding.codec = .gzip ∧ binding.chunk.metadata.codec = 2 do
    throw (IO.userError "original GZIP column codec differs")
  let seen ← take (Parquet.RecursiveSchema.Repeated.Chunk.read {} binding)
  let decoded ← seen.pages.mapM fun page =>
    match page.frame.value.kind with
    | .dataV1 _ => take (readV1Body {} binding.codec input page.frame)
    | .dataV2 info => do
      let some spans := page.frame.v2Spans | throw (IO.userError "missing original V2 spans")
      take (readV2Suffix {} binding.codec binding.leaf page.frame info (bytesAt input spans.values))
    | _ => throw (IO.userError "unexpected page kind")
  unless decoded == wanted do throw (IO.userError "decoded body or suffix differs from zlib")
"""

BRIDGE_LEAN = BRIDGE["LEAN"] + """\

private def projectWithoutCalls (input : Bytes) : EventStream :=
  readProjected {} { chunk.gzipCalls := 0 } input (fun source => selection source [])
"""


def first_member(block, size):
    """Bound zlib output, require a completed trailer, and report unused input."""
    z = zlib.decompressobj(16 + zlib.MAX_WBITS)
    raw = z.decompress(block, size + 1)
    assert z.eof and not z.unconsumed_tail and len(raw) == size
    end = len(block) - len(z.unused_data)
    crc, isize = struct.unpack_from("<II", block, end - 8)
    assert crc == zlib.crc32(raw) and isize == size
    return raw, z.unused_data


def decode_block(codec, block, size):
    assert codec == 2 and block.startswith(b"\x1f\x8b\x08")
    raw, unread = first_member(block, size)
    assert unread == b""
    return raw


def parts(header, stored):
    if header[1][1] == 0:
        return b"", stored, header[2][1], True
    assert header[1][1] == 3
    level_prefix = EDIT["level_size"](header)
    assert level_prefix <= min(len(stored), header[2][1])
    return stored[:level_prefix], stored[level_prefix:], header[2][1] - level_prefix, EDIT["resolved"](header)


def controls(native, location, name):
    def stored_crc(header, stored):
        return encode(header, stored[:-1] + bytes([stored[-1] ^ 1]), crc=False)

    def replace_member(header, stored, edit):
        levels, member, size, compressed = parts(header, stored)
        assert compressed
        decode_block(2, member, size)
        return encode(header, levels + edit(member, size))

    def bad_trailer(member, size, distance):
        offset = len(member) - distance
        broken = member[:offset] + bytes([member[offset] ^ 1]) + member[offset + 1:]
        try:
            first_member(broken, size)
        except zlib.error:
            return broken
        raise AssertionError("zlib accepted a corrupt GZIP trailer")

    def trailing(member, size):
        wire = member + b"\0"
        assert first_member(wire, size)[1] == b"\0"
        return wire

    def second_member(member, size):
        wire = member + member
        assert first_member(wire, size)[1] == member
        return wire

    def short_output(_, size):
        assert size > 0 and decode_block(2, EMPTY_MEMBER, 0) == b""
        return EMPTY_MEMBER

    suffix_edits = {
        "gzip_crc": lambda member, size: bad_trailer(member, size, 8),
        "gzip_isize": lambda member, size: bad_trailer(member, size, 4),
        "trailing": trailing,
        "second_member": second_member,
        "short_output": short_output,
    }
    labeled = {f"{name}_stored_crc": replace_page(native, location, stored_crc)}
    for suffix, edit in suffix_edits.items():
        labeled[f"{name}_{suffix}"] = replace_page(
            native, location, lambda header, stored: replace_member(header, stored, edit))

    footer = MIXED["metadata"](native)
    leaf = THRIFT["column_metadata"](footer, *location[:2])
    leaf[6] = TType.I64, leaf[6][1] + 1
    labeled[f"{name}_footer_total"] = SCHEMA["pack"](native, footer)
    return labeled


def verify(scratch):
    _, samples, _ = SCHEMA["fixtures"]()
    schema, rows = samples["nullable_lists"]
    packet = {"flag": 0, "items": [{"lo": -7, "nested": {"hi": -2**63}}] * 9}
    many = [{"packet": packet, "seq": 2**40}] * 16
    groups = [rows[:3], many + rows[3:]]
    genuine = {name: EDIT["write"](schema, groups, compression="GZIP", page_version=version)
               for name, version in (("v1", "1.0"), ("v2", "2.0"))}
    genuine["pageless"] = EDIT["write"](schema, [groups[0], [], groups[1]], compression="GZIP")
    for key, metadata, start, stop in V2["columns"](genuine["pageless"]):
        if key[0] == 1:
            assert [metadata[field][1] for field in (4, 5, 6, 7, 9)] == [2, 0, 0, 0, 0]
            assert start == stop == 0

    target = (1, 0, 0)
    labeled = {name: wire for label in ("v1", "v2")
               for name, wire in controls(genuine[label], target, label).items()}
    files = genuine | labeled
    for name, wire in files.items():
        (scratch / f"{name}.parquet").write_bytes(wire)

    main = ["public def main (args : List String) : IO Unit := do",
            '  let [folder] := args | throw (IO.userError "expected fixture folder")']
    code, bridge = [LEAN, *main], [BRIDGE_LEAN, *main]
    page_totals = {}
    raw_v2 = 0
    for label in ("v1", "v2"):
        wire = genuine[label]
        frames = raw_chunks(wire)
        assert all(col[4][1] == 2 for _, col, _, _ in V2["columns"](wire))
        original = list(V2["capture"](wire, schema, groups[0] + groups[1], codec=2, decode_block=decode_block))
        page_totals[label] = sum(len(column.pages) for column, _ in original)
        assert len(frames[1, 0]) > 1 and len(frames[1, 0]) != len(frames[1, 1])
        for column, spans in original:
            decoded = []
            for _, header, _, stored in frames[column.group, column.index]:
                _, block, size, compressed = parts(header, stored)
                ready = decode_block(2, block, size) if compressed else block
                assert len(ready) == size
                if label == "v2":
                    raw_v2 += not compressed
                    if column.group == 0:
                        assert not compressed
                decoded.append(f"(Bytes.ofList {list(ready)})")
            code.append(CHUNK["check_term"](column, label))
            code.append(f'  spans (← load folder "{label}") {column.group} {column.index} {lst(spans)}')
            code.append(f'  checkedBytes (← load folder "{label}") {column.group} {column.index} {lst(decoded)}')
        fields, observations, counts = BRIDGE["observed"](wire)
        assert counts == [3, 18]
        bridge.append(f'  emit folder "{label}" (← load folder "{label}") {fields} {observations}')

        group, col, ordinal = target
        column = next(source for source, _ in original if (source.group, source.index) == (group, col))
        address = f"⟨{group}, {col}, {json.dumps(column.path, ensure_ascii=False)}⟩"
        state = EDIT["lean_state"](column.pages[ordinal].before)

        def page_error(fixture, cause, limits="{}"):
            at = raw_chunks(files[fixture])[group, col][ordinal][0]
            error = f".page {address} ⟨{ordinal}, {at}, {state}⟩ ({cause})"
            code.append(f'  refuse (← load folder "{fixture}") {group} {col} {limits} ({error})')
            return error

        _, header, _, stored = frames[group, col][ordinal]
        assert parts(header, stored)[3] and len(stored) < header[2][1]
        page_error(label, ".checksum .byteLimit", f"{{ maxBodyBytes := {len(stored) - 1} }}")
        page_error(label, ".payload .outputLimit", f"{{ maxBodyBytes := {len(stored)}, gzipCalls := 0 }}")
        no_calls = page_error(label, ".payload .gzipIncomplete", "{ gzipCalls := 0 }")
        page_error(label, ".payload .gzipIncomplete", "{ gzipCalls := 1 }")
        _, changed, _, bad = raw_chunks(files[label + "_stored_crc"])[group, col][ordinal]
        page_error(label + "_stored_crc",
                   f".checksum (.mismatch {changed[4][1] & 0xffffffff} {zlib.crc32(bad)})",
                   "{ gzipCalls := 0 }")
        late = page_error(label + "_gzip_crc", ".payload (.malformed .gzip)")
        page_error(label + "_gzip_isize", ".payload (.malformed .gzip)")
        page_error(label + "_trailing", ".payload (.trailingInput .gzip)")
        page_error(label + "_second_member", ".payload (.trailingInput .gzip)")
        page_error(label + "_short_output", ".payload .outputSizeMismatch")
        total = THRIFT["column_metadata"](MIXED["metadata"](wire), group, col)[6][1]
        code.append(f'  refuse (← load folder "{label}_footer_total") {group} {col} {{}} '
                    f'(.chunk {address} ⟨{column.start}, {column.stop}⟩ (.uncompressedSize {total + 1} {total}))')
        terminal = f".readError (.group 1 (.chunk ({late})))"
        fixture = f"{label}_gzip_crc"
        wide = BRIDGE["observed"](wire, limit=1)
        empty = BRIDGE["observed"](wire, positions=[], limit=1)
        bridge.extend([
            BRIDGE["check"](f"{label} late GZIP trailer", f'direct (← load folder "{fixture}")', wide, terminal),
            BRIDGE["check"](f"{label} projected late trailer", f'project (← load folder "{fixture}") []',
                            empty, terminal),
            f'  sourceFailure (← load folder "{fixture}") (.chunk ({late}))',
        ])
        if label == "v2":
            bridge.append(BRIDGE["check"]("V2 raw prefix at zero GZIP calls", 'projectWithoutCalls (← load folder "v2")',
                                          empty, f".readError (.group 1 (.chunk ({no_calls})))"))

    assert 0 < raw_v2 < page_totals["v2"]
    code.append('  deny (.original (.snapshot (.invalidMetadata .pageInterval))) (openFile {} (← load folder "pageless"))')
    V2["run_lean"](scratch, "Chunk.lean", code)
    V2["run_lean"](scratch, "Bridge.lean", bridge)

    ipc = {}
    for name in page_totals:
        raw = (scratch / f"{name}.arrow").read_bytes()
        parquet = pq.ParquetFile(pa.BufferReader(genuine[name]), page_checksum_verification=True)
        reader = pa.ipc.open_stream(raw)
        assert reader.schema == parquet.schema_arrow == schema
        assert [batch.to_pylist() for batch in reader] == groups
        _, cursor = STREAM["metadata"](raw)
        for group in groups:
            frame = STREAM["read_record"](raw, cursor)
            assert frame.rows == len(group)
            cursor = frame.end
        assert raw[cursor:] == STREAM["EOS"]
        ipc[name] = raw
    print(f"Checked {page_totals['v1']} V1 pages and {page_totals['v2']} V2 pages ({raw_v2} raw suffixes), "
          "two native IPC streams and 23 typed refusals")
    return {"genuine_parquet": fingerprints(genuine), "labeled_edits": fingerprints(labeled),
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
