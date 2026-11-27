"""Check native Parquet LZ4_RAW V1/V2 against a distinct pinned block decoder."""

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
LZ4 = runpy.run_path(str(HERE.parent / "lz4-raw-oracle/check.py"))
EDIT = runpy.run_path(str(HERE.parent / "parquet-recursive-v2-snappy-oracle/check.py"))
V2, BRIDGE, SCHEMA, STREAM, CHUNK, THRIFT, MIXED, fingerprints, lst = (
    EDIT[key] for key in ("V2", "BRIDGE", "SCHEMA", "STREAM", "CHUNK", "THRIFT", "MIXED",
                          "fingerprints", "lst")
)
encode, raw_chunks, replace_page = (EDIT[key] for key in ("encode", "raw_chunks", "replace_page"))

LEAN = V2["LEAN"] + """\

private def checkedBytes (input : Bytes) (group column : Nat) (wanted : List Bytes) : IO Unit := do
  let source ← take (openFile {} input)
  let binding ← take (bindChunk source.schema group column)
  unless binding.codec = .lz4Raw ∧ binding.chunk.metadata.codec = 7 do
    throw (IO.userError "original codec was not retained")
  let seen ← take (Parquet.RecursiveSchema.Repeated.Chunk.read {} binding)
  let decoded ← seen.pages.mapM fun page =>
    match page.frame.value.kind with
    | .dataV1 _ => take (readV1Body {} binding.codec input page.frame)
    | .dataV2 info => do
      let some spans := page.frame.v2Spans | throw (IO.userError "missing original V2 spans")
      take (readV2Suffix {} binding.codec binding.leaf page.frame info (bytesAt input spans.values))
    | _ => throw (IO.userError "unexpected page kind")
  unless decoded == wanted do throw (IO.userError "checked body or suffix differs from liblz4")
"""


def parts(header, stored):
    """Return the untouched V2 levels and the independently encoded value range."""
    if header[1][1] == 0:
        return b"", stored, header[2][1], True
    assert header[1][1] == 3
    level_prefix = EDIT["level_size"](header)
    assert 0 <= level_prefix <= min(len(stored), header[2][1])
    return stored[:level_prefix], stored[level_prefix:], header[2][1] - level_prefix, EDIT["resolved"](header)


def controls(reference, native, location, name):
    def stored_crc(header, stored):
        return encode(header, stored[:-1] + bytes([stored[-1] ^ 1]), crc=False)

    def malformed(header, stored):
        levels, _, size, compressed = parts(header, stored)
        assert compressed and reference(b"\xf0", size) is None
        return encode(header, levels + b"\xf0")

    def wrong_decoded_extent(header, stored):
        levels, _, size, compressed = parts(header, stored)
        assert compressed and reference(b"\0", size) in (None, b"")
        return encode(header, levels + b"\0")

    def framed_lz4(header, stored):
        levels, block, size, compressed = parts(header, stored)
        assert compressed
        decoded = reference(block, size)
        framed = pa.Codec("lz4").compress(decoded).to_pybytes()
        assert framed.startswith(bytes.fromhex("04 22 4d 18"))
        assert reference(framed, size) != decoded
        return encode(header, levels + framed)

    edits = (stored_crc, malformed, wrong_decoded_extent)
    if name == "v1":
        edits += (framed_lz4,)
    labeled = {f"{name}_{edit.__name__}": replace_page(native, location, edit) for edit in edits}

    footer = MIXED["metadata"](native)
    col = THRIFT["column_metadata"](footer, *location[:2])
    col[6] = TType.I64, col[6][1] + 1
    labeled[f"{name}_footer_total"] = SCHEMA["pack"](native, footer)

    footer = MIXED["metadata"](native)
    leaf = THRIFT["column_metadata"](footer, 0, 0)
    leaf[4] = TType.I32, 5
    labeled[f"{name}_legacy_id"] = SCHEMA["pack"](native, footer)
    return labeled


def verify(scratch):
    lib = LZ4["build_reference"](scratch)

    def reference(block, size):
        return LZ4["reference_decode"](lib, block, size)

    def decode_block(codec, block, size):
        assert codec == 7
        decoded = reference(block, size)
        assert decoded is not None and len(decoded) == size
        return decoded

    _, samples, _ = SCHEMA["fixtures"]()
    schema, rows = samples["nullable_lists"]
    packet = {"flag": 0, "items": [{"lo": -7, "nested": {"hi": -2**63}}] * 9}
    many = [{"packet": packet, "seq": 2**40}] * 16
    groups = [rows[:3], many + rows[3:]]
    genuine = {name: EDIT["write"](schema, groups, compression="LZ4", page_version=version)
               for name, version in (("v1", "1.0"), ("v2", "2.0"))}
    genuine["pageless"] = EDIT["write"](schema, [groups[0], [], groups[1]], compression="LZ4")
    for key, metadata, start, stop in V2["columns"](genuine["pageless"]):
        if key[0] == 1:
            assert [metadata[field][1] for field in (4, 5, 6, 7, 9)] == [7, 0, 0, 0, 0]
            assert start == stop == 0

    target = (1, 0, 0)
    labeled = {}
    for label in ("v1", "v2"):
        labeled.update(controls(reference, genuine[label], target, label))
    files = genuine | labeled
    for name, wire in files.items():
        (scratch / f"{name}.parquet").write_bytes(wire)

    entry = ["public def main (args : List String) : IO Unit := do",
             '  let [folder] := args | throw (IO.userError "expected fixture folder")']
    code, bridge = [LEAN, *entry], [BRIDGE["LEAN"], *entry]
    page_totals = {}
    raw_v2 = 0
    for label in ("v1", "v2"):
        wire = genuine[label]
        frames = raw_chunks(wire)
        assert all(col[4][1] == 7 for _, col, _, _ in V2["columns"](wire))
        original = list(V2["capture"](wire, schema, groups[0] + groups[1], codec=7, decode_block=decode_block))
        page_totals[label] = sum(len(column.pages) for column, _ in original)
        assert len(frames[1, 0]) > 1 and len(frames[1, 0]) != len(frames[1, 1])
        for column, spans in original:
            raw_bytes = []
            for _, header, _, stored in frames[column.group, column.index]:
                _, data, size, compressed = parts(header, stored)
                ready = decode_block(7, data, size) if compressed else data
                assert len(ready) == size
                if label == "v2" and not compressed:
                    raw_v2 += 1
                raw_bytes.append(f"(Bytes.ofList {list(ready)})")
            code.append(CHUNK["check_term"](column, label))
            code.append(f'  spans (← load folder "{label}") {column.group} {column.index} {lst(spans)}')
            code.append(f'  checkedBytes (← load folder "{label}") {column.group} {column.index} {lst(raw_bytes)}')
        fields, observations, counts = BRIDGE["observed"](wire)
        assert counts == [3, 18]
        bridge.append(f'  emit folder "{label}" (← load folder "{label}") {fields} {observations}')

        group, col, ordinal = target
        column = next(source for source, _ in original if (source.group, source.index) == (group, col))
        address = f"⟨{group}, {col}, {json.dumps(column.path, ensure_ascii=False)}⟩"
        start_state = EDIT["lean_state"](column.pages[ordinal].before)

        def page_error(fixture, cause, limits="{}"):
            at = raw_chunks(files[fixture])[group, col][ordinal][0]
            error = f".page {address} ⟨{ordinal}, {at}, {start_state}⟩ ({cause})"
            code.append(f'  refuse (← load folder "{fixture}") {group} {col} {limits} ({error})')
            return error

        _, header, _, stored = frames[group, col][ordinal]
        assert parts(header, stored)[3] and len(stored) < header[2][1]
        page_error(label, ".checksum .byteLimit", f"{{ maxBodyBytes := {len(stored) - 1} }}")
        page_error(label, ".payload .outputLimit", f"{{ maxBodyBytes := {len(stored)} }}")
        _, changed, _, corrupted = raw_chunks(files[label + "_stored_crc"])[group, col][ordinal]
        page_error(label + "_stored_crc", f".checksum (.mismatch {changed[4][1] & 0xffffffff} {zlib.crc32(corrupted)})")
        late = page_error(label + "_malformed", ".payload (.malformed .lz4Raw)")
        page_error(label + "_wrong_decoded_extent", ".payload .outputSizeMismatch")
        if label == "v1":
            page_error("v1_framed_lz4", ".payload .outputSizeMismatch")
        total = THRIFT["column_metadata"](MIXED["metadata"](wire), group, col)[6][1]
        code.append(f'  refuse (← load folder "{label}_footer_total") {group} {col} {{}} '
                    f'(.chunk {address} ⟨{column.start}, {column.stop}⟩ (.uncompressedSize {total + 1} {total}))')
        code.append(f'  bindFailure (← load folder "{label}_legacy_id") 0 0 '
                    '(.column ⟨0, 0, ["packet", "items", "list", "élément", "lo"]⟩ (.codec 5))')
        terminal = f".readError (.group 1 (.chunk ({late})))"
        fixture = f'{label}_malformed'
        bridge.extend([
            BRIDGE["check"](f"{label} late error", f'direct (← load folder "{fixture}")',
                            BRIDGE["observed"](wire, limit=1), terminal),
            BRIDGE["check"](f"{label} projected error", f'project (← load folder "{fixture}") []',
                            BRIDGE["observed"](wire, positions=[], limit=1), terminal),
            f'  sourceFailure (← load folder "{fixture}") (.chunk ({late}))',
        ])

    assert 0 < raw_v2 < page_totals["v2"]
    code.append('  deny (.original (.snapshot (.invalidMetadata .pageInterval))) (openFile {} (← load folder "pageless"))')
    V2["run_lean"](scratch, "Chunk.lean", code)
    V2["run_lean"](scratch, "Bridge.lean", bridge)

    ipc = {}
    for label in page_totals:
        raw = (scratch / f"{label}.arrow").read_bytes()
        parquet = pq.ParquetFile(pa.BufferReader(genuine[label]), page_checksum_verification=True)
        reader = pa.ipc.open_stream(raw)
        assert reader.schema == parquet.schema_arrow == schema
        assert [batch.to_pylist() for batch in reader] == groups
        _, cursor = STREAM["metadata"](raw)
        for group in groups:
            frame = STREAM["read_record"](raw, cursor)
            assert frame.rows == len(group)
            cursor = frame.end
        assert raw[cursor:] == STREAM["EOS"]
        ipc[label] = raw
    print(f"Checked {page_totals['v1']} V1 pages, {page_totals['v2']} V2 pages ({raw_v2} raw suffixes), "
          "two native IPC streams and sixteen typed refusals")
    return {"genuine_parquet": fingerprints(genuine), "labeled_edits": fingerprints(labeled),
            "lean_ipc": fingerprints(ipc)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    assert pins["liblz4"] == LZ4["PIN"]
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for kind, values in captured.items():
        assert values == pins[kind], f"{kind} fixture pins changed"


if __name__ == "__main__":
    main()
