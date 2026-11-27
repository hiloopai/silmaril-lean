"""Compare recursive Parquet Zstd frames with a separately pinned libzstd."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
ZSTD = runpy.run_path(str(HERE.parent / "zstd-literal-oracle/check_frame.py"))
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
  unless binding.codec = .zstd ∧ binding.chunk.metadata.codec = 6 do
    throw (IO.userError "original Zstd column codec differs")
  let seen ← take (Parquet.RecursiveSchema.Repeated.Chunk.read {} binding)
  let decoded ← seen.pages.mapM fun page =>
    match page.frame.value.kind with
    | .dataV1 _ => take (readV1Body {} binding.codec input page.frame)
    | .dataV2 info => do
      let some spans := page.frame.v2Spans | throw (IO.userError "missing original V2 spans")
      take (readV2Suffix {} binding.codec binding.leaf page.frame info (bytesAt input spans.values))
    | _ => throw (IO.userError "unexpected page kind")
  unless decoded == wanted do throw (IO.userError "decoded body or suffix differs from libzstd")
"""


def frame_info(reference, wire):
    return tuple(int(value) for value in ZSTD["run"](reference, "frame-info", data=wire).split())


def block_kinds(wire, at, trailer):
    kinds = []
    while at < trailer:
        bits = int.from_bytes(wire[at:at+3], "little")
        kind, size = (bits >> 1) & 3, bits >> 3
        assert kind in (0, 1, 2)
        kinds.append(kind)
        at += 3 + (1 if kind == 1 else size)
        if bits & 1:
            assert at == trailer
            return kinds
    raise AssertionError("no last Zstd block")


def decode_frame(reference, wire, size):
    extent, header, window, content, dictionary, checksum = frame_info(reference, wire)
    assert wire[:4] == ZSTD["MAGIC"] and extent == len(wire)
    assert content in (size, 2**64 - 1) and dictionary == 0
    assert window <= 8 * 1024 * 1024
    block_kinds(wire, header, extent - 4 * checksum)
    raw = ZSTD["run"](reference, "decode", str(size), data=wire)
    assert len(raw) == size
    return raw


def parts(header, stored):
    if header[1][1] == 0:
        return b"", stored, header[2][1], True
    assert header[1][1] == 3
    level_prefix = EDIT["level_size"](header)
    assert level_prefix <= min(len(stored), header[2][1])
    return stored[:level_prefix], stored[level_prefix:], header[2][1] - level_prefix, EDIT["resolved"](header)


def controls(reference, native, location, name):
    def stored_crc(header, stored):
        return encode(header, stored[:-1] + bytes([stored[-1] ^ 1]), crc=False)

    def replace_frame(header, stored, edit):
        levels, frame, size, compressed = parts(header, stored)
        assert compressed
        return encode(header, levels + edit(frame, size))

    def checksummed(frame, size):
        raw = decode_frame(reference, frame, size)
        checked = ZSTD["run"](reference, "compress-checksum", data=raw)
        assert frame_info(reference, checked)[5] == 1
        assert decode_frame(reference, checked, size) == raw
        return checked

    def checksum_corrupt(frame, size):
        checked = checksummed(frame, size)
        return checked[:-1] + bytes([checked[-1] ^ 1])

    def content_size(frame, size):
        _, end, _, content, _, _ = frame_info(reference, frame)
        assert content == size and frame[4] >> 6 == 1
        encoded = int.from_bytes(frame[end-2:end], "little")
        return frame[:end-2] + (encoded + 1).to_bytes(2, "little") + frame[end:]

    def dictionary(frame, _):
        descriptor = frame[4]
        assert descriptor & 3 == 0
        at = 5 if descriptor & 32 else 6
        changed = frame[:4] + bytes([descriptor | 1]) + frame[5:at] + b"\x07" + frame[at:]
        assert frame_info(reference, changed)[4] == 7
        return changed

    def block_extent(frame, _):
        _, at, window, _, _, _ = frame_info(reference, frame)
        header = int.from_bytes(frame[at:at+3], "little")
        assert (header >> 1) & 3 == 2 and window < 131072
        too_large = (((window + 1) << 3) | (header & 7)).to_bytes(3, "little")
        return frame[:at] + too_large + frame[at+3:]

    def trailing_frame(frame, size):
        both = frame + frame
        assert frame_info(reference, both)[0] == len(frame) < len(both)
        assert len(ZSTD["run"](reference, "decode", str(2 * size), data=both)) == 2 * size
        return both

    def trailing_byte(frame, _):
        changed = frame + b"\0"
        assert frame_info(reference, changed)[0] == len(frame)
        return changed

    def truncated(frame, _):
        broken = frame[:-1]
        native = subprocess.run([reference, "frame-info"], input=broken, capture_output=True, check=False)
        assert native.returncode == 3
        return broken

    edits = (checksummed, checksum_corrupt, content_size, dictionary, block_extent,
             trailing_frame, trailing_byte, truncated)
    labeled = {f"{name}_stored_crc": replace_page(native, location, stored_crc)}
    for edit in edits:
        labeled[f"{name}_{edit.__name__}"] = replace_page(
            native, location, lambda header, stored: replace_frame(header, stored, edit))

    footer = MIXED["metadata"](native)
    leaf = THRIFT["column_metadata"](footer, *location[:2])
    leaf[6] = TType.I64, leaf[6][1] + 1
    labeled[f"{name}_footer_total"] = SCHEMA["pack"](native, footer)
    return labeled


def verify(scratch):
    reference = ZSTD["build_reference"](scratch)

    def decode_block(codec, block, size):
        assert codec == 6
        return decode_frame(reference, block, size)

    _, samples, _ = SCHEMA["fixtures"]()
    schema, rows = samples["nullable_lists"]
    packet = {"flag": 0, "items": [{"lo": -7, "nested": {"hi": -2**63}}] * 9}
    many = [{"packet": packet, "seq": 2**40}] * 16
    groups = [rows[:3], many + rows[3:]]
    genuine = {name: EDIT["write"](schema, groups, compression="ZSTD", page_version=version)
               for name, version in (("v1", "1.0"), ("v2", "2.0"))}
    genuine["pageless"] = EDIT["write"](schema, [groups[0], [], groups[1]], compression="ZSTD")
    for key, metadata, start, stop in V2["columns"](genuine["pageless"]):
        if key[0] == 1:
            assert [metadata[field][1] for field in (4, 5, 6, 7, 9)] == [6, 0, 0, 0, 0]
            assert start == stop == 0

    target = (1, 0, 0)
    labeled = {name: wire for label in ("v1", "v2")
               for name, wire in controls(reference, genuine[label], target, label).items()}
    files = genuine | labeled
    for name, wire in files.items():
        (scratch / f"{name}.parquet").write_bytes(wire)

    main = ["public def main (args : List String) : IO Unit := do",
            '  let [folder] := args | throw (IO.userError "expected fixture folder")']
    code, bridge = [LEAN, *main], [BRIDGE["LEAN"], *main]
    page_totals = {}
    raw_v2 = 0
    for label in ("v1", "v2", "v1_checksummed", "v2_checksummed"):
        wire = files[label]
        frames = raw_chunks(wire)
        assert all(col[4][1] == 6 for _, col, _, _ in V2["columns"](wire))
        original = list(V2["capture"](wire, schema, groups[0] + groups[1], codec=6, decode_block=decode_block))
        page_totals[label] = sum(len(column.pages) for column, _ in original)
        assert len(frames[1, 0]) > 1 and len(frames[1, 0]) != len(frames[1, 1])
        for column, spans in original:
            decoded = []
            for _, header, _, stored in frames[column.group, column.index]:
                _, block, size, compressed = parts(header, stored)
                ready = decode_block(6, block, size) if compressed else block
                assert len(ready) == size
                if label == "v2":
                    raw_v2 += not compressed
                decoded.append(f"(Bytes.ofList {list(ready)})")
            code.append(CHUNK["check_term"](column, label))
            code.append(f'  spans (← load folder "{label}") {column.group} {column.index} {lst(spans)}')
            code.append(f'  checkedBytes (← load folder "{label}") {column.group} {column.index} {lst(decoded)}')
        fields, observations, counts = BRIDGE["observed"](wire)
        assert counts == [3, 18]
        bridge.append(f'  emit folder "{label}" (← load folder "{label}") {fields} {observations}')
        if label.endswith("checksummed"):
            continue

        group, col, ordinal = target
        column = next(source for source, _ in original if (source.group, source.index) == (group, col))
        address = f"⟨{group}, {col}, {json.dumps(column.path, ensure_ascii=False)}⟩"
        state = EDIT["lean_state"](column.pages[ordinal].before)

        def page_error(fixture, cause, limits="{}"):
            at = raw_chunks(files[fixture])[group, col][ordinal][0]
            error = f".page {address} ⟨{ordinal}, {at}, {state}⟩ ({cause})"
            code.append(f'  refuse (← load folder "{fixture}") {group} {col} {limits} ({error})')
            return error

        def frame_error(fixture, cause, limits="{}"):
            return page_error(fixture, f".zstd (.frame (.frame ({cause})))", limits)

        _, header, _, stored = frames[group, col][ordinal]
        assert parts(header, stored)[3] and len(stored) < header[2][1]
        page_error(label, ".checksum .byteLimit", f"{{ maxBodyBytes := {len(stored) - 1} }}")
        output_limit = ".zstd (.scalar (.payload .outputLimit))" if label == "v1" else ".payload .outputLimit"
        page_error(label, output_limit, f"{{ maxBodyBytes := {len(stored)} }}")
        frame_error(label, ".windowLimit", "{ zstd := { ({} : Limits).zstd with window := 1 } }")
        page_error(label, ".zstd (.frame (.compressed (.block (.tables (.prefix .sequenceLimit)))))",
                   "{ zstd := { ({} : Limits).zstd with commandsPerBlock := 0 } }")
        _, changed, _, bad = raw_chunks(files[label + "_stored_crc"])[group, col][ordinal]
        page_error(label + "_stored_crc", f".checksum (.mismatch {changed[4][1] & 0xffffffff} {zlib.crc32(bad)})")
        late = frame_error(label + "_checksum_corrupt", ".checksumMismatch")
        for suffix, cause in (
            ("content_size", ".contentSizeMismatch"), ("dictionary", ".unsupportedDictionary 7"),
            ("block_extent", ".blockLimit"), ("trailing_frame", ".trailingInput"),
            ("trailing_byte", ".trailingInput"), ("truncated", ".truncated"),
        ):
            frame_error(f"{label}_{suffix}", cause)
        total = THRIFT["column_metadata"](MIXED["metadata"](wire), group, col)[6][1]
        code.append(f'  refuse (← load folder "{label}_footer_total") {group} {col} {{}} '
                    f'(.chunk {address} ⟨{column.start}, {column.stop}⟩ (.uncompressedSize {total + 1} {total}))')
        ending = f".readError (.group 1 (.chunk ({late})))"
        broken = f"{label}_checksum_corrupt"
        wide = BRIDGE["observed"](wire, limit=1)
        empty = BRIDGE["observed"](wire, positions=[], limit=1)
        bridge.extend([
            BRIDGE["check"](f"{label} late Zstd checksum", f'direct (← load folder "{broken}")', wide, ending),
            BRIDGE["check"](f"{label} projected late checksum", f'project (← load folder "{broken}") []',
                            empty, ending),
            f'  sourceFailure (← load folder "{broken}") (.chunk ({late}))',
        ])

    assert 0 < raw_v2 < page_totals["v2"]
    code.append('  deny (.original (.snapshot (.invalidMetadata .pageInterval))) (openFile {} (← load folder "pageless"))')
    V2["run_lean"](scratch, "Chunk.lean", code)
    V2["run_lean"](scratch, "Bridge.lean", bridge)

    ipc = {}
    for name in page_totals:
        raw = (scratch / f"{name}.arrow").read_bytes()
        parquet = pq.ParquetFile(pa.BufferReader(files[name]), page_checksum_verification=True)
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
    print(f"Checked {sum(page_totals.values())} pages including {raw_v2} genuine raw V2 suffixes, "
          "four native IPC streams and 27 typed refusals")
    return {"genuine_parquet": fingerprints(genuine), "labeled_edits": fingerprints(labeled),
            "lean_ipc": fingerprints(ipc)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    assert pins["libzstd"] == ZSTD["PIN"]
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for kind, values in captured.items():
        assert values == pins[kind], f"{kind} fixture pins changed"


if __name__ == "__main__":
    main()
