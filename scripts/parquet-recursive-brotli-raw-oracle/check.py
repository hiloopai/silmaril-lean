"""Inspect opt-in recursive codec-4 raw streams against pinned libbrotli."""

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
BROTLI = runpy.run_path(str(HERE.parent / "parquet-brotli-raw/check.py"))
RAW = runpy.run_path(str(HERE.parent / "brotli-raw-oracle/check.py"))
EDIT = runpy.run_path(str(HERE.parent / "parquet-recursive-v2-snappy-oracle/check.py"))
V2, BRIDGE, SCHEMA, STREAM, CHUNK, THRIFT, MIXED, fingerprints, lst = (
    EDIT[key] for key in ("V2", "BRIDGE", "SCHEMA", "STREAM", "CHUNK", "THRIFT", "MIXED",
                          "fingerprints", "lst")
)
encode, raw_chunks, replace_page, pack_chunks = (
    EDIT[key] for key in ("encode", "raw_chunks", "replace_page", "pack_chunks")
)
LIMITS = "{ brotliRaw := some ⟨2 ^ 24 - 16, 16⟩ }"
NO_WORK = "{ brotliRaw := some ⟨2 ^ 24 - 16, 0⟩ }"

LEAN = V2["LEAN"] + """\

private def checkedBytes (input : Bytes) (group column : Nat) (wanted : List Bytes)
    (limits : Limits) : IO Unit := do
  let source ← take (openFile {} input)
  let binding ← take (bindChunk source.schema group column limits)
  unless binding.codec = .brotliRaw ∧ binding.chunk.metadata.codec = 4 do
    throw (IO.userError "original Brotli column codec differs")
  let seen ← take (Parquet.RecursiveSchema.Repeated.Chunk.read limits binding)
  let decoded ← seen.pages.mapM fun page =>
    match page.frame.value.kind with
    | .dataV1 _ => take (readV1Body limits binding.codec input page.frame)
    | .dataV2 info => do
      let some spans := page.frame.v2Spans | throw (IO.userError "missing original V2 spans")
      take (readV2Suffix limits binding.codec binding.leaf page.frame info (bytesAt input spans.values))
    | _ => throw (IO.userError "unexpected page kind")
  unless decoded == wanted do throw (IO.userError "decoded body or suffix differs from libbrotli")
"""

BRIDGE_LEAN = BRIDGE["LEAN"] + """\

private def options : Parquet.RecursiveSchema.Repeated.Rows.Limits :=
  { chunk.brotliRaw := some ⟨2 ^ 24 - 16, 16⟩ }

private def directRaw (input : Bytes) : EventStream :=
  Parquet.RecursiveSchema.Repeated.Rows.Events.read {} options input

private def projectRaw (input : Bytes) : EventStream :=
  readProjected {} options input (fun source => selection source [])

private def projectNoWork (input : Bytes) : EventStream :=
  readProjected {} { chunk.brotliRaw := some ⟨2 ^ 24 - 16, 0⟩ } input
    (fun source => selection source [])

private def emitRaw (folder : System.FilePath) (label : String) (input : Bytes)
    (fields : List (Option String × Field)) (batches : List Observation) : IO Unit := do
  check label (directRaw input) fields batches .eos
  let source ← take (openFile {} input)
  let wire ← take (convert options {} source.schema)
  check label (Arrow.RecursiveSchema.Stream.Events.read {} wire) fields batches .eos
  IO.FS.writeBinFile (folder / (label ++ ".arrow")) wire.toByteArray

private def sourceFailureRaw (input : Bytes) (wanted : Parquet.RecursiveSchema.Repeated.Rows.Error) :
    IO Unit := do
  let source ← take (openFile {} input)
  refuse (.source wanted) (convert options { schema.ipc := { fields := 0, batches := 0 }, slots := 0 }
    source.schema)
"""


def raw_blocks(stream):
    """Inspect the raw headers independently, including the final fill and extent."""
    bits, at = int.from_bytes(stream, "little"), 0

    def take(width):
        nonlocal at
        assert at + width <= 8 * len(stream)
        result = (bits >> at) & ((1 << width) - 1)
        at += width
        return result

    def align():
        assert take((-at) % 8) == 0

    if take(1) == 0:
        window = 16
    else:
        short = take(3)
        if short:
            window = 17 + short
        else:
            long = take(3)
            assert long != 1
            window = 17 if long == 0 else 8 + long
    chunks = []
    while True:
        if take(1):
            if not take(1):
                return "compressed", window, chunks
            align()
            assert at == 8 * len(stream)
            return "raw", window, chunks
        selector = take(2)
        if selector == 3:
            return "metadata", window, chunks
        minus_one = take(16 + 4 * selector)
        assert selector == 0 or minus_one >= 1 << (12 + 4 * selector)
        if not take(1):
            return "compressed", window, chunks
        align()
        start = at // 8
        end = start + minus_one + 1
        assert end <= len(stream)
        chunks.append(stream[start:end])
        at = end * 8


def raw_stream(plain):
    assert len(plain) <= 65536
    return RAW["raw_stream"](plain, 0, 1, 4) if plain else b"\x06"


def parts(header, stored):
    if header[1][1] == 0:
        return b"", stored, header[2][1], True
    assert header[1][1] == 3
    extent = EDIT["level_size"](header)
    assert extent <= min(len(stored), header[2][1])
    return stored[:extent], stored[extent:], header[2][1] - extent, EDIT["resolved"](header)


def pyarrow_brotli(schema, groups, page_version, level):
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, compression="BROTLI", compression_level=level,
                          use_dictionary=False, use_compliant_nested_type=False, store_schema=False,
                          data_page_version=page_version, write_page_checksum=True,
                          write_page_index=False, write_statistics=True,
                          data_page_size=256, write_batch_size=8, max_rows_per_page=12) as writer:
        for rows in groups:
            writer.write_table(pa.Table.from_pylist(rows, schema=schema))
    return sink.getvalue().to_pybytes()


def author(source):
    """Replace whole V1 bodies or V2 suffixes and preserve the raw level bytes."""
    chunks = {}
    for key, frames in raw_chunks(source).items():
        pages = []
        for _, header, _, body in frames:
            levels, plain, size, _ = parts(header, body)
            assert len(plain) == size
            v1 = header[1][1] == 0
            compressed = v1 or key[0] != 0
            if not v1:
                header[8][1][7] = TType.BOOL, compressed
            pages.append(encode(header, levels + (raw_stream(plain) if compressed else plain)))
        chunks[key] = b"".join(pages)
    footer = MIXED["metadata"](source)
    for group in THRIFT["list_field"](footer, 4):
        for leaf in THRIFT["list_field"](group, 1):
            leaf[3][1][4] = TType.I32, 4
    return pack_chunks(SCHEMA["pack"](source, footer), chunks)


def controls(native, location, name):
    def stored_crc(header, stored):
        return encode(header, stored[:-1] + bytes([stored[-1] ^ 1]), crc=False)

    def replace_stream(header, stored, edit):
        levels, stream, size, compressed = parts(header, stored)
        assert compressed
        kind, window, chunks = raw_blocks(stream)
        assert kind == "raw" and window == 16
        plain = b"".join(chunks)
        assert len(plain) == size and len(chunks) == 1
        return encode(header, levels + edit(stream, plain))

    edits = {
        "wrong_extent": lambda _, plain: raw_stream(plain[:-1]),
        "trailing": lambda stream, _: stream + b"\0",
        "truncated": lambda stream, _: stream[:-1],
        "padding": lambda stream, _: stream[:-1] + bytes([stream[-1] | 128]),
        "metadata": lambda _, plain: (
            b"\x0c" + (((len(plain) - 1) << 3) | (1 << 19)).to_bytes(3, "little") + plain + b"\x03"
        ),
    }
    labeled = {f"{name}_stored_crc": replace_page(native, location, stored_crc)}
    for suffix, edit in edits.items():
        labeled[f"{name}_{suffix}"] = replace_page(
            native, location, lambda header, stored: replace_stream(header, stored, edit))

    footer = MIXED["metadata"](native)
    leaf = THRIFT["column_metadata"](footer, *location[:2])
    leaf[6] = TType.I64, leaf[6][1] + 1
    labeled[f"{name}_footer_total"] = SCHEMA["pack"](native, footer)
    return labeled


def verify(scratch):
    cli = BROTLI["build_reference"](None, scratch)

    def decode_block(codec, stream, size):
        assert codec == 4
        kind, _, chunks = raw_blocks(stream)
        assert kind == "raw"
        raw = BROTLI["run"](cli, "--decompress", "--stdout", data=stream)
        assert raw == b"".join(chunks) and len(raw) == size
        return raw

    _, samples, _ = SCHEMA["fixtures"]()
    schema, rows = samples["nullable_lists"]
    small = [rows[:3], rows[3:]]
    packet = {"flag": 0, "items": [{"lo": -7, "nested": {"hi": -2**63}}] * 9}
    many = [{"packet": packet, "seq": 2**40}] * 16
    groups = [rows[:3], many + rows[3:]]

    genuine, labeled, seeds = {}, {}, {}
    for tag, version in (("v1", "1.0"), ("v2", "2.0")):
        genuine[tag] = pyarrow_brotli(schema, small, version, 0)
        genuine[f"{tag}_entropy"] = pyarrow_brotli(schema, small, version, 5)
        seeds[tag] = EDIT["write"](schema, groups, compression="NONE", page_version=version)
        captured = list(V2["capture"](seeds[tag], schema, groups[0] + groups[1]))
        assert sum(len(col.pages) for col, _ in captured) > 8
        label = f"authored_{tag}"
        labeled[label] = author(seeds[tag])
        labeled.update(controls(labeled[label], (1, 0, 0), tag))
    genuine["pageless"] = pyarrow_brotli(schema, [small[0], [], small[1]], "2.0", 0)
    for key, metadata, start, stop in V2["columns"](genuine["pageless"]):
        if key[0] == 1:
            assert [metadata[field][1] for field in (4, 5, 6, 7, 9)] == [4, 0, 0, 0, 0]
            assert start == stop == 0

    files = genuine | labeled
    for name, wire in files.items():
        (scratch / f"{name}.parquet").write_bytes(wire)
    positives = {"v1": small, "v2": small, "authored_v1": groups, "authored_v2": groups}
    manifest = {name: list(V2["capture"](files[name], schema, expected[0] + expected[1], codec=4,
                                        decode_block=decode_block))
                for name, expected in positives.items()}
    main = ["public def main (args : List String) : IO Unit := do",
            '  let [folder] := args | throw (IO.userError "expected fixture folder")']
    code, bridge = [LEAN, *main], [BRIDGE_LEAN, *main]
    streams_checked, bypassed = 0, 0
    for label, original in manifest.items():
        wire = files[label]
        frames = raw_chunks(wire)
        seed_frames = raw_chunks(seeds[label.removeprefix("authored_")]) if label.startswith("authored") else None
        assert all(col[4][1] == 4 for _, col, _, _ in V2["columns"](wire))
        for column, spans in original:
            decoded = []
            for _, header, _, stored in frames[column.group, column.index]:
                levels, block, size, compressed = parts(header, stored)
                if seed_frames is not None:
                    seed_page = seed_frames[column.group, column.index]
                    _, seed_header, _, seed_stored = seed_page[len(decoded)]
                    assert levels == parts(seed_header, seed_stored)[0]
                ready = decode_block(4, block, size) if compressed else block
                streams_checked += compressed
                bypassed += not compressed
                assert len(ready) == size
                if label == "v2":
                    assert not compressed
                decoded.append(f"(Bytes.ofList {list(ready)})")
            chosen = NO_WORK if label == "v2" else LIMITS
            code.append(CHUNK["check_term"](column, label, chosen))
            code.append(f'  spans (← load folder "{label}") {column.group} {column.index} {lst(spans)} {chosen}')
            code.append(f'  checkedBytes (← load folder "{label}") {column.group} {column.index} {lst(decoded)} {chosen}')
        fields, observations, counts = BRIDGE["observed"](wire)
        assert counts == [len(group) for group in positives[label]]
        bridge.append(f'  emitRaw folder "{label}" (← load folder "{label}") {fields} {observations}')

    bridge.append(BRIDGE["check"]("complete raw V2 at zero work", 'projectNoWork (← load folder "v2")',
                                  BRIDGE["observed"](genuine["v2"], positions=[])))
    bridge.append(BRIDGE["check"]("default reader refuses codec 4", 'direct (← load folder "v2")',
                                  BRIDGE["observed"](genuine["v2"], limit=0),
                                  '.readError (.group 0 (.binding (.column '
                                  '⟨0, 0, ["packet", "items", "list", "élément", "lo"]⟩ (.codec 4))))'))

    for tag in ("v1", "v2"):
        label = f"authored_{tag}"
        column = next(col for col, _ in manifest[label] if (col.group, col.index) == (1, 0))
        address = f"⟨1, 0, {json.dumps(column.path, ensure_ascii=False)}⟩"

        def page_error(fixture, cause, limits=LIMITS):
            at = raw_chunks(files[fixture])[1, 0][0][0]
            error = f".page {address} ⟨0, {at}, {{}}⟩ ({cause})"
            code.append(f'  refuse (← load folder "{fixture}") 1 0 {limits} ({error})')
            return error

        _, _, _, stored = raw_chunks(files[label])[1, 0][0]
        page_error(label, ".checksum .byteLimit",
                   f"{{ brotliRaw := some ⟨2 ^ 24 - 16, 16⟩, maxBodyBytes := {len(stored)-1} }}")
        page_error(label, ".brotli (.stream .windowLimit)", "{ brotliRaw := some ⟨65519, 16⟩ }")
        page_error(label, ".brotli (.stream .stepLimit)", "{ brotliRaw := some ⟨65520, 1⟩ }")
        exhausted = page_error(label, ".brotli (.stream .stepLimit)", NO_WORK) if tag == "v2" else None
        _, changed, _, corrupted = raw_chunks(files[tag + "_stored_crc"])[1, 0][0]
        page_error(tag + "_stored_crc", f".checksum (.mismatch {changed[4][1] & 0xffffffff} {zlib.crc32(corrupted)})",
                   NO_WORK)
        page_error(tag + "_wrong_extent", ".brotli (.page (.payload .outputSizeMismatch))")
        late = page_error(tag + "_trailing", ".brotli (.stream .trailingInput)")
        page_error(tag + "_truncated", ".brotli (.stream .truncated)")
        page_error(tag + "_padding", ".brotli (.stream .nonzeroPadding)")
        page_error(tag + "_metadata", ".brotli (.stream .unsupportedMetadata)")
        total = THRIFT["column_metadata"](MIXED["metadata"](files[label]), 1, 0)[6][1]
        code.append(f'  refuse (← load folder "{tag}_footer_total") 1 0 {LIMITS} '
                    f'(.chunk {address} ⟨{column.start}, {column.stop}⟩ (.uncompressedSize {total + 1} {total}))')
        code.append(f'  bindFailure (← load folder "{tag}") 0 0 '
                    '(.column ⟨0, 0, ["packet", "items", "list", "élément", "lo"]⟩ (.codec 4))')
        fixture = f"{tag}_trailing"
        terminal = f".readError (.group 1 (.chunk ({late})))"
        wide = BRIDGE["observed"](files[label], limit=1)
        empty = BRIDGE["observed"](files[label], positions=[], limit=1)
        bridge.extend([
            BRIDGE["check"](f"{tag} late stream error", f'directRaw (← load folder "{fixture}")', wide, terminal),
            BRIDGE["check"](f"{tag} projected late stream error", f'projectRaw (← load folder "{fixture}")',
                            empty, terminal),
            f'  sourceFailureRaw (← load folder "{fixture}") (.chunk ({late}))',
        ])
        if exhausted:
            ending = f".readError (.group 1 (.chunk ({exhausted})))"
            bridge.append(BRIDGE["check"]("raw prefix uses no Brotli work",
                          'projectNoWork (← load folder "authored_v2")', empty, ending))

        entropy = genuine[f"{tag}_entropy"]
        _, leaves = SCHEMA["describe"](entropy, schema, small[0] + small[1])
        for (group, col), pages in raw_chunks(entropy).items():
            [(byte, header, _, body)] = pages
            _, block, size, compressed = parts(header, body)
            if not compressed or raw_blocks(block)[0] != "compressed":
                continue
            assert len(BROTLI["run"](cli, "--decompress", "--stdout", data=block)) == size
            (_, path), *_ = leaves[col]
            name = json.dumps(path, ensure_ascii=False)
            code.append(f'  refuse (← load folder "{tag}_entropy") {group} {col} {LIMITS} '
                        f'(.page ⟨{group}, {col}, {name}⟩ ⟨0, {byte}, {{}}⟩ (.brotli (.stream .unsupportedCompressed)))')
            break
        else:
            raise AssertionError("genuine entropy-coded control is missing")

    code.append('  deny (.original (.snapshot (.invalidMetadata .pageInterval))) (openFile {} (← load folder "pageless"))')
    V2["run_lean"](scratch, "Chunk.lean", code)
    V2["run_lean"](scratch, "Bridge.lean", bridge)
    ipc = {}
    for name, expected in positives.items():
        raw = (scratch / f"{name}.arrow").read_bytes()
        parquet = pq.ParquetFile(pa.BufferReader(files[name]), page_checksum_verification=True)
        reader = pa.ipc.open_stream(raw)
        assert reader.schema == parquet.schema_arrow == schema
        assert [batch.to_pylist() for batch in reader] == expected
        _, cursor = STREAM["metadata"](raw)
        for group in expected:
            frame = STREAM["read_record"](raw, cursor)
            assert frame.rows == len(group)
            cursor = frame.end
        assert raw[cursor:] == STREAM["EOS"]
        ipc[name] = raw
    print(f"Verified {streams_checked} raw Brotli streams and {bypassed} raw V2 suffixes, "
          "four native IPC streams and 26 typed refusals")
    return {"genuine_parquet": fingerprints(genuine), "uncompressed_seeds": fingerprints(seeds),
            "labeled_edits": fingerprints(labeled), "lean_ipc": fingerprints(ipc)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    assert pins["libbrotli"] == BROTLI["PIN"]
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for kind, values in captured.items():
        assert values == pins[kind], f"{kind} fixture pins changed"


if __name__ == "__main__":
    main()
