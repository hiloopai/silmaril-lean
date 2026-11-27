"""Inspect exact raw Snappy blocks and recursive signed dictionary pages."""

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
FALLBACK = runpy.run_path(str(HERE.parent / "parquet-recursive-dictionary-fallback-oracle/check.py"))
V1, V2, BRIDGE, STREAM, CHUNK, THRIFT, MIXED, FRAMES, fingerprints, lst, I32 = (
    FALLBACK[key] for key in ("V1", "V2", "BRIDGE", "STREAM", "CHUNK", "THRIFT", "MIXED",
                              "FRAMES", "fingerprints", "lst", "I32")
)
raw_chunks, header_body = V1["raw_chunks"], V1["header_body"]
SNAPPY = pa.Codec("snappy")
I64 = TType.I64

LEAN = V1["LEAN"] + """\

private def rawPayloads (file : Bytes) (group column : Nat) (dict : Bytes)
    (data : List Bytes) (storedBytes rawBytes : Nat) : IO Unit := do
  let source ← take (openFile {} file)
  let binding ← take (bindChunk source.schema group column)
  let seen ← take (Parquet.RecursiveSchema.Repeated.Chunk.read {} binding)
  let some original := seen.dictionary | throw (IO.userError "expected leading dictionary")
  unless original.codec = .snappy ∧ binding.codec = .snappy ∧
      (← take (readV1Body {} binding.codec file original.frame)) = dict do
    throw (IO.userError "decoded original dictionary differs")
  let mut bodies := []
  for page in seen.pages do
    let body ← match page.frame.value.kind with
      | .dataV1 _ => take (readV1Body {} binding.codec file page.frame)
      | .dataV2 info => do
        let sections ← take (readV2Sections {} binding.leaf file page.frame info)
        let stored := bytesAt file sections.spans.values
        if info.encoding = 0 then
          take (readV2Suffix {} binding.codec binding.leaf page.frame info stored)
        else take (readV2SuffixWith {} binding.codec page.frame info stored none)
      | _ => throw (IO.userError "expected a data page")
    bodies := body :: bodies
  unless bodies.reverse = data ∧ storedChunkBytes seen.frames = storedBytes ∧
      rawChunkBytes seen.frames = rawBytes do throw (IO.userError "payloads or header-inclusive totals differ")
"""


def snappy(stored, extent):
    """Check the raw length varint, all literal/copy commands, and exact consumption."""
    size, at = 0, 0
    for shift in range(0, 35, 7):
        byte = stored[at]
        at += 1
        size |= (byte & 127) << shift
        if byte < 128:
            break
    else:
        raise AssertionError("invalid Snappy length")
    assert size == extent
    output = bytearray()

    def take(width):
        nonlocal at
        assert at + width <= len(stored)
        word = stored[at:at + width]
        at += width
        return word

    while at < len(stored):
        [tag] = take(1)
        kind = tag & 3
        code = tag >> 2
        if kind == 0:
            length = code + 1 if code < 60 else 1 + int.from_bytes(take(code - 59), "little")
            assert len(output) + length <= extent
            output.extend(take(length))
        else:
            if kind == 1:
                length = 4 + (code & 7)
                distance = ((tag & 224) << 3) | take(1)[0]
            else:
                length = code + 1
                distance = int.from_bytes(take(2 if kind == 2 else 4), "little")
            assert 1 <= distance <= len(output) and len(output) + length <= extent
            for _ in range(length):
                output.append(output[-distance])
    assert at == len(stored) and len(output) == extent
    assert output == SNAPPY.decompress(stored, extent).to_pybytes()
    return bytes(output)


def write(schema, groups, **options):
    """Leave the codec and dictionary selection at the PyArrow defaults."""
    sink = pa.BufferOutputStream()
    settings = dict(use_compliant_nested_type=False, store_schema=False, write_page_checksum=True,
                    write_page_index=False, data_page_size=64, write_batch_size=2, max_rows_per_page=3)
    with pq.ParquetWriter(sink, schema, **(settings | options)) as writer:
        for rows in groups:
            writer.write_table(pa.Table.from_pylist(rows, schema=schema))
    return sink.getvalue().to_pybytes()


def encode(header, body, raw_size, *, crc=True):
    header[2], header[3] = (I32, raw_size), (I32, len(body))
    if crc:
        digest = zlib.crc32(body)
        header[4] = I32, digest if digest < 2**31 else digest - 2**32
    return THRIFT["encode"](header) + body


def repack(wire, chunks, footer=None):
    """Splice labeled pages and independently recompute the two footer lengths."""
    packed = V1["repack"](wire, chunks, footer)
    footer = MIXED["metadata"](packed)
    for group, row_group in enumerate(THRIFT["list_field"](footer, 4)):
        columns = THRIFT["list_field"](row_group, 1)
        total = 0
        for column, carrier in enumerate(columns):
            chunk_raw = 0
            for frame in chunks[group, column]:
                [(_, header, payload, _)] = FRAMES(frame, 0, len(frame))
                chunk_raw += payload + header[2][1]
            carrier[3][1][6] = I64, chunk_raw
            total += chunk_raw
        row_group[2] = I64, total
    return V1["SCHEMA"]["pack"](packed, footer)


def replace_page(wire, key, ordinal, edit):
    chunks = raw_chunks(wire)
    chunks[key][ordinal] = edit(*header_body(chunks[key][ordinal]))
    return repack(wire, chunks)


def frame_bytes(header, body):
    if header[1][1] != 3:
        return snappy(body, header[2][1])
    info = header[8][1]
    levels = info[5][1] + info[6][1]
    suffix = body[levels:]
    expected = header[2][1] - levels
    if info.get(7, (None, True))[1]:
        return snappy(suffix, expected)
    assert len(suffix) == expected
    return suffix


def author_continuation(scratch):
    fixtures, schema, groups = FALLBACK["split_row"](scratch)
    wire = fixtures["continued_into_plain"]
    chunks = raw_chunks(wire)
    for key, frames in chunks.items():
        chunks[key] = [encode(header, SNAPPY.compress(body).to_pybytes(), len(body))
                       for header, body in map(header_body, frames)]
    footer = MIXED["metadata"](wire)
    THRIFT["column_metadata"](footer, 0, 0)[4] = I32, 1
    return repack(wire, chunks, footer), schema, groups


def raw_bypass(header, body):
    raw = frame_bytes(header, body)
    assert header[1][1] == 3 and header[8][1][7][1]
    info = header[8][1]
    levels = info[5][1] + info[6][1]
    info[7] = TType.BOOL, False
    return encode(header, body[:levels] + raw, levels + len(raw))


def append_index_byte(header, body):
    raw = frame_bytes(header, body) + b"\0"
    if header[1][1] == 0:
        return encode(header, SNAPPY.compress(raw).to_pybytes(), len(raw))
    info = header[8][1]
    levels = info[5][1] + info[6][1]
    assert info[7][1]
    return encode(header, body[:levels] + SNAPPY.compress(raw).to_pybytes(), levels + len(raw))


def verify(scratch):
    schema, groups = V1["nested_samples"]()
    alternating = [{"packet": {"flag": 0, "items": [{"lo": i % 2, "nested": {"hi": (-1)**i}}
                                                     for i in range(160)]}, "seq": 1}]
    indexed_groups = [groups[0], alternating]
    fall_groups = [groups[0], FALLBACK["rows_for_fallback"]()]
    genuine = {
        "default_v1": write(schema, groups),
        "default_v2": write(schema, groups, data_page_version="2.0"),
        "compressed_indices_v2": write(schema, indexed_groups, data_page_version="2.0", data_page_size=32768),
        "fallback_v1": write(schema, fall_groups, dictionary_pagesize_limit=48),
        "fallback_v2": write(schema, fall_groups, data_page_version="2.0", dictionary_pagesize_limit=48),
    }
    v1, v2 = genuine["default_v1"], genuine["compressed_indices_v2"]
    key, dict_key = (1, 0), (1, 1)
    target = 1
    continuation, cont_schema, cont_groups = author_continuation(scratch)
    edited = {
        "v2_raw_bypass": replace_page(v2, key, target, raw_bypass),
        "v1_midrow_fallback": continuation,
        "late_v1_indices": replace_page(v1, key, target, append_index_byte),
        "late_v2_indices": replace_page(v2, key, target, append_index_byte),
    }
    carrier = genuine["fallback_v1"]

    def corrupt_crc(header, body):
        return encode(header, bytes([body[0] ^ 1]) + body[1:], header[2][1], crc=False)

    def malformed(header, _):
        return encode(header, b"\x01", header[2][1])

    def raw_size(header, body):
        return encode(header, body, header[2][1] + 1)

    for name, change in (("dict_crc", corrupt_crc), ("dict_malformed", malformed), ("dict_extent", raw_size)):
        edited[name] = replace_page(carrier, dict_key, 0, change)

    def v2_malformed(header, body):
        info = header[8][1]
        levels = info[5][1] + info[6][1]
        return encode(header, body[:levels] + b"\x01", header[2][1])

    def v2_bad_crc(header, body):
        return encode(header, body[:-1] + bytes([body[-1] ^ 1]), header[2][1], crc=False)

    def v2_trailing(header, body):
        return encode(header, body + b"\0", header[2][1])

    edited["v1_body_malformed"] = replace_page(v1, key, target, malformed)
    for name, change in (("v2_malformed", v2_malformed), ("v2_extent", raw_size),
                         ("v2_snappy_trailing", v2_trailing), ("v2_stored_crc", v2_bad_crc)):
        edited[name] = replace_page(v2, key, target, change)

    bypass = edited["v2_raw_bypass"]
    edited["v2_raw_extent"] = replace_page(bypass, key, target, raw_size)
    dictionary_frame = raw_chunks(v2)[key][0]
    dictionary_header, dictionary_payload = header_body(dictionary_frame)
    dictionary_raw_total = len(dictionary_frame) - len(dictionary_payload) + dictionary_header[2][1]
    for field, change, label in ((6, -dictionary_raw_total, "wrong_raw_total"), (7, -1, "short_stored_total")):
        footer = MIXED["metadata"](v2)
        leaf = THRIFT["column_metadata"](footer, *key)
        leaf[field] = I64, leaf[field][1] + change
        edited[label] = V1["SCHEMA"]["pack"](v2, footer)

    files = genuine | edited
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)
    positives = {
        "default_v1": (schema, groups),
        "default_v2": (schema, groups),
        "compressed_indices_v2": (schema, indexed_groups),
        "fallback_v1": (schema, fall_groups),
        "fallback_v2": (schema, fall_groups),
        "v2_raw_bypass": (schema, indexed_groups),
        "v1_midrow_fallback": (cont_schema, cont_groups),
    }

    code, bridge = [LEAN, *V1["ENTRY"]], [BRIDGE["LEAN"], *V1["ENTRY"]]
    capture, frame_count, v2_index_compressed, v2_index_raw, v2_plain_compressed = {}, 0, 0, 0, 0
    for label, (declarations, rows) in positives.items():
        wire = files[label]
        capture[label] = {}
        chunks = raw_chunks(wire)
        for column, dictionary, traces, spans in V1["inspect"](wire, declarations, rows, decode_snappy=snappy):
            assert dictionary is not None
            capture[label][column.group, column.index] = column
            code.append(CHUNK["check_term"](column, label))
            code.append(V1["dictionary_term"](column, dictionary, traces, label))
            code.append(f'  spans (← load folder "{label}") {column.group} {column.index} {lst(spans)}')
            frames = [header_body(frame) for frame in chunks[column.group, column.index]]
            frame_count += len(frames)
            raw = [frame_bytes(header, body) for header, body in frames]
            raw_total = sum(len(frame) - len(body) + header[2][1]
                            for frame, (header, body) in zip(chunks[column.group, column.index], frames, strict=True))
            for header, _ in frames[1:]:
                if header[1][1] == 3:
                    info = header[8][1]
                    flag = info[7][1]
                    v2_index_compressed += int(flag and info[4][1] == 8)
                    v2_index_raw += int(not flag and info[4][1] == 8)
                    v2_plain_compressed += int(flag and info[4][1] == 0)
            terms = [f"(Bytes.ofList {list(body)})" for body in raw]
            code.append(f'  rawPayloads (← load folder "{label}") {column.group} {column.index} '
                        f'{terms[0]} {lst(terms[1:])} {column.stop - column.start} {raw_total}')
        fields, batches, counts = BRIDGE["observed"](wire)
        assert counts == [len(group) for group in rows]
        bridge.append(f'  emit folder "{label}" (← load folder "{label}") {fields} {batches}')
    assert v2_index_compressed > 0 and v2_index_raw > 0 and v2_plain_compressed > 0
    last = capture["v1_midrow_fallback"][0, 0].pages[-1]
    assert last.before[2] and last.events[0][0] == 1 and last.before[1] == last.after[1]

    def at(label, position, ordinal):
        lo, hi = next((lo, hi) for key, _, lo, hi in V2["columns"](files[label]) if key == position)
        return list(FRAMES(files[label], lo, hi))[ordinal]

    def refuse(label, position, ordinal, cause, limits="{}", *, original=None):
        group, column = position
        reference = capture[original or label][position]
        address = f"⟨{group}, {column}, {CHUNK['path_term'](reference.path)}⟩"
        byte = at(original, position, ordinal)[0] if label == "short_stored_total" else at(label, position, ordinal)[0]
        before = CHUNK["state_term"](reference.pages[ordinal - 1].before if ordinal else (0, 0, False))
        error = f".page {address} ⟨{ordinal}, {byte}, {before}⟩ ({cause})"
        code.append(f'  refuse (← load folder "{label}") {group} {column} {limits} ({error})')
        return error

    for control, original in (("late_v1_indices", "default_v1"), ("late_v2_indices", "compressed_indices_v2")):
        error = refuse(control, key, target, ".dictionaryIndices (.hybrid .trailingBytes)", original=original)
        terminal = f".readError (.group 1 (.chunk ({error})))"
        for positions, call in [(None, f'direct (← load folder "{control}")'),
                                ([], f'project (← load folder "{control}") []')]:
            expected = BRIDGE["observed"](files[original], positions=positions, limit=1)
            bridge.append(BRIDGE["check"](control, call, expected, terminal))
        bridge.append(f'  sourceFailure (← load folder "{control}") (.chunk ({error}))')

    _, header, _, body = at("dict_crc", dict_key, 0)
    refuse("dict_crc", dict_key, 0, f".checksum (.mismatch {header[4][1] & 0xffffffff} {zlib.crc32(body)})",
           original="fallback_v1")
    refuse("dict_malformed", dict_key, 0, ".payload (.malformed .snappy)", original="fallback_v1")
    refuse("dict_extent", dict_key, 0, ".payload .outputSizeMismatch", original="fallback_v1")
    _, dict_header, _, dict_bytes = at("fallback_v1", dict_key, 0)
    raw, stored = dict_header[2][1], len(dict_bytes)
    assert stored < raw
    refuse("fallback_v1", dict_key, 0, f".dictionaryByteLimit {stored}", f"{{ maxDictionaryBytes := {stored - 1} }}")
    refuse("fallback_v1", dict_key, 0, f".dictionaryRawByteLimit {raw}", f"{{ maxDictionaryBytes := {stored} }}")
    refuse("fallback_v1", dict_key, 0, ".payload .outputLimit", f"{{ maxBodyBytes := {stored} }}")

    refuse("v1_body_malformed", key, target, ".payload (.malformed .snappy)", original="default_v1")
    original = "compressed_indices_v2"
    _, v2_header, _, v2_body = at("v2_stored_crc", key, target)
    refuse("v2_stored_crc", key, target,
           f".checksum (.mismatch {v2_header[4][1] & 0xffffffff} {zlib.crc32(v2_body)})", original=original)
    refuse("v2_malformed", key, target, ".payload (.malformed .snappy)", original=original)
    refuse("v2_extent", key, target, ".payload .outputSizeMismatch", original=original)
    refuse("v2_snappy_trailing", key, target, ".payload (.trailingInput .snappy)", original=original)
    refuse("v2_raw_extent", key, target, ".framing (.header .invalidV2Lengths)", original=original)
    refuse("short_stored_total", key, target, ".framing .payloadBounds", original=original)
    _, h, _, encoded = at(original, key, target)
    assert h[8][1][7][1]
    refuse(original, key, target, ".payload .outputLimit", f"{{ maxBodyBytes := {len(encoded)} }}")
    refuse(original, key, target, ".framing .pageLimit", "{ framing.maxPages := 1 }")
    column = capture[original][key]
    raw_total = THRIFT["column_metadata"](MIXED["metadata"](v2), *key)[6][1]
    address = f"⟨1, 0, {CHUNK['path_term'](column.path)}⟩"
    code.append(f'  refuse (← load folder "wrong_raw_total") 1 0 {{}} '
                f'(.chunk {address} ⟨{column.start}, {column.stop}⟩ (.uncompressedSize {raw_total - dictionary_raw_total} {raw_total}))')

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
    print(f"Checked {frame_count} physical frames, {v2_index_compressed} compressed and {v2_index_raw} raw V2 index suffixes, "
          f"and {v2_plain_compressed} compressed PLAIN V2 suffix; seven IPC streams and 18 typed controls")
    return {"genuine_parquet": fingerprints(genuine), "labeled_edits": fingerprints(edited),
            "lean_ipc": fingerprints(ipc)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for name, values in captured.items():
        assert values == pins[name], f"{name} fixture pins changed"


if __name__ == "__main__":
    main()
