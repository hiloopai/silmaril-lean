"""Check recursive dictionary-first raw Brotli against pinned libbrotli and PyArrow."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import tempfile
import zlib

import pyarrow as pa
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
PLAIN = runpy.run_path(str(HERE.parent / "parquet-recursive-brotli-raw-oracle/check.py"))
SHARED = runpy.run_path(str(HERE.parent / "parquet-recursive-dictionary-snappy-oracle/check.py"))
V1, V2, BRIDGE, STREAM, CHUNK, THRIFT, MIXED, FRAMES, fingerprints, lst = (
    SHARED[key] for key in ("V1", "V2", "BRIDGE", "STREAM", "CHUNK", "THRIFT", "MIXED",
                           "FRAMES", "fingerprints", "lst")
)
write, encode, replace_page, repack, raw_chunks, header_body = (
    SHARED[key] for key in ("write", "encode", "replace_page", "repack", "raw_chunks", "header_body")
)
BROTLI, raw_blocks, raw_stream = (PLAIN[key] for key in ("BROTLI", "raw_blocks", "raw_stream"))
LIMITS, NO_WORK = PLAIN["LIMITS"], PLAIN["NO_WORK"]

LEAN = SHARED["LEAN"] + """\

private def checkRawBypass (file : Bytes) (group column : Nat) (limits noWork : Limits) : IO Unit := do
  let source ← take (openFile {} file)
  let binding ← take (bindChunk source.schema group column limits)
  let seen ← take (Parquet.RecursiveSchema.Repeated.Chunk.read limits binding)
  let some dictionary := seen.dictionary | throw (IO.userError "expected checked Brotli dictionary")
  for page in seen.pages do
    let .dataV2 info := page.frame.value.kind | continue
    let start := page.start.state
    let remaining := binding.chunk.metadata.numValues.toNat - start.slot
    let rows := binding.rowGroup.numRows.toNat
    let result :=
      if info.encoding = 8 then
        decodeV2DictionaryPage noWork binding.leaf dictionary.entries file page.frame start remaining rows
          dictionary.codec
      else decodeV2Page noWork binding.codec binding.leaf file page.frame start remaining rows
    if info.isCompressed then
      deny (.brotli (.stream .stepLimit)) result
    else
      let decoded ← take result
      unless decoded.levels = page.decoded.levels ∧ decoded.words = page.decoded.words ∧
          decoded.after = page.decoded.after do
        throw (IO.userError "raw Brotli column suffix differs with zero work")

set_option maxRecDepth 8192
"""


def parts(header, body):
    if header[1][1] == 2:
        return b"", body, header[2][1], True
    return PLAIN["parts"](header, body)


def author_v2(seed):
    """Wrap selected original suffixes and all dictionaries in authored raw streams."""
    chunks = raw_chunks(seed)
    for key, frames in chunks.items():
        for ordinal, frame in enumerate(frames):
            header, body = header_body(frame)
            levels, suffix, size, _ = parts(header, body)
            assert len(suffix) == size
            framed = ordinal == 0 or ordinal % 2 == 1
            if ordinal > 0:
                header[8][1][7] = TType.BOOL, framed
            frames[ordinal] = encode(header, levels + (raw_stream(suffix) if framed else suffix),
                                     header[2][1])
    footer = MIXED["metadata"](seed)
    for key in chunks:
        THRIFT["column_metadata"](footer, *key)[4] = TType.I32, 4
    return repack(seed, chunks, footer)


def verify(scratch):
    cli = BROTLI["build_reference"](None, scratch)

    def native_decode(stream):
        return BROTLI["run"](cli, "--decompress", "--stdout", data=stream)

    def decode_block(codec, stream, size):
        assert codec == 4
        kind, _, raw = raw_blocks(stream)
        assert kind == "raw"
        decoded = native_decode(stream)
        assert len(decoded) == size and decoded == b"".join(raw)
        return decoded

    schema, rows = V1["nested_samples"]()
    fall_rows = [rows[0], SHARED["FALLBACK"]["rows_for_fallback"]()]
    fallback = {"dictionary_pagesize_limit": 48}
    genuine = {}
    for tag, ver in (("v1", "1.0"), ("v2", "2.0")):
        opts = {"compression": "BROTLI", "data_page_version": ver}
        genuine[tag] = write(schema, rows, compression_level=0, **opts)
        genuine[f"{tag}_fallback"] = write(schema, fall_rows, compression_level=0, **opts, **fallback)
        genuine[f"{tag}_entropy"] = write(schema, rows, compression_level=5, **opts)

    seed = write(schema, fall_rows, compression="NONE", data_page_version="2.0", **fallback)
    seed_manifest = list(V1["inspect"](seed, schema, fall_rows))
    assert all(dictionary is not None for _, dictionary, _, _ in seed_manifest)
    continuation, cont_schema, cont_rows = SHARED["author_continuation"](scratch, compress=raw_stream, codec=4)
    authored = {"v2_selected_raw_frames": author_v2(seed), "v1_midrow_fallback": continuation}
    v1, v2 = genuine["v1_fallback"], authored["v2_selected_raw_frames"]
    key, page = (1, 0), 1

    def corrupt_crc(header, body):
        return encode(header, body[:-1] + bytes([body[-1] ^ 1]), header[2][1], crc=False)

    def extra_byte(header, body):
        assert parts(header, body)[3]
        return encode(header, body + b"\0", header[2][1])

    def wrong_extent(header, body):
        return encode(header, body, header[2][1] + 64)

    for label, wire in (("v1", v1), ("v2", v2)):
        authored[f"{label}_data_crc"] = replace_page(wire, key, page, corrupt_crc)
        authored[f"{label}_trailing"] = replace_page(wire, key, page, extra_byte)
        authored[f"{label}_extent"] = replace_page(wire, key, page, wrong_extent)
    authored["dictionary_crc"] = replace_page(v2, key, 0, corrupt_crc)
    authored["dictionary_trailing"] = replace_page(v2, key, 0, extra_byte)
    authored["dictionary_extent"] = replace_page(v2, key, 0, wrong_extent)
    authored["late_v2_indices"] = replace_page(v2, key, page,
        lambda h, b: SHARED["append_index_byte"](h, b, decode=lambda stream, size: decode_block(4, stream, size),
                                                compress=raw_stream))
    footer = MIXED["metadata"](v2)
    meta = THRIFT["column_metadata"](footer, *key)
    dict_frame = raw_chunks(v2)[key][0]
    dict_header, dict_body = header_body(dict_frame)
    raw_dictionary = len(dict_frame) - len(dict_body) + dict_header[2][1]
    meta[6] = TType.I64, meta[6][1] - raw_dictionary
    authored["dictionary_missing_from_total"] = V1["SCHEMA"]["pack"](v2, footer)
    footer = MIXED["metadata"](v2)
    meta = THRIFT["column_metadata"](footer, *key)
    meta[7] = TType.I64, meta[7][1] - 1
    authored["short_stored_total"] = V1["SCHEMA"]["pack"](v2, footer)

    files = genuine | authored
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)
    positives = {"v1": (schema, rows), "v2": (schema, rows),
                 "v1_fallback": (schema, fall_rows), "v2_fallback": (schema, fall_rows),
                 "v2_selected_raw_frames": (schema, fall_rows), "v1_midrow_fallback": (cont_schema, cont_rows)}
    bridge = [PLAIN["BRIDGE_LEAN"], "set_option maxRecDepth 8192", *V1["ENTRY"]]
    captured, checks, flags = {}, {}, set()
    stored_streams, bypassed = 0, 0
    seed_frames = raw_chunks(seed)
    for label, (declarations, expected) in positives.items():
        code = checks[label] = []
        wire = files[label]
        chunks = raw_chunks(wire)
        captured[label] = {}
        for column, dictionary, traces, spans in V1["inspect"](wire, declarations, expected, decode_block=decode_block):
            assert dictionary is not None
            position = column.group, column.index
            captured[label][position] = column
            code.append(CHUNK["check_term"](column, label, LIMITS))
            code.append(V1["dictionary_term"](column, dictionary, traces, label) + f" {LIMITS}")
            code.append(f'  spans (← load folder "{label}") {column.group} {column.index} {lst(spans)} {LIMITS}')
            raw, raw_total, tags = [], 0, []
            for ordinal, frame in enumerate(chunks[position]):
                header, body = header_body(frame)
                levels, payload, size, framed = parts(header, body)
                result = decode_block(4, payload, size) if framed else payload
                assert size == len(result)
                if label == "v2_selected_raw_frames":
                    old_levels, old_payload, old_size, _ = parts(*header_body(seed_frames[position][ordinal]))
                    assert (levels, result, size) == (old_levels, old_payload, old_size)
                stored_streams += framed
                bypassed += not framed
                raw_total += len(frame) - len(body) + header[2][1]
                raw.append(f"(Bytes.ofList {list(result)})")
                if ordinal:
                    tag = SHARED["FALLBACK"]["original_encoding"](header)
                    tags.append(tag)
                    if header[1][1] == 3:
                        flags.add((label, tag, framed))
            if label.endswith("_fallback") and column.group == 1:
                assert set(tags) == {0, 8} and tags == sorted(tags, reverse=True)
            code.append(f'  rawPayloads (← load folder "{label}") {column.group} {column.index} '
                        f'.brotliRaw {raw[0]} {lst(raw[1:])} {column.stop - column.start} {raw_total} {LIMITS}')
            if any(span != "none" for span in spans):
                code.append(f'  checkRawBypass (← load folder "{label}") {column.group} {column.index} '
                            f'{LIMITS} {NO_WORK}')
        fields, batches, counts = BRIDGE["observed"](wire)
        assert counts == [len(group) for group in expected]
        bridge.append(f'  emitRaw folder "{label}" (← load folder "{label}") {fields} {batches}')
    assert {("v2_fallback", tag, False) for tag in (0, 8)} <= flags
    assert {("v2_selected_raw_frames", tag, framed) for tag in (0, 8) for framed in (True, False)} <= flags
    midrow = captured["v1_midrow_fallback"][0, 0].pages[-1]
    assert midrow.before[2] and midrow.events[0][0] == 1 and midrow.before[1] == midrow.after[1]

    code = checks["refusals"] = []

    def at(label, position, ordinal):
        lo, hi = next((lo, hi) for key, _, lo, hi in V2["columns"](files[label]) if key == position)
        return list(FRAMES(files[label], lo, hi))[ordinal]

    def address(column):
        return f"⟨{column.group}, {column.index}, {CHUNK['path_term'](column.path)}⟩"

    def refuse(label, original, position, ordinal, cause, limits=LIMITS, *, use_original_extent=False):
        column = captured[original][position]
        frame_source = original if use_original_extent else label
        byte = at(frame_source, position, ordinal)[0]
        before = CHUNK["state_term"](column.pages[ordinal - 1].before if ordinal else (0, 0, False))
        error = f".page {address(column)} ⟨{ordinal}, {byte}, {before}⟩ ({cause})"
        code.append(f'  refuse (← load folder "{label}") {column.group} {column.index} {limits} ({error})')
        return error

    def bridge_failure(label, original, error, completed=1):
        terminal = f".readError (.group {completed} (.chunk ({error})))"
        for call, positions in (("directRaw", None), ("projectRaw", [])):
            expected = BRIDGE["observed"](files[original], positions=positions, limit=completed)
            bridge.append(BRIDGE["check"](label, f'{call} (← load folder "{label}")', expected, terminal))
        bridge.append(f'  sourceFailureRaw (← load folder "{label}") (.chunk ({error}))')

    v2_label = "v2_selected_raw_frames"
    frame_limit = "(.brotli (.stream .stepLimit))"
    extent = ".brotli (.page (.payload .outputSizeMismatch))"
    for tag, original in (("v1", "v1_fallback"), ("v2", v2_label), ("dictionary", v2_label)):
        ordinal = 0 if tag == "dictionary" else page
        label = f"{tag}_crc" if ordinal == 0 else f"{tag}_data_crc"
        _, header, _, corrupted = at(label, key, ordinal)
        cause = f".checksum (.mismatch {header[4][1] & 0xffffffff} {zlib.crc32(corrupted)})"
        error = refuse(label, original, key, ordinal, cause, NO_WORK if ordinal == 0 else LIMITS)
        if ordinal == 0:
            bridge_failure(label, original, error)
        refuse(f"{tag}_extent", original, key, ordinal, extent)
        label = f"{tag}_trailing"
        error = refuse(label, original, key, ordinal, ".brotli (.stream .trailingInput)")
        if ordinal > 0:
            bridge_failure(label, original, error)
    error = refuse("late_v2_indices", v2_label, key, page, ".dictionaryIndices (.hybrid .trailingBytes)")
    bridge_failure("late_v2_indices", v2_label, error)

    for tag, position, ordinal in (("v1", (1, 0), 1), ("v2", (0, 2), 0)):
        label = f"{tag}_entropy"
        _, header, _, body = at(label, position, ordinal)
        levels, payload, size, framed = parts(header, body)
        _, same_header, _, same_body = at(tag, position, ordinal)
        same_levels, same_payload, same_size, same_framed = parts(same_header, same_body)
        assert framed and raw_blocks(payload)[0] == "compressed"
        assert levels == same_levels and size == same_size
        expected = decode_block(4, same_payload, same_size) if same_framed else same_payload
        assert native_decode(payload) == expected
        refuse(label, tag, position, ordinal, ".brotli (.stream .unsupportedCompressed)")

    cap = f"({LIMITS} : Limits) with"
    refuse(v2_label, v2_label, key, 0, frame_limit, NO_WORK)
    refuse(v2_label, v2_label, key, 0, ".brotli (.stream .windowLimit)", "{ brotliRaw := some ⟨65519, 16⟩ }")
    refuse(v2_label, v2_label, key, 0, f".dictionaryByteLimit {len(dict_body)}",
           f"{{ {cap} maxDictionaryBytes := {len(dict_body) - 1} }}")
    claimed_raw = dict_header[2][1] + 64
    assert claimed_raw > len(dict_body)
    refuse("dictionary_extent", v2_label, key, 0, f".dictionaryRawByteLimit {claimed_raw}",
           f"{{ {cap} maxDictionaryBytes := {len(dict_body)} }}")
    entries = dict_header[7][1][1][1]
    refuse(v2_label, v2_label, key, 0, f".dictionaryEntryLimit {entries}", f"{{ {cap} maxDictionaryEntries := 0 }}")
    refuse(v2_label, v2_label, key, 0, ".checksum .byteLimit",
           f"{{ {cap} maxBodyBytes := {len(dict_body) - 1} }}")
    _, header, _, body = at("v2_extent", key, page)
    body_cap = max(len(body), len(dict_body))
    assert body_cap < header[2][1]
    refuse("v2_extent", v2_label, key, page, ".payload .outputLimit", f"{{ {cap} maxBodyBytes := {body_cap} }}")
    refuse(v2_label, v2_label, key, page, ".framing .pageLimit", f"{{ {cap} framing.maxPages := 1 }}")
    last_ordinal = len(raw_chunks(v2)[key]) - 1
    refuse("short_stored_total", v2_label, key, last_ordinal,
           ".framing .payloadBounds", use_original_extent=True)
    column = captured[v2_label][key]
    total = THRIFT["column_metadata"](MIXED["metadata"](v2), *key)[6][1]
    code.append(f'  refuse (← load folder "dictionary_missing_from_total") 1 0 {LIMITS} '
                f'(.chunk {address(column)} ⟨{column.start}, {column.stop}⟩ '
                f'(.uncompressedSize {total - raw_dictionary} {total}))')

    column = captured["v2_fallback"][0, 0]
    disabled = f".column {address(column)} (.codec 4)"
    code.append(f'  bindFailure (← load folder "v2_fallback") 0 0 ({disabled})')
    bridge.append(BRIDGE["check"]("default refuses dictionary codec 4 with raw V2 data",
                                  'project (← load folder "v2_fallback") []',
                                  BRIDGE["observed"](files["v2_fallback"], positions=[], limit=0),
                                  f".readError (.group 0 (.binding ({disabled})))"))
    driver = [LEAN]
    for label, terms in checks.items():
        driver.extend([f"private def check_{label} (folder : String) : IO Unit := do", *terms, ""])
    driver.extend([*V1["ENTRY"], *(f"  check_{label} folder" for label in checks)])
    V2["run_lean"](scratch, "Chunk.lean", driver)
    V2["run_lean"](scratch, "Bridge.lean", bridge)

    ipc = {}
    for label, (declarations, expected) in positives.items():
        wire = (scratch / f"{label}.arrow").read_bytes()
        reader = pa.ipc.open_stream(wire)
        assert reader.schema == declarations
        assert [batch.to_pylist() for batch in reader] == expected
        _, cursor = STREAM["metadata"](wire)
        for group in expected:
            frame = STREAM["read_record"](wire, cursor)
            assert frame.rows == len(group)
            cursor = frame.end
        assert wire[cursor:] == STREAM["EOS"]
        ipc[label] = wire
    print(f"Checked {stored_streams} raw Brotli streams, {bypassed} false-flag V2 suffixes, "
          f"{len(ipc)} native IPC streams through exact EOS and {len(code)} typed chunk controls")
    return {"genuine_parquet": fingerprints(genuine), "seeds": fingerprints({"v2_fallback": seed}),
            "labeled_edits": fingerprints(authored), "lean_ipc": fingerprints(ipc)}


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
