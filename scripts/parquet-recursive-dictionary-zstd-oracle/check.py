"""Check recursive Parquet value dictionaries and data pages against pinned libzstd."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile
import zlib

import pyarrow as pa
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
ZSTD = runpy.run_path(str(HERE.parent / "parquet-recursive-zstd-oracle/check.py"))
REFERENCE = ZSTD["ZSTD"]
SHARED = runpy.run_path(str(HERE.parent / "parquet-recursive-dictionary-snappy-oracle/check.py"))
V1, V2, BRIDGE, STREAM, CHUNK, THRIFT, MIXED, FRAMES, fingerprints, lst, I64 = (
    SHARED[key] for key in ("V1", "V2", "BRIDGE", "STREAM", "CHUNK", "THRIFT", "MIXED",
                           "FRAMES", "fingerprints", "lst", "I64")
)
write, encode, replace_page, raw_chunks, header_body = (
    SHARED[key] for key in ("write", "encode", "replace_page", "raw_chunks", "header_body")
)

LEAN = SHARED["LEAN"] + """\

private def checkRawBypass (file : Bytes) (group column : Nat) : IO Unit := do
  let source ← take (openFile {} file)
  let binding ← take (bindChunk source.schema group column)
  let seen ← take (Parquet.RecursiveSchema.Repeated.Chunk.read {} binding)
  let some original := seen.dictionary | throw (IO.userError "expected checked Zstd column dictionary")
  let limits : Limits := { zstd := { ({} : Limits).zstd with window := 0, commandsPerBlock := 0 } }
  for page in seen.pages do
    let .dataV2 info := page.frame.value.kind | continue
    let start := page.start.state
    let remaining := binding.chunk.metadata.numValues.toNat - start.slot
    let rows := binding.rowGroup.numRows.toNat
    let result :=
      if info.encoding = 8 then
        decodeV2DictionaryPage limits binding.leaf original.entries file page.frame start remaining rows original.codec
      else decodeV2Page limits binding.codec binding.leaf file page.frame start remaining rows
    if info.isCompressed then
      deny (.zstd (.frame (.frame .windowLimit))) result
    else
      let decoded ← take result
      unless decoded.levels = page.decoded.levels ∧ decoded.words = page.decoded.words ∧
          decoded.after = page.decoded.after do
        throw (IO.userError "raw Zstd column suffix differs with zero window and command limits")

set_option maxRecDepth 8192
"""


def mutate_frame(header, body, edit):
    """Keep the original V2 level bytes and edit only the selected codec frame."""
    if header[1][1] == 3:
        info = header[8][1]
        assert info[7][1]
        prefix = info[5][1] + info[6][1]
    else:
        prefix = 0
    size = header[2][1] - prefix
    return encode(header, body[:prefix] + edit(body[prefix:], size), header[2][1])


def verify(scratch):
    reference = REFERENCE["build_reference"](scratch)

    def decode(stored, size):
        return ZSTD["decode_frame"](reference, stored, size)

    def decode_block(codec, stored, size):
        assert codec == 6
        return decode(stored, size)

    def compress(raw, *, checksum=False):
        mode = "compress-checksum" if checksum else "compress"
        return REFERENCE["run"](reference, mode, data=raw)

    def checksummed(frame, size):
        raw = decode(frame, size)
        checked = compress(raw, checksum=True)
        assert ZSTD["frame_info"](reference, checked)[5] == 1
        assert decode(checked, size) == raw
        return checked

    def reject_native(*args, data):
        result = subprocess.run([reference, *args], input=data, capture_output=True, check=False)
        assert result.returncode == 3

    def corrupt_checksum(frame, size):
        checked = checksummed(frame, size)
        changed = checked[:-1] + bytes([checked[-1] ^ 1])
        reject_native("decode", str(size), data=changed)
        return changed

    def wrong_content_size(frame, size):
        _, header_size, _, content_size, _, _ = ZSTD["frame_info"](reference, frame)
        assert frame[4] >> 6 == 0 and frame[4] & 32 and content_size == size < 255
        changed = frame[:header_size-1] + bytes([size + 1]) + frame[header_size:]
        reject_native("decode", str(size + 1), data=changed)
        return changed

    def truncate(frame, _):
        changed = frame[:-1]
        reject_native("frame-info", data=changed)
        return changed

    def compression_dictionary(frame, _):
        descriptor = frame[4]
        assert descriptor & 3 == 0
        at = 5 if descriptor & 32 else 6
        changed = frame[:4] + bytes([descriptor | 1]) + frame[5:at] + b"\x07" + frame[at:]
        assert ZSTD["frame_info"](reference, changed)[4] == 7
        return changed

    def excess_input(frame, second):
        extra = compress(b"") if second else b"\0"
        if second:
            assert decode(extra, 0) == b""
        combined = frame + extra
        assert ZSTD["frame_info"](reference, combined)[0] == len(frame)
        return combined

    schema, groups = V1["nested_samples"]()
    alternating = [{"packet": {"flag": 0, "items": [{"lo": i % 2, "nested": {"hi": (-1)**i}}
                                                     for i in range(160)]}, "seq": 1}]
    indexed_groups = [groups[0], alternating]
    extra_plain = [{"packet": {"flag": 111, "items": [{"lo": 2, "nested": {"hi": -3}}] * 32},
                    "seq": 9}] * 2
    fall_groups = [groups[0], SHARED["FALLBACK"]["rows_for_fallback"]() + extra_plain]
    genuine = {
        "v1": write(schema, groups, compression="ZSTD"),
        "v2": write(schema, groups, compression="ZSTD", data_page_version="2.0"),
        "v2_compressed_indices": write(schema, indexed_groups, compression="ZSTD", data_page_version="2.0",
                                       data_page_size=32768),
        "v1_fallback": write(schema, fall_groups, compression="ZSTD", dictionary_pagesize_limit=48),
        "v2_fallback": write(schema, fall_groups, compression="ZSTD", data_page_version="2.0",
                             dictionary_pagesize_limit=48),
    }
    for wire in genuine.values():
        assert all(metadata[4][1] == 6 for _, metadata, _, _ in V2["columns"](wire))
    for label in ("v1_fallback", "v2_fallback"):
        for position, frames in raw_chunks(genuine[label]).items():
            if position[0] == 1:
                tags = [SHARED["FALLBACK"]["original_encoding"](header_body(frame)[0]) for frame in frames[1:]]
                assert 0 in tags and 8 in tags and tags == sorted(tags, reverse=True)

    v1, v2 = genuine["v1"], genuine["v2_compressed_indices"]
    key, dict_key, target = (1, 0), (1, 1), 1
    continuation, cont_schema, cont_groups = SHARED["author_continuation"](scratch, compress=compress, codec=6)

    def append_index_byte(header, body):
        return SHARED["append_index_byte"](header, body, decode=decode, compress=compress)

    edited = {
        "v2_raw_bypass": replace_page(v2, key, target,
                                      lambda header, body: SHARED["raw_bypass"](header, body, decode=decode)),
        "v1_midrow_fallback": continuation,
        "late_v1_indices": replace_page(v1, key, target, append_index_byte),
        "late_v2_indices": replace_page(v2, key, target, append_index_byte),
    }

    def stored_crc(header, body):
        return encode(header, body[:-1] + bytes([body[-1] ^ 1]), header[2][1], crc=False)

    def wrong_extent(header, body):
        return encode(header, body, header[2][1] + 1)

    for label, wire, position, page in (("dictionary", genuine["v1_fallback"], dict_key, 0),
                                       ("v1", v1, key, target), ("v2", v2, key, target)):
        edited[f"{label}_checksummed"] = replace_page(wire, position, page,
            lambda header, body: mutate_frame(header, body, checksummed))
        edited[f"{label}_stored_crc"] = replace_page(wire, position, page, stored_crc)
        edited[f"{label}_extent"] = replace_page(wire, position, page, wrong_extent)
        for suffix, transform in (("content_crc", corrupt_checksum),
                                  ("trailing", lambda frame, _: excess_input(frame, False)),
                                  ("second_frame", lambda frame, _: excess_input(frame, True))):
            edited[f"{label}_{suffix}"] = replace_page(wire, position, page,
                lambda header, body: mutate_frame(header, body, transform))
    edited["compression_dictionary_id"] = replace_page(genuine["v1_fallback"], dict_key, 0,
        lambda header, body: mutate_frame(header, body, compression_dictionary))
    edited["truncated_v2_frame"] = replace_page(v2, key, target,
        lambda header, body: mutate_frame(header, body, truncate))
    edited["v2_content_size"] = replace_page(v2, key, target,
        lambda header, body: mutate_frame(header, body, wrong_content_size))

    edited["raw_v2_extent"] = replace_page(edited["v2_raw_bypass"], key, target, wrong_extent)
    dict_frame = raw_chunks(v2)[key][0]
    dict_header, dict_payload = header_body(dict_frame)
    dictionary_raw_size = len(dict_frame) - len(dict_payload) + dict_header[2][1]
    for field, delta, label in ((6, -dictionary_raw_size, "missing_dictionary_from_total"),
                                (7, -1, "short_stored_total")):
        footer = MIXED["metadata"](v2)
        leaf = THRIFT["column_metadata"](footer, *key)
        leaf[field] = I64, leaf[field][1] + delta
        edited[label] = V1["SCHEMA"]["pack"](v2, footer)

    files = genuine | edited
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)
    positives = {
        "v1": (schema, groups), "v2": (schema, groups),
        "v2_compressed_indices": (schema, indexed_groups),
        "v1_fallback": (schema, fall_groups), "v2_fallback": (schema, fall_groups),
        "v2_raw_bypass": (schema, indexed_groups), "v1_midrow_fallback": (cont_schema, cont_groups),
        "dictionary_checksummed": (schema, fall_groups), "v1_checksummed": (schema, groups),
        "v2_checksummed": (schema, indexed_groups),
    }
    bridge = [BRIDGE["LEAN"], "set_option maxRecDepth 8192", *V1["ENTRY"]]
    captured, fixture_checks, frame_count, flags_seen = {}, {}, 0, set()
    for label, (declarations, rows) in positives.items():
        code = fixture_checks[label] = []
        wire = files[label]
        chunks = raw_chunks(wire)
        captured[label] = {}
        for column, dictionary, traces, spans in V1["inspect"](wire, declarations, rows,
                                                               decode_block=decode_block):
            assert dictionary is not None
            captured[label][column.group, column.index] = column
            code.append(CHUNK["check_term"](column, label))
            code.append(V1["dictionary_term"](column, dictionary, traces, label))
            code.append(f'  spans (← load folder "{label}") {column.group} {column.index} {lst(spans)}')
            stored = chunks[column.group, column.index]
            raw = []
            raw_total = 0
            frame_count += len(stored)
            for frame in stored:
                header, body = header_body(frame)
                raw_total += len(frame) - len(body) + header[2][1]
                raw.append(f"(Bytes.ofList {list(SHARED['frame_bytes'](header, body, decode=decode))})")
                if header[1][1] == 3:
                    info = header[8][1]
                    flags_seen.add((label, info[4][1], info[7][1]))
            code.append(f'  rawPayloads (← load folder "{label}") {column.group} {column.index} '
                        f'.zstd {raw[0]} {lst(raw[1:])} {column.stop - column.start} {raw_total}')
            if any(span != "none" for span in spans):
                code.append(f'  checkRawBypass (← load folder "{label}") {column.group} {column.index}')
        fields, batches, counts = BRIDGE["observed"](wire)
        assert counts == [len(group) for group in rows]
        bridge.append(f'  emit folder "{label}" (← load folder "{label}") {fields} {batches}')
    assert {("v2", 8, False), ("v2_compressed_indices", 8, True), ("v2_raw_bypass", 8, False),
            ("v2_fallback", 0, False), ("v2_fallback", 0, True)} <= flags_seen
    last = captured["v1_midrow_fallback"][0, 0].pages[-1]
    assert last.before[2] and last.events[0][0] == 1 and last.before[1] == last.after[1]

    def at(label, position, page):
        lo, hi = next((lo, hi) for key, _, lo, hi in V2["columns"](files[label]) if key == position)
        return list(FRAMES(files[label], lo, hi))[page]

    def address(column):
        return f"⟨{column.group}, {column.index}, {CHUNK['path_term'](column.path)}⟩"

    code = fixture_checks["refusals"] = []

    def refuse(label, position, page, cause, limits="{}", *, original=None):
        wanted = captured[original or label][position]
        cursor_source = original if label == "short_stored_total" else label
        byte = at(cursor_source, position, page)[0]
        before = CHUNK["state_term"](wanted.pages[page - 1].before if page else (0, 0, False))
        error = f".page {address(wanted)} ⟨{page}, {byte}, {before}⟩ ({cause})"
        code.append(f'  refuse (← load folder "{label}") {wanted.group} {wanted.index} {limits} ({error})')
        return error

    def bridge_failure(label, original, error):
        terminal = f".readError (.group 1 (.chunk ({error})))"
        for positions, call in [(None, f'direct (← load folder "{label}")'),
                                ([], f'project (← load folder "{label}") []')]:
            expected = BRIDGE["observed"](files[original], positions=positions, limit=1)
            bridge.append(BRIDGE["check"](label, call, expected, terminal))
        bridge.append(f'  sourceFailure (← load folder "{label}") (.chunk ({error}))')

    original_v2 = "v2_compressed_indices"
    for label, original in (("late_v1_indices", "v1"), ("late_v2_indices", original_v2)):
        error = refuse(label, key, target, ".dictionaryIndices (.hybrid .trailingBytes)", original=original)
        bridge_failure(label, original, error)

    for prefix, position, page, original in (("dictionary", dict_key, 0, "v1_fallback"),
                                             ("v1", key, target, "v1"), ("v2", key, target, original_v2)):
        label = f"{prefix}_stored_crc"
        _, h, _, encoded = at(label, position, page)
        refuse(label, position, page, f".checksum (.mismatch {h[4][1] & 0xffffffff} {zlib.crc32(encoded)})",
               original=original)
        for suffix, cause in (("content_crc", ".checksumMismatch"),
                              ("trailing", ".trailingInput"),
                              ("second_frame", ".trailingInput")):
            label = f"{prefix}_{suffix}"
            error = refuse(label, position, page, f".zstd (.frame (.frame {cause}))", original=original)
            if prefix != "dictionary" and suffix == "content_crc":
                bridge_failure(label, original, error)

        refuse(f"{prefix}_extent", position, page, ".zstd (.scalar (.payload .outputSizeMismatch))",
               original=original)

    refuse("compression_dictionary_id", dict_key, 0,
           ".zstd (.frame (.frame (.unsupportedDictionary 7)))", original="v1_fallback")
    refuse("truncated_v2_frame", key, target, ".zstd (.frame (.frame .truncated))", original=original_v2)
    refuse("v2_content_size", key, target, ".zstd (.frame (.frame .contentSizeMismatch))", original=original_v2)

    _, h, _, encoded = at("v1_fallback", dict_key, 0)
    stored, raw = len(encoded), h[2][1]
    refuse("v1_fallback", dict_key, 0, f".dictionaryByteLimit {stored}", f"{{ maxDictionaryBytes := {stored - 1} }}")
    assert stored < raw
    refuse("v1_fallback", dict_key, 0, f".dictionaryRawByteLimit {raw}", f"{{ maxDictionaryBytes := {stored} }}")
    refuse("v1_fallback", dict_key, 0, ".zstd (.scalar (.payload .outputLimit))",
           f"{{ maxBodyBytes := {stored} }}")
    window = "{ zstd := { ({} : Limits).zstd with window := 0 } }"
    refuse("v1_fallback", dict_key, 0, ".zstd (.frame (.frame .windowLimit))", window)
    dict_window = ZSTD["frame_info"](reference, dict_payload)[2]
    _, h, _, encoded = at(original_v2, key, target)
    level_size = h[8][1][5][1] + h[8][1][6][1]
    assert dict_window < ZSTD["frame_info"](reference, encoded[level_size:])[2]
    refuse(original_v2, key, target, ".zstd (.frame (.frame .windowLimit))",
           f"{{ zstd := {{ ({{}} : Limits).zstd with window := {dict_window} }} }}")
    refuse(original_v2, key, target, ".zstd (.frame (.compressed (.block (.tables (.prefix .sequenceLimit)))))",
           "{ zstd := { ({} : Limits).zstd with commandsPerBlock := 0 } }")
    assert h[8][1][7][1] and len(dict_payload) < len(encoded) < h[2][1]
    refuse(original_v2, key, target, ".checksum .byteLimit", f"{{ maxBodyBytes := {len(encoded) - 1} }}")
    refuse(original_v2, key, target, ".payload .outputLimit", f"{{ maxBodyBytes := {len(encoded)} }}")
    refuse(original_v2, key, target, ".framing .pageLimit", "{ framing.maxPages := 1 }")
    refuse("raw_v2_extent", key, target, ".framing (.header .invalidV2Lengths)", original=original_v2)
    refuse("short_stored_total", key, target, ".framing .payloadBounds", original=original_v2)
    column = captured[original_v2][key]
    plain = THRIFT["column_metadata"](MIXED["metadata"](v2), *key)[6][1]
    code.append(f'  refuse (← load folder "missing_dictionary_from_total") 1 0 {{}} '
                f'(.chunk {address(column)} ⟨{column.start}, {column.stop}⟩ '
                f'(.uncompressedSize {plain - dictionary_raw_size} {plain}))')

    driver = [LEAN]
    for label, checks in fixture_checks.items():
        driver.extend([f"private def check_{label} (folder : String) : IO Unit := do", *checks, ""])
    driver.extend(V1["ENTRY"])
    driver.extend(f"  check_{label} folder" for label in fixture_checks)
    V2["run_lean"](scratch, "Chunk.lean", driver)
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
    print(f"Checked {frame_count} original frames and {len(ipc)} native IPC streams through exact EOS")
    print(f"Checked {len(fixture_checks['refusals'])} typed refusals")
    return {"genuine_parquet": fingerprints(genuine),
            "labeled_edits": fingerprints(edited), "lean_ipc": fingerprints(ipc)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    assert pins["libzstd"] == REFERENCE["PIN"]
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for name, values in captured.items():
        assert values == pins[name], f"{name} fixture pins changed"


if __name__ == "__main__":
    main()
