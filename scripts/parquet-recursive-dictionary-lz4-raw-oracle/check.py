"""Compare original dictionary-first LZ4_RAW Parquet frames against pinned liblz4."""

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
SHARED = runpy.run_path(str(HERE.parent / "parquet-recursive-dictionary-snappy-oracle/check.py"))
V1, V2, BRIDGE, STREAM, CHUNK, THRIFT, MIXED, FRAMES, fingerprints, lst, I32, I64 = (
    SHARED[key] for key in ("V1", "V2", "BRIDGE", "STREAM", "CHUNK", "THRIFT", "MIXED",
                           "FRAMES", "fingerprints", "lst", "I32", "I64")
)
write, encode, replace_page, raw_chunks, header_body = (
    SHARED[key] for key in ("write", "encode", "replace_page", "raw_chunks", "header_body")
)


def verify(scratch):
    lib = LZ4["build_reference"](scratch)

    def reference(block, size):
        return LZ4["reference_decode"](lib, block, size)

    def decode(block, size):
        raw = reference(block, size)
        assert raw is not None and len(raw) == size
        return raw

    def decode_block(codec, block, size):
        assert codec == 7
        return decode(block, size)

    def compress(data):
        return LZ4["reference_encode"](lib, data)

    schema, groups = V1["nested_samples"]()
    alternating = [{"packet": {"flag": 0, "items": [{"lo": i % 2, "nested": {"hi": (-1)**i}}
                                                     for i in range(160)]}, "seq": 1}]
    indexed_groups = [groups[0], alternating]
    fall_groups = [groups[0], SHARED["FALLBACK"]["rows_for_fallback"]()]
    genuine = {
        "v1": write(schema, groups, compression="LZ4"),
        "v2": write(schema, groups, compression="LZ4", data_page_version="2.0"),
        "v2_compressed_indices": write(schema, indexed_groups, compression="LZ4", data_page_version="2.0",
                                       data_page_size=32768),
        "v1_fallback": write(schema, fall_groups, compression="LZ4", dictionary_pagesize_limit=48),
        "v2_fallback": write(schema, fall_groups, compression="LZ4", data_page_version="2.0",
                             dictionary_pagesize_limit=48),
    }
    for wire in genuine.values():
        assert all(metadata[4][1] == 7 for _, metadata, _, _ in V2["columns"](wire))
    for label in ("v1_fallback", "v2_fallback"):
        for position, frames in raw_chunks(genuine[label]).items():
            if position[0] == 1:
                tags = [SHARED["FALLBACK"]["original_encoding"](header_body(frame)[0]) for frame in frames[1:]]
                assert 0 in tags and 8 in tags and tags == sorted(tags, reverse=True)

    v1, v2 = genuine["v1"], genuine["v2_compressed_indices"]
    key, dict_key = (1, 0), (1, 1)
    target = 1
    continuation, cont_schema, cont_groups = SHARED["author_continuation"](scratch, compress=compress, codec=7)

    def append_index_byte(header, body):
        return SHARED["append_index_byte"](header, body, decode=decode, compress=compress)

    edited = {
        "v2_raw_bypass": replace_page(v2, key, target,
                                      lambda header, body: SHARED["raw_bypass"](header, body, decode=decode)),
        "v1_midrow_fallback": continuation,
        "late_v1_indices": replace_page(v1, key, target, append_index_byte),
        "late_v2_indices": replace_page(v2, key, target, append_index_byte),
    }

    def wrong_extent(header, body):
        return encode(header, body, header[2][1] + 1)

    def trailing(header, body):
        levels = 0
        if header[1][1] == 3:
            info = header[8][1]
            assert info[7][1]
            levels = info[5][1] + info[6][1]
        assert reference(body[levels:] + b"\0", header[2][1] - levels) is None
        return encode(header, body + b"\0", header[2][1])

    def crc_corrupt(header, body):
        return encode(header, body[:-1] + bytes([body[-1] ^ 1]), header[2][1], crc=False)

    def framed_dictionary(header, body):
        payload = pa.Codec("lz4").compress(decode(body, header[2][1])).to_pybytes()
        assert payload.startswith(bytes.fromhex("04 22 4d 18"))
        assert reference(payload, header[2][1]) is None
        return encode(header, payload, header[2][1])

    def malformed_v2(header, body):
        info = header[8][1]
        levels = info[5][1] + info[6][1]
        assert info[7][1] and reference(b"\xf0", header[2][1] - levels) is None
        return encode(header, body[:levels] + b"\xf0", header[2][1])

    dictionary_carrier = genuine["v1_fallback"]
    for name, change in (("dictionary_crc", crc_corrupt), ("dictionary_trailing", trailing),
                         ("dictionary_extent", wrong_extent), ("framed_dictionary", framed_dictionary)):
        edited[name] = replace_page(dictionary_carrier, dict_key, 0, change)
    for name, change in (("v2_bad_block", malformed_v2), ("v2_crc", crc_corrupt),
                         ("v2_trailing", trailing), ("v2_extent", wrong_extent)):
        edited[name] = replace_page(v2, key, target, change)
    edited["v1_extent"] = replace_page(v1, key, target, wrong_extent)
    edited["v2_raw_extent"] = replace_page(edited["v2_raw_bypass"], key, target, wrong_extent)

    dictionary_frame = raw_chunks(v2)[key][0]
    dictionary_header, dictionary_payload = header_body(dictionary_frame)
    dictionary_raw_size = len(dictionary_frame) - len(dictionary_payload) + dictionary_header[2][1]
    for field, delta, label in ((6, -dictionary_raw_size, "missing_dictionary_from_total"),
                                (7, -1, "short_stored_total")):
        footer = MIXED["metadata"](v2)
        leaf = THRIFT["column_metadata"](footer, *key)
        leaf[field] = I64, leaf[field][1] + delta
        edited[label] = V1["SCHEMA"]["pack"](v2, footer)

    footer = MIXED["metadata"](v2)
    THRIFT["column_metadata"](footer, *key)[4] = I32, 5
    edited["legacy_id"] = V1["SCHEMA"]["pack"](v2, footer)
    files = genuine | edited
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)

    positives = {
        "v1": (schema, groups), "v2": (schema, groups),
        "v2_compressed_indices": (schema, indexed_groups),
        "v1_fallback": (schema, fall_groups), "v2_fallback": (schema, fall_groups),
        "v2_raw_bypass": (schema, indexed_groups), "v1_midrow_fallback": (cont_schema, cont_groups),
    }
    code, bridge = [SHARED["LEAN"], *V1["ENTRY"]], [BRIDGE["LEAN"], *V1["ENTRY"]]
    captured, frames_seen, flags_seen = {}, 0, set()
    for label, (declarations, rows) in positives.items():
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
            raw_size = 0
            frames_seen += len(stored)
            for frame in stored:
                header, body = header_body(frame)
                raw_size += len(frame) - len(body) + header[2][1]
                raw.append(f"(Bytes.ofList {list(SHARED['frame_bytes'](header, body, decode=decode))})")
                if header[1][1] == 3:
                    info = header[8][1]
                    flags_seen.add((label, info[4][1], info[7][1]))
            code.append(f'  rawPayloads (← load folder "{label}") {column.group} {column.index} '
                        f'.lz4Raw {raw[0]} {lst(raw[1:])} {column.stop - column.start} {raw_size}')
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

    def refuse(label, position, page, cause, limits="{}", *, original=None):
        wanted = captured[original or label][position]
        cursor_source = original if label == "short_stored_total" else label
        byte = at(cursor_source, position, page)[0]
        before = CHUNK["state_term"](wanted.pages[page - 1].before if page else (0, 0, False))
        error = f".page {address(wanted)} ⟨{page}, {byte}, {before}⟩ ({cause})"
        code.append(f'  refuse (← load folder "{label}") {wanted.group} {wanted.index} {limits} ({error})')
        return error

    invalid_block = ".payload (.malformed .lz4Raw)"
    invalid_extent = ".payload .outputSizeMismatch"
    for label, original in (("late_v1_indices", "v1"), ("late_v2_indices", "v2_compressed_indices")):
        error = refuse(label, key, target, ".dictionaryIndices (.hybrid .trailingBytes)", original=original)
        terminal = f".readError (.group 1 (.chunk ({error})))"
        for positions, call in [(None, f'direct (← load folder "{label}")'),
                                ([], f'project (← load folder "{label}") []')]:
            expected = BRIDGE["observed"](files[original], positions=positions, limit=1)
            bridge.append(BRIDGE["check"](label, call, expected, terminal))
        bridge.append(f'  sourceFailure (← load folder "{label}") (.chunk ({error}))')

    for label, position, page, original in (("dictionary_crc", dict_key, 0, "v1_fallback"),
                                            ("v2_crc", key, target, "v2_compressed_indices")):
        _, h, _, encoded = at(label, position, page)
        refuse(label, position, page, f".checksum (.mismatch {h[4][1] & 0xffffffff} {zlib.crc32(encoded)})",
               original=original)
    for label, cause in (("dictionary_trailing", invalid_block), ("dictionary_extent", invalid_extent),
                         ("framed_dictionary", invalid_extent)):
        refuse(label, dict_key, 0, cause, original="v1_fallback")
    refuse("v1_extent", key, target, invalid_extent, original="v1")
    ref_v2 = "v2_compressed_indices"
    for label, cause in (("v2_bad_block", invalid_block), ("v2_trailing", invalid_block),
                         ("v2_extent", invalid_extent), ("v2_raw_extent", ".framing (.header .invalidV2Lengths)"),
                         ("short_stored_total", ".framing .payloadBounds")):
        refuse(label, key, target, cause, original=ref_v2)

    _, h, _, encoded = at("v1_fallback", dict_key, 0)
    stored, raw = len(encoded), h[2][1]
    assert stored < raw
    refuse("v1_fallback", dict_key, 0, f".dictionaryByteLimit {stored}", f"{{ maxDictionaryBytes := {stored - 1} }}")
    refuse("v1_fallback", dict_key, 0, f".dictionaryRawByteLimit {raw}", f"{{ maxDictionaryBytes := {stored} }}")
    _, h, _, encoded = at(ref_v2, key, target)
    assert h[8][1][7][1] and len(encoded) < h[2][1]
    refuse(ref_v2, key, target, ".payload .outputLimit", f"{{ maxBodyBytes := {len(encoded)} }}")
    refuse(ref_v2, key, target, ".framing .pageLimit", "{ framing.maxPages := 1 }")

    column = captured[ref_v2][key]
    plain = THRIFT["column_metadata"](MIXED["metadata"](v2), *key)[6][1]
    code.append(f'  refuse (← load folder "missing_dictionary_from_total") 1 0 {{}} '
                f'(.chunk {address(column)} ⟨{column.start}, {column.stop}⟩ '
                f'(.uncompressedSize {plain - dictionary_raw_size} {plain}))')
    code.append(f'  bindFailure (← load folder "legacy_id") 1 0 (.column {address(column)} (.codec 5))')

    V2["run_lean"](scratch, "Chunk.lean", code)
    V2["run_lean"](scratch, "Bridge.lean", bridge)
    ipc = {}
    for label, (schema, expected) in positives.items():
        wire = (scratch / f"{label}.arrow").read_bytes()
        stream = pa.ipc.open_stream(wire)
        assert stream.schema == schema
        assert [batch.to_pylist() for batch in stream] == expected
        _, cursor = STREAM["metadata"](wire)
        for group in expected:
            frame = STREAM["read_record"](wire, cursor)
            assert frame.rows == len(group)
            cursor = frame.end
        assert wire[cursor:] == STREAM["EOS"]
        ipc[label] = wire
    print(f"Checked {frames_seen} original frames, seven native IPC streams and 19 typed controls")
    return {"liblz4": LZ4["PIN"], "genuine_parquet": fingerprints(genuine), "labeled_edits": fingerprints(edited),
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
