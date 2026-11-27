"""Compare original dictionary V2 sections with independent PyArrow and Lean readback."""

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
V1 = runpy.run_path(str(HERE.parent / "parquet-recursive-dictionary-v1-oracle/check.py"))
V2, BRIDGE, SCHEMA, STREAM, CHUNK, THRIFT, FRAMES, fingerprints, lst, I32 = (
    V1[key] for key in ("V2", "BRIDGE", "SCHEMA", "STREAM", "CHUNK", "THRIFT", "FRAMES",
                        "fingerprints", "lst", "I32")
)
write, encode, raw_chunks, repack, header_body = (
    V1[key] for key in ("write", "encode", "raw_chunks", "repack", "header_body")
)


def rewrite(wire, key, edits):
    chunks = raw_chunks(wire)
    frames = chunks[key]
    for page, edit in edits.items():
        frames[page] = edit(*header_body(frames[page]))
    return repack(wire, chunks)


def raw_flag(flag):
    def edit(header, body):
        info = header[8][1]
        if flag is None:
            del info[7]
        else:
            info[7] = TType.BOOL, flag
        return encode(header, body)
    return edit


def v1_to_v2(header, body):
    """Keep the exact dictionary index suffix and remove only the V1 length words."""
    count = header[5][1][1][1]
    reps, tail = CHUNK["level_section"](body, 1, count)
    defs, suffix = CHUNK["level_section"](tail, 3, count)
    raw_reps = body[4:len(body) - len(tail)]
    raw_defs = tail[4:len(tail) - len(suffix)]
    info = {1: (I32, count), 2: (I32, sum(level != 3 for level in defs)),
            3: (I32, reps.count(0)), 4: (I32, 8), 5: (I32, len(raw_defs)),
            6: (I32, len(raw_reps)), 7: (TType.BOOL, False)}
    return encode({1: (I32, 3), 8: (TType.STRUCT, info)}, raw_reps + raw_defs + suffix)


def controls(wire, key, page):
    def index_bytes(data):
        def edit(header, body):
            info = header[8][1]
            index_at = info[5][1] + info[6][1]
            return encode(header, body[:index_at] + data(body[index_at:]))
        return edit

    def change_info(field, value):
        def edit(header, body):
            info = header[8][1]
            info[field] = I32, value(info[field][1])
            return encode(header, body)
        return edit

    def unequal_sizes(flag):
        def edit(header, body):
            header[8][1][7] = TType.BOOL, flag
            header[2] = I32, len(body) + 1
            return THRIFT["encode"](header) + body
        return edit

    edits = {
        "index_trailing": index_bytes(lambda indices: indices + b"\0"),
        "index_truncated": index_bytes(lambda _: b"\x02\x03\x00"),
        "index_width_missing": index_bytes(lambda _: b""),
        "index_out_of_bounds": index_bytes(lambda _: b"\x08\x03" + b"\xff" * 8),
        "index_run_count": index_bytes(lambda _: b"\x01\x7e\x00"),
        "wrong_rows": change_info(3, lambda n: n + 1),
        "wrong_nulls": change_info(2, lambda n: n + 1),
        "invalid_counts": change_info(2, lambda _: 10000),
        "bad_level_extent": change_info(5, lambda _: 10000),
        "plain_tag_over_indices": change_info(4, lambda _: 0),
        "legacy_encoding": change_info(4, lambda _: 2),
        "bad_sizes_true": unequal_sizes(True),
        "bad_sizes_false": unequal_sizes(False),
        "bad_crc": lambda header, body: encode(header, body[:-1] + bytes([body[-1] ^ 1]), crc=False),
    }
    return {name: rewrite(wire, key, {page: edit}) for name, edit in edits.items()}


def verify(scratch):
    schema, groups = V1["nested_samples"]()
    _, samples, _ = SCHEMA["fixtures"]()
    _, short = samples["nullable_lists"]
    # The native fixture is byte-for-byte the V2 carrier pinned in the V1 slice.
    native = write(schema, groups, data_page_version="2.0")
    short_groups = [short[:3], short[3:]]
    short_wire = write(schema, short_groups, data_page_version="2.0")
    mixed = write(schema, groups, data_page_version="2.0",
                  use_dictionary=["packet.items.list.élément.lo"])
    compressed = write(schema, groups, data_page_version="2.0", compression="ZSTD")
    genuine = {"native": native, "zero_slot_pages": short_wire, "mixed": mixed, "compressed": compressed}
    key, target = (1, 0), 1
    edited = controls(native, key, target)
    edited["resolved_flags"] = rewrite(native, key, {target: raw_flag(True), target + 1: raw_flag(None)})
    continued = V1["continuation"](scratch)
    edited["mixed_versions"] = rewrite(continued, (0, 0), {1: v1_to_v2})
    edited["v1_after_closed_v2"] = rewrite(continued, (0, 0), {3: v1_to_v2})
    edited["v2_starts_midrow"] = rewrite(continued, (0, 0), {4: v1_to_v2})
    files = genuine | edited
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)

    standalone = pq.ParquetFile(pa.BufferReader(continued)).schema_arrow
    continued_rows = [[{"items": value} for value in CHUNK["CONT"]["CONTINUED"]]]
    positives = {
        "native": (schema, groups),
        "zero_slot_pages": (schema, short_groups),
        "mixed": (schema, groups),
        "resolved_flags": (schema, groups),
        "mixed_versions": (standalone, continued_rows),
    }
    code, bridge = [V1["LEAN"], *V1["ENTRY"]], [BRIDGE["LEAN"], *V1["ENTRY"]]
    captured, dictionaries, data_pages, zero_pages, raw_true = {}, 0, 0, 0, 0
    for label, (declarations, rows) in positives.items():
        captured[label] = {}
        for column, dictionary, traces, spans in V1["inspect"](files[label], declarations, rows):
            captured[label][column.group, column.index] = column
            dictionaries += int(dictionary is not None)
            data_pages += len(column.pages)
            zero_pages += sum(not page.events and v2 != "none" for page, v2 in zip(column.pages, spans, strict=True))
            raw_true += sum(v2 != "none" and "true⟩" in v2 for v2 in spans)
            code.append(CHUNK["check_term"](column, label))
            code.append(V1["dictionary_term"](column, dictionary, traces, label))
            code.append(f'  spans (← load folder "{label}") {column.group} {column.index} {lst(spans)}')
        fields, batches, counts = BRIDGE["observed"](files[label])
        assert counts == [len(group) for group in rows]
        bridge.append(f'  emit folder "{label}" (← load folder "{label}") {fields} {batches}')
    assert zero_pages > 0 and raw_true == 2
    positive_columns = list(V1["inspect"](short_wire, schema, short_groups))
    assert sum(dictionary is not None and not dictionary[-1] for _, dictionary, _, _ in positive_columns) == 2
    authored = captured["mixed_versions"][0, 0]
    assert authored.pages[1].before[2] is False
    assert authored.pages[-1].before[2] and authored.pages[-1].events[0][0] == 1

    original = captured["native"][key]
    group, column = key
    address = f"⟨{group}, {column}, {CHUNK['path_term'](original.path)}⟩"
    before = CHUNK["state_term"](original.pages[0].before)

    def location(label, key, page):
        start, stop = next((lo, hi) for pos, _, lo, hi in V2["columns"](files[label]) if pos == key)
        return list(FRAMES(files[label], start, stop))[page]

    def page_error(label, cause, limits="{}"):
        byte, _, _, _ = location(label, key, target)
        error = f".page {address} ⟨{target}, {byte}, {before}⟩ ({cause})"
        code.append(f'  refuse (← load folder "{label}") {group} {column} {limits} ({error})')
        return error

    _, header, _, body = location("native", key, target)
    count, nulls, rows = (header[8][1][i][1] for i in range(1, 4))
    assert 0 < count - nulls <= 8 and rows < count and nulls < count
    late = page_error("index_trailing", ".dictionaryIndices (.hybrid .trailingBytes)")
    page_error("index_truncated", ".dictionaryIndices (.hybrid .truncated)")
    page_error("index_width_missing", ".dictionaryIndices .missingBitWidth")
    page_error("index_out_of_bounds", ".dictionaryIndices (.outOfBounds 255)")
    page_error("index_run_count", ".dictionaryIndices (.hybrid .countMismatch)")
    page_error("wrong_rows", f".v2Rows {rows + 1} {rows}")
    page_error("wrong_nulls", f".v2Nulls {nulls + 1} {nulls}")
    page_error("invalid_counts", ".framing (.header .invalidV2Counts)")
    page_error("bad_level_extent", ".framing (.header .invalidV2Lengths)")
    page_error("plain_tag_over_indices", ".plain .truncated")
    page_error("legacy_encoding", ".v2Encoding 2")
    page_error("bad_sizes_true", f".header (.pageSizes {len(body) + 1} {len(body)})")
    page_error("bad_sizes_false", ".framing (.header .invalidV2Lengths)")
    _, crc_header, _, edited_body = location("bad_crc", key, target)
    page_error("bad_crc", f".checksum (.mismatch {crc_header[4][1] & 0xffffffff} {zlib.crc32(edited_body)})")
    page_error("native", ".dictionaryIndices .indexByteLimit", "{ indices := ⟨1048576, 0⟩ }")
    page_error("native", ".dictionaryIndices (.hybrid .valueLimit)", "{ indices := ⟨0, 16777216⟩ }")
    code.append(f'  bindFailure (← load folder "compressed") {group} {column} (.column {address} (.codec 6))')

    page = authored.pages[-1]
    mid_slot, mid_row, _ = page.before
    mid_addr = f"⟨0, 0, {CHUNK['path_term'](authored.path)}⟩"
    for label, live, cause in [
        ("v1_after_closed_v2", False, f".continuationWithoutList {mid_slot}"),
        ("v2_starts_midrow", True, f".v2RowBoundary {mid_slot} 1"),
    ]:
        byte, _, _, _ = location(label, (0, 0), page.index)
        state = CHUNK["state_term"]((mid_slot, mid_row, live))
        code.append(f'  refuse (← load folder "{label}") 0 0 {{}} '
                    f'(.page {mid_addr} ⟨{page.index}, {byte}, {state}⟩ ({cause}))')

    terminal = f".readError (.group 1 (.chunk ({late})))"
    bridge.extend([
        BRIDGE["check"]("V2 dictionary late", 'direct (← load folder "index_trailing")',
                        BRIDGE["observed"](native, limit=1), terminal),
        BRIDGE["check"]("V2 dictionary late empty projection", 'project (← load folder "index_trailing") []',
                        BRIDGE["observed"](native, positions=[], limit=1), terminal),
        f'  sourceFailure (← load folder "index_trailing") (.chunk ({late}))',
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
    print(f"Checked {dictionaries} dictionaries and {data_pages} data pages including {zero_pages} zero-slot V2 pages, "
          "five native IPC streams and 19 typed controls")
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
