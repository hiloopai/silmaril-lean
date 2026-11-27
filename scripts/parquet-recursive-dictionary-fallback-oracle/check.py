"""Check original dictionary and PLAIN pages in the same signed recursive chunk."""

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
V1 = runpy.run_path(str(HERE.parent / "parquet-recursive-dictionary-v1-oracle/check.py"))
V2_DICT = runpy.run_path(str(HERE.parent / "parquet-recursive-dictionary-v2-oracle/check.py"))
V2, BRIDGE, STREAM, CHUNK, THRIFT, MIXED, FRAMES, HYBRID, fingerprints, lst, I32 = (
    V1[key] for key in ("V2", "BRIDGE", "STREAM", "CHUNK", "THRIFT", "MIXED", "FRAMES", "HYBRID",
                        "fingerprints", "lst", "I32")
)
write, encode, raw_chunks, repack, header_body = (
    V1[key] for key in ("write", "encode", "raw_chunks", "repack", "header_body")
)


def rows_for_fallback():
    def entry(i):
        return {
            "flag": i,
            "items": [None, {"lo": -2**31 if i == 0 else -1000-i,
                             "nested": {"hi": -2**63 if i == 12 else 2000+i}},
                      {"lo": 2**31-1 if i == 12 else 1000+i,
                       "nested": {"hi": 2**63-1} if i == 1 else None}],
        }
    return [{"packet": entry(i), "seq": -1000-i} for i in range(16)]


def original_encoding(header):
    if header[1][1] == 0:
        return header[5][1][2][1]
    assert header[1][1] == 3
    return header[8][1][4][1]


def set_encoding(header, encoding):
    if header[1][1] == 0:
        header[5][1][2] = I32, encoding
    else:
        assert header[1][1] == 3
        header[8][1][4] = I32, encoding


def replace_chunk(wire, key, frames, *, drop_stats=False):
    footer = MIXED["metadata"](wire)
    if drop_stats:
        THRIFT["column_metadata"](footer, *key).pop(13, None)
    return repack(wire, raw_chunks(wire) | {key: frames}, footer)


def to_plain(frames, page, max_def):
    """Replace just the index suffix by exact dictionary words from this chunk."""
    _, dictionary = header_body(frames[0])
    words = [word for word, in struct.iter_unpack("<i", dictionary)]
    header, body = header_body(frames[page])
    assert original_encoding(header) == 8
    if header[1][1] == 0:
        count = header[5][1][1][1]
        _, defs, prefix, indices = V1["section_suffix"](body, 1, max_def, count)
    else:
        info = header[8][1]
        _, defs, indices = V1["sections_v2"](info, body, 1, max_def)
        prefix = body[:len(body) - len(indices)]
    assert indices
    selected = HYBRID(indices[1:], indices[0], defs.count(max_def))
    values = b"".join(struct.pack("<i", words[index]) for index in selected)
    set_encoding(header, 0)
    return encode(header, prefix + values)


def interleave(wire, key):
    """Author 0→8 and 8→0→8 without changing any levels or values."""
    frames = raw_chunks(wire)[key]
    data = [i for i in range(1, len(frames)) if original_encoding(header_body(frames[i])[0]) == 8]
    assert len(data) >= 4 and data[:4] == [1, 2, 3, 4]
    for page in (1, 3):
        frames[page] = to_plain(frames, page, 4)
    assert [original_encoding(header_body(frame)[0]) for frame in frames[1:5]] == [0, 8, 0, 8]
    return replace_chunk(wire, key, frames, drop_stats=True)


def split_row(scratch):
    v1 = V1["continuation"](scratch)
    key = (0, 0)
    frames = raw_chunks(v1)[key]
    assert len(frames) == 5
    before, after = len(frames) - 2, len(frames) - 1
    outputs = {
        "continued_into_plain": replace_chunk(v1, key,
            frames[:after] + [to_plain(frames, after, 3)], drop_stats=True),
        "continued_into_dictionary": replace_chunk(v1, key,
            frames[:before] + [to_plain(frames, before, 3), frames[after]], drop_stats=True),
    }
    # The preceding PLAIN page now closes the row under the V2 contract.
    closing = V2_DICT["v1_to_v2"](*header_body(to_plain(frames, before, 3)))
    header, payload = header_body(closing)
    set_encoding(header, 0)
    outputs["v1_after_closed_plain_v2"] = replace_chunk(v1, key,
        frames[:before] + [encode(header, payload), frames[after]], drop_stats=True)
    schema = pq.ParquetFile(pa.BufferReader(v1)).schema_arrow
    rows = [[{"items": value} for value in CHUNK["CONT"]["CONTINUED"]]]
    return outputs, schema, rows


def malformed(wire, key, page):
    frames = raw_chunks(wire)[key]

    def edit(change):
        altered = frames.copy()
        altered[page] = change(*header_body(frames[page]))
        return replace_chunk(wire, key, altered)

    def conflict(header, body):
        header[7] = TType.STRUCT, {1: (I32, 0), 2: (I32, 0)}
        return encode(header, body)

    def unsupported(header, body):
        set_encoding(header, 5)
        return encode(header, body)

    return {
        "plain_short": edit(lambda header, body: encode(header, body[:-1])),
        "plain_extra": edit(lambda header, body: encode(header, body + b"\x00")),
        "plain_crc": edit(lambda header, body: encode(header, body[:-1] + bytes([body[-1] ^ 1]), crc=False)),
        "plain_conflicting_header": edit(conflict),
        "unsupported_encoding": edit(unsupported),
    }


def verify(scratch):
    schema, sample = V1["nested_samples"]()
    groups = [sample[0], rows_for_fallback()]
    native = {label: write(schema, groups, data_page_version=ver, dictionary_pagesize_limit=48)
              for label, ver in (("v1", "1.0"), ("v2", "2.0"))}
    genuine = native | {
        "plain_only": write(schema, groups, data_page_version="2.0", use_dictionary=False),
        "dictionary_only": write(schema, groups, data_page_version="1.0", dictionary_pagesize_limit=1 << 20),
    }
    key = (1, 0)
    targets = {}
    for label, wire in native.items():
        for position, frames in raw_chunks(wire).items():
            if position[0] != key[0]:
                continue
            assert header_body(frames[0])[0][1][1] == 2
            data = [original_encoding(header_body(frame)[0]) for frame in frames[1:]]
            assert 0 in data and 8 in data and data == sorted(data, reverse=True)
            if position == key:
                targets[label] = data.index(0) + 1

    edited, positives = {}, {label: (schema, groups) for label in genuine}
    for label, wire in native.items():
        altered = interleave(wire, key)
        edited[f"{label}_interleaved"] = altered
        positives[f"{label}_interleaved"] = schema, groups
        frames = raw_chunks(altered)[key]
        edited[f"{label}_missing_leading"] = replace_chunk(altered, key, frames[1:])
        edited[f"{label}_repeated_after_plain"] = replace_chunk(altered, key, [*frames[:2], frames[0], *frames[2:]])
        edited.update({f"{label}_{name}": control
                       for name, control in malformed(wire, key, targets[label]).items()})

    cross, stand_schema, stand_rows = split_row(scratch)
    edited.update(cross)
    positives["continued_into_plain"] = positives["continued_into_dictionary"] = stand_schema, stand_rows

    files = genuine | edited
    for name, wire in files.items():
        (scratch / f"{name}.parquet").write_bytes(wire)

    code, bridge = [V1["LEAN"], *V1["ENTRY"]], [BRIDGE["LEAN"], *V1["ENTRY"]]
    capture, dictionaries, pages = {}, 0, 0
    for label, (declarations, expected) in positives.items():
        capture[label] = {}
        for column, dictionary, traces, spans in V1["inspect"](files[label], declarations, expected):
            capture[label][column.group, column.index] = column
            dictionaries += int(dictionary is not None)
            pages += len(column.pages)
            code.append(CHUNK["check_term"](column, label))
            code.append(V1["dictionary_term"](column, dictionary, traces, label))
            code.append(f'  spans (← load folder "{label}") {column.group} {column.index} {lst(spans)}')
        fields, batches, counts = BRIDGE["observed"](files[label])
        assert counts == [len(group) for group in expected]
        bridge.append(f'  emit folder "{label}" (← load folder "{label}") {fields} {batches}')

    for label, tag in (("plain_only", 0), ("dictionary_only", 8)):
        for frames in raw_chunks(genuine[label]).values():
            if tag == 8:
                assert header_body(frames[0])[0][1][1] == 2
                frames = frames[1:]
            assert frames and all(original_encoding(header_body(frame)[0]) == tag for frame in frames)

    def at(label, key, ordinal):
        lo, hi = next((lo, hi) for pos, _, lo, hi in V2["columns"](files[label]) if pos == key)
        return list(FRAMES(files[label], lo, hi))[ordinal]

    def refusal(label, key, path, ordinal, before, cause):
        group, column = key
        address = f"⟨{group}, {column}, {CHUNK['path_term'](path)}⟩"
        offset, _, _, _ = at(label, key, ordinal)
        cursor = f"⟨{ordinal}, {offset}, {CHUNK['state_term'](before)}⟩"
        error = f".page {address} {cursor} ({cause})"
        code.append(f'  refuse (← load folder "{label}") {group} {column} {{}} ({error})')
        return error

    for label in native:
        ordinal = targets[label]
        source = capture[label][key]
        before = source.pages[ordinal - 1].before
        late_label = f"{label}_plain_short"
        error = refusal(late_label, key, source.path, ordinal, before, ".plain .truncated")
        refusal(f"{label}_plain_extra", key, source.path, ordinal, before, ".plain .trailingBytes")
        edited_name = f"{label}_plain_crc"
        _, header, _, payload = at(edited_name, key, ordinal)
        refusal(edited_name, key, source.path, ordinal, before,
                f".checksum (.mismatch {header[4][1] & 0xffffffff} {zlib.crc32(payload)})")
        kind = 0 if label == "v1" else 3
        refusal(f"{label}_plain_conflicting_header", key, source.path, ordinal, before,
                f".framing (.header (.conflictingKind {kind}))")
        unsupported = ".header (.encoding 5 3 3)" if label == "v1" else ".v2Encoding 5"
        refusal(f"{label}_unsupported_encoding", key, source.path, ordinal, before, unsupported)
        interleaved = capture[f"{label}_interleaved"][key]
        refusal(f"{label}_missing_leading", key, source.path, 0, (0, 0, False), ".missingDictionary")
        refusal(f"{label}_repeated_after_plain", key, source.path, 2,
                interleaved.pages[1].before, ".misplacedDictionary")
        terminal = f".readError (.group 1 (.chunk ({error})))"
        for positions, call in [(None, f'direct (← load folder "{late_label}")'),
                                ([], f'project (← load folder "{late_label}") []')]:
            expected = BRIDGE["observed"](files[label], positions=positions, limit=1)
            bridge.append(BRIDGE["check"](late_label, call, expected, terminal))
        bridge.append(f'  sourceFailure (← load folder "{late_label}") (.chunk ({error}))')

    for label in ("continued_into_plain", "continued_into_dictionary"):
        column = capture[label][0, 0]
        last = column.pages[-1]
        assert last.events[0][0] == 1 and last.before[2] and last.after[1] == last.before[1]
    slot, row, _ = last.before
    refusal("v1_after_closed_plain_v2", (0, 0), column.path, last.index, (slot, row, False),
            f".continuationWithoutList {slot}")

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
    print(f"Checked {dictionaries} dictionaries, {pages} data pages, eight IPC streams and 15 typed controls")
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
