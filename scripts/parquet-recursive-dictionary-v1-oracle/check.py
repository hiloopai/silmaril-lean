"""Check leading signed dictionaries and original V1 index streams against PyArrow."""

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
V2 = runpy.run_path(str(HERE.parent / "parquet-recursive-v2-oracle/check.py"))
BRIDGE, SCHEMA, STREAM, CHUNK, THRIFT, MIXED, FRAMES, HYBRID, fingerprints, lst = (
    V2[key] for key in ("BRIDGE", "SCHEMA", "STREAM", "CHUNK", "THRIFT", "MIXED", "FRAMES",
                        "HYBRID", "fingerprints", "lst")
)
Column, Page = CHUNK["Column"], CHUNK["Page"]
I32, I64 = TType.I32, TType.I64
ENTRY = ["public def main (args : List String) : IO Unit := do",
         '  let [folder] := args | throw (IO.userError "expected fixture folder")']

LEAN = V2["LEAN"] + """\

private def dictionary (file : Bytes) (group column : Nat)
    (wanted : Option (Nat × Nat × Nat × Option UInt32 × List Word)) (traces : List (List Nat)) :
    IO Unit := do
  let source ← take (openFile {} file)
  let binding ← take (bindChunk source.schema group column)
  let observed ← take (Parquet.RecursiveSchema.Repeated.Chunk.read {} binding)
  let actual := observed.dictionary.map fun d =>
    (d.frame.header.start, d.frame.payload.start, d.frame.payload.stop, d.frame.value.crc, d.entries.toList)
  unless actual = wanted do throw (IO.userError "dictionary frame or ordered entries differ")
  if observed.dictionary.isSome then
    let mut checked := []
    for page in observed.pages do
      let indices ← match page.frame.value.kind with
        | .dataV1 info => do
          if info.encoding ≠ 8 then pure none
          else
            let body ← take (readV1Body {} binding.codec file page.frame)
            let reps ← take (readLevels ({} : Limits).levels binding.leaf.maxRepetition info.numValues body)
            let defs ← take (readLevels ({} : Limits).levels binding.leaf.maxDefinition info.numValues reps.tail)
            pure (some defs.tail)
        | .dataV2 info => do
          if info.encoding ≠ 8 then pure none
          else
            let sections ← take (readV2Sections {} binding.leaf file page.frame info)
            let suffix ← take (readV2SuffixWith {} binding.codec page.frame info
              (bytesAt file sections.spans.values) none)
            pure (some suffix)
        | _ => throw (IO.userError "expected an original V1 or V2 data frame")
      if let some suffix := indices then
        let count := (page.decoded.levels.map LevelSlot.present).count true
        checked := (← take (Parquet.DictionaryIndex.readIndices ({} : Limits).indices count suffix)) :: checked
    unless checked.reverse = traces do throw (IO.userError "original index traces differ")
  else unless traces.isEmpty do throw (IO.userError "expected a dictionary")
"""


def write(schema, groups, **options):
    sink = pa.BufferOutputStream()
    settings = dict(compression="NONE", use_compliant_nested_type=False, store_schema=False,
                    write_page_checksum=True, write_page_index=False, data_page_size=64,
                    write_batch_size=2, max_rows_per_page=3)
    with pq.ParquetWriter(sink, schema, **(settings | options)) as writer:
        for rows in groups:
            writer.write_table(pa.Table.from_pylist(rows, schema=schema))
    return sink.getvalue().to_pybytes()


def encode(header, body, *, crc=True):
    header[2] = header[3] = I32, len(body)
    if crc:
        checksum = zlib.crc32(body)
        header[4] = I32, checksum if checksum < 2**31 else checksum - 2**32
    return THRIFT["encode"](header) + body


def raw_chunks(wire):
    return {key: [wire[start:payload + len(body)] for start, _, payload, body in FRAMES(wire, lo, hi)]
            for key, _, lo, hi in V2["columns"](wire)}


def repack(wire, chunks, footer=None):
    """Splice labeled controls and recompute the exact stored offsets and lengths."""
    footer = MIXED["metadata"](wire) if footer is None else footer
    output = bytearray(b"PAR1")
    for group, row_group in enumerate(THRIFT["list_field"](footer, 4)):
        start = len(output)
        for column, chunk in enumerate(THRIFT["list_field"](row_group, 1)):
            leaf = chunk[3][1]
            frames = chunks[group, column]
            chunk[2] = I64, len(output)
            if 11 in leaf:
                leaf[11] = I64, len(output)
                [(_, header, _, _)] = FRAMES(frames[0], 0, len(frames[0]))
                leaf[9] = I64, len(output) + (len(frames[0]) if header[1][1] == 2 else 0)
            else:
                leaf[9] = I64, len(output)
            leaf[6] = leaf[7] = I64, sum(map(len, frames))
            output.extend(b"".join(frames))
        if 5 in row_group:
            row_group[5] = I64, start
        row_group[2] = I64, len(output) - start
        if 6 in row_group:
            row_group[6] = row_group[2]
    encoded = THRIFT["encode"](footer)
    return bytes(output) + encoded + struct.pack("<I", len(encoded)) + b"PAR1"


def header_body(frame):
    [(_, header, _, body)] = FRAMES(frame, 0, len(frame))
    return header, body


def section_suffix(body, rep, definition, count):
    reps, tail = CHUNK["level_section"](body, rep, count)
    defs, suffix = CHUNK["level_section"](tail, definition, count)
    return reps, defs, body[:len(body) - len(suffix)], suffix


def raw_levels(data, maximum, count):
    if maximum == 0:
        assert data == b""
        return [0] * count
    return HYBRID(data, maximum.bit_length(), count)


def sections_v2(info, body, max_rep, max_def):
    count, nulls, rows, _, dl, rl = (info[i][1] for i in range(1, 7))
    suffix_at = rl + dl
    assert suffix_at <= len(body)
    reps = raw_levels(body[:rl], max_rep, count)
    defs = raw_levels(body[rl:suffix_at], max_def, count)
    assert (not reps or reps[0] == 0) and reps.count(0) == rows
    assert sum(level != max_def for level in defs) == nulls
    return reps, defs, body[suffix_at:]


def inspect(wire, schema, groups, *, decode_block=None):
    """Inspect raw frames independent of Lean, then compare the signed trace with PyArrow."""
    _, leaves = SCHEMA["describe"](wire, schema, [row for group in groups for row in group])
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow == schema and parquet.num_row_groups == len(groups)
    for group, expected_rows in enumerate(groups):
        assert parquet.read_row_group(group).to_pylist() == expected_rows
    for (group, column), metadata, start, stop in V2["columns"](wire):
        (_, path), field, steps, boundary = leaves[column]
        expected = [slot for row in groups[group] for slot in
                    CHUNK["from_arrow"](row[path[0]], schema.field(path[0]), path[1:])]
        codec = metadata[4][1]
        assert codec == 0 or (codec in (1, 7) and decode_block is not None)
        assert metadata[7][1] == stop - start
        slot, row, live, raw_total = 0, 0, False, 0
        dictionary, traces, pages, spans = None, [], [], []
        code = "<i" if field.type.bit_width == 32 else "<q"
        for ordinal, (at, header, payload, body) in enumerate(FRAMES(wire, start, stop)):
            tag = header[1][1]
            assert header[3][1] == len(body)
            raw_size = header[2][1]
            raw_total += (payload - at) + raw_size
            crc = header[4][1] & 0xffffffff
            assert zlib.crc32(body) == crc
            end = payload + len(body)
            if tag == 2:
                assert ordinal == 0 and at == metadata[11][1] and end == metadata[9][1]
                assert metadata[2][1][1] == [0, 3, 8]
                info = header[7][1]
                raw = decode_block(codec, body, raw_size) if codec else body
                assert len(raw) == raw_size
                entries = [word for word, in struct.iter_unpack(code, raw)]
                assert info[1][1] == len(entries) and info[2][1] == 0
                dictionary = (at, payload, end, crc, entries)
                continue
            max_rep, max_def = int(boundary is not None), len(steps)
            if tag == 0:
                info = header[5][1]
                encoding = info[2][1]
                assert [info[i][1] for i in (3, 4)] == [3, 3]
                count = info[1][1]
                raw = decode_block(codec, body, raw_size) if codec else body
                assert len(raw) == raw_size
                reps, defs, _, suffix = section_suffix(raw, max_rep, max_def, count)
                spans.append("none")
            else:
                assert tag == 3
                info = header[8][1]
                count = info[1][1]
                encoding = info[4][1]
                reps, defs, suffix = sections_v2(info, body, max_rep, max_def)
                rep_end, def_end = payload + info[6][1], end - len(suffix)
                suffix_size = raw_size - info[5][1] - info[6][1]
                if codec and info.get(7, (None, True))[1]:
                    suffix = decode_block(codec, suffix, suffix_size)
                assert len(suffix) == suffix_size
                spans.append(f"(some ({V2['schema_term'](info)}, ⟨⟨{payload}, {rep_end}⟩, "
                             f"⟨{rep_end}, {def_end}⟩, ⟨{def_end}, {end}⟩⟩))")
            nonnull = defs.count(len(steps))
            assert encoding == 0 or (encoding == 8 and dictionary is not None)
            if encoding == 8:
                assert suffix and suffix[0] <= 32
                indices = HYBRID(suffix[1:], suffix[0], nonnull)
                assert all(index < len(dictionary[-1]) for index in indices)
                traces.append(indices)
                words = [dictionary[-1][index] for index in indices]
            else:
                words = [word for word, in struct.iter_unpack(code, suffix)]
                assert len(words) == nonnull
            values = iter(words)
            events = [(rep, level, next(values) if level == len(steps) else None)
                      for rep, level in zip(reps, defs, strict=True)]
            assert events == expected[slot:slot+count]
            before = slot, row, live
            for rep, definition, _ in events:
                assert rep == 0 or live
                live = boundary is not None and definition > boundary[2]
                row += int(rep == 0)
            if tag == 3:
                live = False
            slot += count
            pages.append(Page(ordinal, at, payload, end, crc, before, (slot, row, live), events))
        assert raw_total == metadata[6][1]
        assert pages[-1].stop == stop and slot == len(expected) == metadata[5][1]
        assert row == len(groups[group]) and (dictionary is not None) == (11 in metadata)
        yield Column(group, column, path, field.type.bit_width, start, stop, slot, row, steps, pages), dictionary, traces, spans


def continuation(scratch):
    """Author dictionary indices for the checked unindexed mid-row split."""
    _, _, edits = CHUNK["continuation_fixtures"](scratch)
    source = edits["authored_continuation"]
    footer = MIXED["metadata"](source)
    leaf = THRIFT["column_metadata"](footer, 0, 0)
    leaf[2] = TType.LIST, (I32, [0, 3, 8])
    leaf[11] = I64, 4
    # The authored carrier replaces the predecessor's optional encoding statistics.
    leaf.pop(13, None)
    chunks = raw_chunks(source)
    data = []
    entries = []
    for frame in chunks[0, 0]:
        header, body = header_body(frame)
        info = header[5][1]
        _, _, prefix, suffix = section_suffix(body, 1, 3, info[1][1])
        indices = []
        for value, in struct.iter_unpack("<i", suffix):
            if value not in entries:
                entries.append(value)
            indices.append(entries.index(value))
        info[2] = I32, 8
        if indices:
            # A single width-2 packed group, with final padding.
            assert len(indices) <= 8 and max(indices) < 4
            packed = sum(index << (2 * ordinal) for ordinal, index in enumerate(indices))
            suffix = b"\x02\x03" + packed.to_bytes(2, "little")
        else:
            suffix = b"\0"
        data.append(encode(header, prefix + suffix))
    plain = b"".join(struct.pack("<i", value) for value in entries)
    dictionary = encode({1: (I32, 2), 7: (TType.STRUCT, {1: (I32, len(entries)), 2: (I32, 0)})}, plain)
    chunks[0, 0] = [dictionary, *data]
    return repack(source, chunks, footer)


def negative_files(wire, key):
    chunks = raw_chunks(wire)
    frames = chunks[key]
    assert len(frames) > 2
    dictionary, first, *later = frames

    def replace(frames):
        return repack(wire, chunks | {key: frames})

    def edit_frame(frame, edit, **options):
        header, body = header_body(frame)
        return encode(header, edit(header, body), **options)

    def indices(value):
        def edit(header, body):
            _, _, prefix, _ = section_suffix(body, 1, 4, header[5][1][1][1])
            return prefix + value
        return edit_frame(first, edit)

    def legacy(header, body):
        header[5][1][2] = I32, 2
        return body

    def change_to_plain(header, body):
        header[5][1][2] = I32, 0
        return body

    edits = {
        "missing_page": replace([first, *later]),
        "missing_offset": None,
        "second_dictionary": replace([dictionary, first, dictionary, *later]),
        "dictionary_after_data": replace([first, dictionary, *later]),
        "legacy_page": replace([dictionary, edit_frame(first, legacy), *later]),
        "plain_tag_over_indices": replace([dictionary, edit_frame(first, change_to_plain), *later]),
        "index_out_of_range": replace([dictionary, indices(b"\x08\x03" + b"\xff" * 8), *later]),
        "index_trailing": replace([dictionary, edit_frame(first, lambda _, body: body + b"\0"), *later]),
        "index_width_missing": replace([dictionary, indices(b""), *later]),
        "index_short": replace([dictionary, indices(b"\x02\x03\x00"), *later]),
        "dictionary_short": replace([edit_frame(dictionary, lambda _, body: body[:-1]), first, *later]),
        "dictionary_crc": replace([edit_frame(dictionary, lambda _, body: bytes([body[0] ^ 1]) + body[1:],
                                              crc=False), first, *later]),
    }
    footer = MIXED["metadata"](wire)
    leaf = THRIFT["column_metadata"](footer, *key)
    leaf.pop(11)
    edits["missing_offset"] = repack(wire, chunks | {key: [first, *later]}, footer)
    footer = MIXED["metadata"](wire)
    leaf = THRIFT["column_metadata"](footer, *key)
    leaf[9] = I64, leaf[9][1] + 1
    edits["wrong_data_offset"] = SCHEMA["pack"](wire, footer)
    footer = MIXED["metadata"](wire)
    leaf = THRIFT["column_metadata"](footer, *key)
    leaf[6] = I64, leaf[6][1] + 1
    edits["footer_total"] = SCHEMA["pack"](wire, footer)
    return edits


def dictionary_term(column, dictionary, traces, label):
    witness = "none"
    if dictionary:
        at, payload, stop, crc, entries = dictionary
        words = lst(f".int{column.width} ({word})" for word in entries)
        witness = f"(some ({at}, {payload}, {stop}, some {crc}, {words}))"
    return (f'  dictionary (← load folder "{label}") {column.group} {column.index} '
            f'{witness} {lst(str(trace) for trace in traces)}')


def nested_samples():
    _, samples, _ = SCHEMA["fixtures"]()
    schema, original = samples["nullable_lists"]
    live = {"flag": 2, "items": [None, {"lo": -2**31, "nested": {"hi": -2**63}},
                                {"lo": 2**31-1, "nested": {"hi": 2**63-1}},
                                {"lo": -4, "nested": None}]}
    groups = [original[:3], [{"packet": live, "seq": 2**40}] * 10 + original[3:]]
    return schema, groups


def verify(scratch):
    schema, groups = nested_samples()
    native = write(schema, groups)
    mixed = write(schema, groups, use_dictionary=["packet.items.list.élément.lo"])
    compressed = write(schema, groups, compression="GZIP")
    genuine = {"native": native, "mixed": mixed, "compressed": compressed}
    key = 1, 0
    edited = negative_files(native, key)
    edited["continuation"] = continuation(scratch)
    files = genuine | edited
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)

    single = pq.ParquetFile(pa.BufferReader(files["continuation"])).schema_arrow
    positives = {"native": (schema, groups), "mixed": (schema, groups),
                 "continuation": (single, [[{"items": item} for item in CHUNK["CONT"]["CONTINUED"]]])}
    code, bridge = [LEAN, *ENTRY], [BRIDGE["LEAN"], *ENTRY]
    captured, data_pages, dictionaries = {}, 0, 0
    for label, (declarations, rows) in positives.items():
        captured[label] = {}
        for column, dictionary, traces, _ in inspect(files[label], declarations, rows):
            captured[label][column.group, column.index] = (column, dictionary)
            data_pages += len(column.pages)
            dictionaries += int(dictionary is not None)
            code.append(CHUNK["check_term"](column, label))
            code.append(dictionary_term(column, dictionary, traces, label))
        fields, batches, counts = BRIDGE["observed"](files[label])
        assert counts == [len(group) for group in rows]
        bridge.append(f'  emit folder "{label}" (← load folder "{label}") {fields} {batches}')
    assert any(dictionary and not dictionary[-1] for _, dictionary in captured["native"].values())
    assert any(not dictionary for _, dictionary in captured["mixed"].values())
    assert any(dictionary for _, dictionary in captured["mixed"].values())
    continued = captured["continuation"][0, 0][0].pages[-1]
    assert continued.before[2] and continued.events[0][0] == 1
    assert continued.before[1] == continued.after[1]

    original_column, dictionary = captured["native"][key]
    assert dictionary and len(original_column.pages) > 1
    path = CHUNK["path_term"](original_column.path)
    group, column = key
    address = f"⟨{group}, {column}, {path}⟩"

    def page_error(label, page, cause, limits="{}"):
        raw = next((start, stop) for here, _, start, stop in V2["columns"](files[label]) if here == key)
        at = list(FRAMES(files[label], *raw))[page][0]
        before = CHUNK["state_term"](original_column.pages[page - 1].before if page else (0, 0, False))
        error = f".page {address} ⟨{page}, {at}, {before}⟩ ({cause})"
        code.append(f'  refuse (← load folder "{label}") {group} {column} {limits} ({error})')
        return error

    for label in ("missing_page", "missing_offset", "dictionary_after_data"):
        page_error(label, 0, ".missingDictionary")
    page_error("second_dictionary", 2, ".misplacedDictionary")
    page_error("legacy_page", 1, ".header (.encoding 2 3 3)")
    page_error("plain_tag_over_indices", 1, ".plain .truncated")
    page_error("index_out_of_range", 1, ".dictionaryIndices (.outOfBounds 255)")
    late = page_error("index_trailing", 1, ".dictionaryIndices (.hybrid .trailingBytes)")
    page_error("index_width_missing", 1, ".dictionaryIndices .missingBitWidth")
    page_error("index_short", 1, ".dictionaryIndices (.hybrid .truncated)")
    page_error("dictionary_short", 0, ".plain .truncated")
    start, payload, _, crc, entries = dictionary
    body = files["native"][payload:dictionary[2]]
    crc_actual = zlib.crc32(bytes([body[0] ^ 1]) + body[1:])
    page_error("dictionary_crc", 0, f".checksum (.mismatch {crc} {crc_actual})")
    page_error("native", 0, f".dictionaryEntryLimit {len(entries)}", "{ maxDictionaryEntries := 0 }")
    page_error("native", 0, f".dictionaryByteLimit {len(body)}", "{ maxDictionaryBytes := 0 }")
    page_error("native", 1, ".dictionaryIndices .indexByteLimit", "{ indices := ⟨1048576, 0⟩ }")
    page_error("native", 1, ".dictionaryIndices (.hybrid .valueLimit)", "{ indices := ⟨0, 16777216⟩ }")
    page_error("native", 1, ".framing .pageLimit", "{ framing.maxPages := 1 }")
    total = original_column.stop - original_column.start
    code.append(f'  refuse (← load folder "footer_total") {group} {column} {{}} '
                f'(.chunk {address} ⟨{start}, {original_column.stop}⟩ (.uncompressedSize {total + 1} {total}))')
    code.append(f'  refuse (← load folder "wrong_data_offset") {group} {column} {{}} '
                f'(.page {address} ⟨1, {dictionary[2]}, {{}}⟩ (.dataOffset {dictionary[2] + 1} {dictionary[2]}))')
    code.append(f'  bindFailure (← load folder "compressed") {group} {column} (.column {address} (.codec 2))')

    terminal = f".readError (.group 1 (.chunk ({late})))"
    bridge.extend([
        BRIDGE["check"]("dictionary late", 'direct (← load folder "index_trailing")',
                        BRIDGE["observed"](native, limit=1), terminal),
        BRIDGE["check"]("dictionary late empty projection", 'project (← load folder "index_trailing") []',
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
    print(f"Checked {dictionaries} dictionaries, {data_pages} original data pages, "
          "three native IPC streams and 20 typed controls")
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
