"""Check original signed LIST-path dictionaries, data pages and strict IPC."""

from copy import deepcopy
from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import struct
import tempfile
import zlib

import pyarrow as pa
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
BASE = runpy.run_path(str(HERE.parent / "parquet-recursive-list-path-snappy-oracle/check.py"))
NATIVE, EVENTS, TWO, GROUP, V1, V2, FRAMES = (
    BASE[key] for key in ("NATIVE", "EVENTS", "TWO", "GROUP", "V1", "V2", "FRAMES")
)
capture, chunk, schema_for, samples, page_term, triple, metadata, inspect_ipc = (
    BASE[key] for key in ("capture", "chunk", "schema_for", "samples", "page_term", "triple", "metadata", "inspect_ipc")
)
raw_chunks, repack, header_body, encode, level_bytes, expand, lst, write, fingerprints = (
    BASE[key] for key in ("raw_chunks", "repack", "header_body", "encode", "level_bytes",
                         "expand", "lst", "write", "fingerprints")
)
levels, v1_frame, v2_frame = (BASE["BASE"][key] for key in ("levels", "v1_frame", "v2_frame"))
THRIFT, SCHEMA = TWO["THRIFT"], TWO["SCHEMA"]

LEAN = BASE["BASE"]["LEAN"] + """
open RecursiveSchema.Repeated.Chunk (storedChunkBytes rawChunkBytes)

private def checkDictionary (file : Bytes) (depth group : Nat) (frame : Page.Frame)
    (codec : RecursiveSchema.Repeated.Chunk.DictionaryCodec)
    (entries : List RecursiveSchema.Chunk.Word) (stored raw : Nat) : IO Unit := do
  let source ← take (openFile { maxSchemaDepth := 2 * depth + 2 } file)
  let binding ← take (Chunk.bind source.schema group)
  let result ← take (Chunk.read {} binding)
  let some table := result.dictionary | throw (IO.userError "dictionary was not retained")
  unless table.codec = codec ∧ table.frame = frame ∧ table.entries.toList = entries ∧
      RecursiveSchema.Repeated.Chunk.DictionaryCodec.ofId binding.column.metadata.codec = some codec ∧
      binding.codec.column = codec.column ∧
      binding.column.metadata.dictionaryPageOffset = some (Int.ofNat frame.header.start) ∧
      binding.column.metadata.dataPageOffset = Int.ofNat frame.payload.stop ∧
      result.pages.head?.map (·.frame.header.start) = some frame.payload.stop ∧
      storedChunkBytes result.frames = stored ∧ rawChunkBytes result.frames = raw do
    throw (IO.userError "dictionary frame, entries, anchors or totals differ")
"""


def original_frames(wire, group=1):
    return list(FRAMES(wire, *chunk(wire, (group, 0))))


def address(depth, group):
    return f'⟨{group}, 0, {json.dumps(["chain"] + ["list", "element"] * depth)}⟩'


def suffix_start(header, body):
    if header[1][1] == 3:
        return level_bytes(header)
    first = 4 + int.from_bytes(body[:4], "little")
    return first + 4 + int.from_bytes(body[first:first + 4], "little")


def authored_page(template, trace, table, *, encoding, page_version):
    if page_version == 1:
        header, body = header_body(v1_frame(template, trace, 32))
        header[5][1][2] = TType.I32, encoding
    else:
        header, body = header_body(v2_frame(template, trace, flag=True))
        header[8][1][4] = TType.I32, encoding
    if encoding == 8:
        selected = (table.index(word) for _, _, word in trace if word is not None)
        body = body[:suffix_start(header, body)] + b"\x08" + b"".join(bytes((2, index)) for index in selected)
    return encode(header, body, len(body))


def nested_row(words, depth):
    for _ in range(depth - 1):
        words = [words]
    return words


def fixtures():
    genuine, authored, positives, controls = {}, {}, {}, []

    def native(label, depth, width, page_version, *, fallback=False, codec=0):
        nullable = (True,) * (depth + 1) if depth != 6 else (True, False) * 3 + (True,)
        schema, groups = schema_for(nullable, width), samples(nullable, width)
        if depth == 3 and width == 32:
            groups[1] = [groups[1][0], [], groups[1][1], groups[1][2]]
        if fallback:
            groups[1] += [nested_row([100 + i * 4 + j for j in range(4)], depth) for i in range(6)]
        case = schema, nullable, width, groups
        genuine[label] = write(schema, groups, use_dictionary=True, data_page_version=f"{page_version}.0",
                               max_rows_per_page=1, write_batch_size=1, data_page_size=16,
                               write_page_checksum=depth != 6, compression="SNAPPY" if codec else "NONE",
                               **({"dictionary_pagesize_limit": 16} if fallback else {}))
        return case

    for depth in (2, 3, 6):
        for width in (32, 64):
            for page_version in (1, 2):
                key = f"native_{width}_depth_{depth}_v{page_version}"
                positives[key] = native(key, depth, width, page_version), [0, 0]
    for width in (32, 64):
        for page_version in (1, 2):
            key = f"fallback_{width}_v{page_version}"
            positives[key] = native(key, 3, width, page_version, fallback=True), [0, 0]

    nullable = (True,) * 4
    schema = schema_for(nullable, 32)
    groups = [[None, [], [None, [], [None, [], [None]]]]]
    genuine["empty_dictionary"] = write(schema, groups, data_page_version="2.0", use_dictionary=True,
                                        max_rows_per_page=1)
    positives["empty_dictionary"] = (schema, nullable, 32, groups), [0]

    key = "native_32_depth_3_v1"
    wire = genuine[key]
    case, _ = positives[key]
    schema, nullable, width, groups = case
    chunks = raw_chunks(wire)
    original = chunks[GROUP]
    v1, v2 = original[1], raw_chunks(genuine["native_32_depth_3_v2"])[GROUP][1]
    table = [value for value, in struct.iter_unpack("<i", header_body(original[0])[1])]
    first, *tail = [levels([row], nullable) for row in groups[1]]
    cuts = [0]
    for rep in (1, 2, 3):
        cuts.append(next(i for i in range(cuts[-1] + 1, len(first)) if first[i][0] == rep))
    pieces = [first[a:b] for a, b in zip(cuts, cuts[1:] + [len(first)], strict=True)]
    pages = [authored_page(v1, trace, table, encoding=tag, page_version=1)
             for trace, tag in zip(pieces, (0, 8, 0, 8), strict=True)]
    pages.extend(authored_page(v2, trace, table, encoding=8, page_version=2) for trace in tail)
    mixed = [original[0], *pages]
    authored["mixed_versions_fallback"] = repack(wire, chunks | {GROUP: mixed})
    positives["mixed_versions_fallback"] = positives[key]

    # Keep the original identity dictionary group and copy an original Snappy PLAIN group.
    genuine["plain_snappy"] = write(schema, groups, compression="SNAPPY", data_page_version="2.0")
    footer = metadata(wire)
    snappy_column = deepcopy(THRIFT["column_metadata"](metadata(genuine["plain_snappy"]), 0, 0))
    dest = THRIFT["column_metadata"](footer, 0, 0)
    dest.clear()
    dest.update(snappy_column)
    authored["mixed_codec_groups"] = repack(wire, chunks | {(0, 0): raw_chunks(genuine["plain_snappy"])[0, 0]}, footer)
    positives["mixed_codec_groups"] = case, [1, 0]

    dictionaries = {}
    seen = capture(authored["mixed_versions_fallback"], *case, dictionaries=dictionaries)[1][-1]

    def replace(label, frames):
        authored[label] = repack(wire, chunks | {GROUP: frames})

    def dictionary_error(name, ordinal, cause, *, cap="{}", late=False):
        target = original_frames((genuine | authored)[name])
        at = target[ordinal][0]
        value = f".dictionary {address(3, 1)} {ordinal} {at} ({cause})"
        controls.append((name, cap, value, key if late else None))

    def page_error(name, ordinal, state, cause, *, cap="{}", late=False):
        at = original_frames((genuine | authored)[name])[ordinal][0]
        value = f".page {address(3, 1)} {ordinal} {at} {triple(state)} ({cause})"
        controls.append((name, cap, value, key if late else None))

    table_header, table_body = header_body(original[0])
    changed = bytes([table_body[0] ^ 1]) + table_body[1:]
    replace("late_dictionary_crc", [encode(table_header, changed, len(changed), crc=False), *original[1:]])
    crc = table_header[4][1] & 0xffffffff
    dictionary_error("late_dictionary_crc", 0, f".checksum (.mismatch {crc} {zlib.crc32(changed)})", late=True)
    table_header[7][1][1] = TType.I32, len(table) + 1
    replace("bad_entry_count", [encode(table_header, table_body, len(table_body)), *original[1:]])
    dictionary_error("bad_entry_count", 0, ".plain .truncated")
    dictionary_error(key, 0, f".dictionaryEntryLimit {len(table)}", cap="{ maxDictionaryEntries := 0 }")
    dictionary_error(key, 0, f".dictionaryByteLimit {len(table_body)}", cap="{ maxDictionaryBytes := 0 }")

    replace("missing_dictionary_frame", original[1:])
    dictionary_error("missing_dictionary_frame", 0, ".missingDictionary")
    footer = metadata(wire)
    del THRIFT["column_metadata"](footer, *GROUP)[11]
    authored["missing_dictionary_offset"] = repack(wire, chunks | {GROUP: original[1:]}, footer)
    dictionary_error("missing_dictionary_offset", 0, ".missingDictionary")
    footer = metadata(wire)
    column = THRIFT["column_metadata"](footer, *GROUP)
    actual = column[9][1]
    column[9] = TType.I64, actual + 1
    authored["wrong_data_offset"] = SCHEMA["pack"](wire, footer)
    dictionary_error("wrong_data_offset", 1, f".dataOffset {actual + 1} {actual}")
    footer = metadata(wire)
    column = THRIFT["column_metadata"](footer, *GROUP)
    column[11] = TType.I64, column[9][1]
    for total in (6, 7):
        column[total] = TType.I64, column[total][1] - len(original[0])
    authored["wrong_dictionary_offset"] = SCHEMA["pack"](wire, footer)
    dictionary_error("wrong_dictionary_offset", 0, ".missingDictionary", late=True)
    replace("duplicate_dictionary", mixed[:2] + [mixed[0]] + mixed[2:])
    page_error("duplicate_dictionary", 2, seen[1][-3], ".dictionary .misplacedDictionary")

    for version, ordinal in ((1, 4), (2, 7)):
        header, body = header_body(mixed[ordinal])
        split = suffix_start(header, body)
        indices = body[split:]
        assert indices[0] == 8 and len(indices) >= 3, (version, ordinal, indices)
        selected = (len(indices) - 1) // 2
        assert 0 < selected < 63
        for name, malformed, cause in (
            ("index_bounds", indices[:2] + bytes([len(table)]) + indices[3:], f".outOfBounds {len(table)}"),
            ("index_count", indices[:-2], ".hybrid .truncated"),
            ("index_overcount", bytes((8, 2 * (selected + 1), indices[2])), ".hybrid .countMismatch"),
            ("index_trailing", indices + b"\x02\0", ".hybrid .trailingBytes"),
        ):
            label = f"{name}_v{version}"
            suffix = body[:split] + malformed
            replace(label, mixed[:ordinal] + [encode(header, suffix, len(suffix))] + mixed[ordinal + 1:])
            page_error(label, ordinal, seen[ordinal - 1][-3], f".dictionaryIndices ({cause})", late=name == "index_bounds")
    page_error("mixed_versions_fallback", 2, seen[1][-3], ".dictionaryIndices .indexByteLimit",
               cap="{ indices := ⟨1024, 0⟩ }")

    # The V1 continuation is legal; the same repetition cannot start a V2 page.
    version_error = authored_page(v2, pieces[1], table, encoding=8, page_version=2)
    replace("v2_inside_row", mixed[:2] + [version_error] + mixed[3:])
    before = seen[1][-3]
    page_error("v2_inside_row", 2, before, f".v2 (.v2RowBoundary {before[0]} 1)")
    after_v2 = [(3, *tail[1][0][1:]), *tail[1][1:]]
    continuation = authored_page(v1, after_v2, table, encoding=8, page_version=1)
    replace("v1_after_v2", mixed[:6] + [continuation] + mixed[7:])
    before = seen[5][-3]
    page_error("v1_after_v2", 6, before, f".level (.closedAncestor {before[0]} 3 0)")

    footer = metadata(wire)
    column = THRIFT["column_metadata"](footer, *GROUP)
    lo, hi = chunk(wire)
    column[6] = TType.I64, column[6][1] + 1
    authored["raw_total"] = SCHEMA["pack"](wire, footer)
    controls.append(("raw_total", "{}", f".chunk {address(3, 1)} ⟨{lo}, {hi}⟩ "
                     f"(.rawSize {column[6][1]} {hi - lo})", None))
    footer = metadata(wire)
    column = THRIFT["column_metadata"](footer, *GROUP)
    column[7] = TType.I64, column[7][1] - 1
    authored["stored_total"] = SCHEMA["pack"](wire, footer)
    controls.append(("stored_total", "{}", f".chunk {address(3, 1)} ⟨{lo}, {hi - 1}⟩ "
                     "(.framing .payloadBounds)", None))

    controls.append((key, f"{{ framing.maxPages := {len(original) - 1} }}",
                     f".chunk {address(3, 1)} ⟨{lo}, {hi}⟩ (.framing .pageLimit)", None))
    positives["compressed_dictionary"] = native("compressed_dictionary", 3, 32, 2, codec=1), [1, 1]
    return genuine, authored, positives, controls


def source_commands(label, wire, case, codecs, decode):
    schema, nullable, width, groups = case
    depth = len(nullable) - 1
    terms = NATIVE["CORE"]["ROWS"]
    dictionaries = {}
    observations = capture(wire, *case, codecs=codecs, expand=decode, dictionaries=dictionaries)
    tags = {0: "uncompressed", 1: "snappy", 2: "gzip", 6: "zstd", 7: "lz4Raw"}
    checks, layouts = [], []
    for group, ((lo, hi, stop, pages), rows) in enumerate(zip(observations, groups, strict=True)):
        frames = list(FRAMES(wire, lo, hi))
        codec = codecs[group]
        if group in dictionaries:
            at, payload, crc, size, entries = dictionaries[group]
            dictionary_header = frames[0][1]
            sorted_flag = dictionary_header[7][1].get(3)
            sorted_term = "none" if sorted_flag is None else f"some {str(sorted_flag[1]).lower()}"
            crc_term = "none" if crc is None else f"some {crc}"
            raw_size = dictionary_header[2][1]
            frame = (f"⟨⟨{raw_size}, {size}, {crc_term}, .dictionary ⟨{len(entries)}, 0, {sorted_term}⟩⟩, "
                     f"⟨{at}, {payload}⟩, ⟨{payload}, {payload + size}⟩⟩")
            words = lst(f".int{width} ({word})" for word in entries)
            raw = sum(body_at - at + header[2][1] for at, header, body_at, _ in frames)
            checks.append(f'  checkDictionary (← load folder "{label}") {depth} {group} {frame} .{tags[codec]} '
                          f'{words} {hi - lo} {raw}')
            frames = frames[1:]
        expected = lst(page_term(page, width, header, codec)
                       for page, (_, header, _, _) in zip(pages, frames, strict=True))
        layouts.append(f"⟨{terms['batch_term'](rows, width)}, ⟨{lo}, {hi}⟩, {triple(stop)}, {expected}⟩")

    field = terms["field_term"](schema.field(0))
    commands = [
        f"private def verify_{label} (folder : System.FilePath) : IO Unit := do",
        f'  checkNative (← load folder "{label}") {depth} ⟨[{field}]⟩ {lst(layouts)}',
        *checks,
        f'  checkIpc folder "{label}" (← load folder "{label}") {depth} '
        f'{EVENTS["declarations"](schema)} {EVENTS["batch_terms"](groups, width)}',
    ]
    if depth == 2:
        commands.append(f'  compareTwoList (← load folder "{label}")')
    return observations, dictionaries, commands


def verify(folder):
    genuine, authored, positives, controls = fixtures()
    files = genuine | authored
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)
    code, entry = [LEAN], [*V1["ENTRY"]]
    pages_count = dictionaries_count = fallback_pages = 0
    for label, (case, codecs) in positives.items():
        wire = files[label]
        observations, dictionaries, commands = source_commands(label, wire, case, codecs, expand)
        expected_dictionaries = [1] if label == "mixed_codec_groups" else list(range(len(observations)))
        assert list(dictionaries) == expected_dictionaries
        if label == "empty_dictionary":
            assert dictionaries[0][-1] == []
        dictionaries_count += len(dictionaries)
        for group, (lo, hi, _, pages) in enumerate(observations):
            pages_count += len(pages)
            if group in dictionaries:
                frames = list(FRAMES(wire, lo, hi))[1:]
                encodings = [header[8][1][4][1] if header[1][1] == 3 else header[5][1][2][1]
                             for _, header, _, _ in frames]
                fallback_pages += encodings.count(0)
                if label.startswith("fallback") and group == 1:
                    assert 0 in encodings and 8 in encodings and encodings[-1] == 0
        code.extend(commands)
        entry.append(f"  verify_{label} folder")

    for label, caps, wanted, late in controls:
        entry.append(f'  refuse (← load folder "{label}") 1 {caps} ({wanted})')
        if late is not None:
            (schema, _, width, groups), _ = positives[late]
            entry.append(f'  sourceFailure (← load folder "{label}") {EVENTS["declarations"](schema)} '
                         f'{EVENTS["batch_terms"](groups[:1], width)} (.group 1 (.chunk ({wanted})))')
    V2["run_lean"](folder, "ListPathDictionary.lean", code + entry)

    emitted = {}
    for label, ((schema, _, _, groups), _) in positives.items():
        for selection in ("field", "empty"):
            name = f"{label}_{selection}"
            wire = emitted[name] = (folder / f"{name}.arrow").read_bytes()
            inspect_ipc(wire, schema, groups, selection)
    for selection in ("field", "empty"):
        original = emitted[f"native_32_depth_3_v1_{selection}"]
        for label in ("native_32_depth_3_v2", "mixed_versions_fallback", "mixed_codec_groups"):
            assert emitted[f"{label}_{selection}"] == original
    print(f"Checked {len(positives)} native inputs, {dictionaries_count} original dictionaries, {pages_count} data pages "
          f"({fallback_pages} PLAIN fallback), {len(emitted)} streams through exact EOS and {len(controls)} typed controls")
    return {kind: fingerprints(values) for kind, values in {
        "genuine_parquet": genuine, "authored_parquet": authored, "lean_ipc": emitted,
    }.items()}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for kind, fixtures in captured.items():
        assert fixtures == pins[kind], f"{kind} fixture pins changed"


if __name__ == "__main__":
    main()
