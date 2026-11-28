"""Inspect original two-LIST dictionaries, Hybrid indices and native IPC."""

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
SNAPPY = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-snappy-oracle/check.py"))
BASE, V2, THRIFT, MIXED, SCHEMA, PATH, IPC, I32, I64, GROUP = (
    SNAPPY[key] for key in ("BASE", "V2", "THRIFT", "MIXED", "SCHEMA", "PATH", "IPC", "I32", "I64", "GROUP")
)
raw_chunks, header_body, encode, repack, expand, compress, original_frames = (
    SNAPPY[key] for key in ("raw_chunks", "header_body", "encode", "repack", "expand", "compress", "original_frames")
)
DICT = SNAPPY["SNAPPY"]["V1"]
section_suffix, sections_v2 = (DICT[key] for key in ("section_suffix", "sections_v2"))
HYBRID = V2["HYBRID"]
NULLABLE = (True, True, True)

LEAN = BASE["LEAN"] + """
open RecursiveSchema.Repeated.Chunk (rawChunkBytes storedChunkBytes)

private def checkDictionary (file : Bytes) (group : Nat) (span : Nat × Nat × Nat)
    (crc : UInt32) (entries : List Word) (rawBytes storedBytes : Nat) : IO Unit := do
  let source ← take (openFile {} file)
  let binding ← take (Chunk.bind source.schema group)
  let checked ← take (read {} binding)
  let some dictionary := checked.dictionary | throw (IO.userError "expected original dictionary")
  let frame := dictionary.frame
  unless (frame.header.start, frame.payload.start, frame.payload.stop) = span ∧
      frame.value.crc = some crc ∧ dictionary.entries.toList = entries ∧
      dictionary.codec.column = binding.codec.column ∧
      binding.column.metadata.dictionaryPageOffset = some (Int.ofNat frame.header.start) ∧
      binding.column.metadata.dataPageOffset = Int.ofNat frame.payload.stop ∧
      checked.pages.head?.map (·.frame.header.start) = some frame.payload.stop ∧
      rawChunkBytes checked.frames = rawBytes ∧ storedChunkBytes checked.frames = storedBytes do
    throw (IO.userError "dictionary wire anchors, contents or totals differ")

private def refuseCodec (file : Bytes) (expected : BindError) : IO Unit := do
  let source ← take (openFile {} file)
  deny expected (Chunk.bind source.schema 0)
"""


def inspect(wire, width, groups, codec):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow == BASE["schema_for"](NULLABLE, width)
    assert parquet.num_row_groups == len(groups)
    for key, meta, start, stop in V2["columns"](wire):
        group, column = key
        assert column == 0 and meta[4][1] == codec and meta[2][1][1] == [0, 3, 8]
        assert [name.decode() for name in meta[3][1][1]] == PATH
        assert parquet.read_row_group(group).column(0).to_pylist() == groups[group]
        expected = BASE["expected_slots"](groups[group], NULLABLE)
        assert meta[5][1] == len(expected)
        frames = original_frames(wire, key)
        cursor, pages, stored_total, raw_total = (0, 0, 0), [], 0, 0
        dictionary = None
        for ordinal, (at, header, payload, body) in enumerate(frames):
            kind = header[1][1]
            raw_size = header[2][1]
            end = payload + len(body)
            assert header[3][1] == len(body)
            crc = zlib.crc32(body)
            assert header[4][1] & 0xffffffff == crc
            stored_total += end - at
            raw_total += payload - at + raw_size
            if ordinal == 0:
                assert kind == 2 and at == start == meta[11][1] and end == meta[9][1]
                raw = expand(body, raw_size) if codec else body
                entries = [word for word, in struct.iter_unpack("<i" if width == 32 else "<q", raw)]
                assert len(raw) == raw_size and [header[7][1][tag][1] for tag in (1, 2)] == [len(entries), 0]
                assert len(entries) == len(set(entries))
                dictionary = at, payload, end, crc, entries
                continue
            slots, rows, live = before = cursor
            v2 = None
            if kind == 0:
                info = header[5][1]
                count, encoding = [info[tag][1] for tag in (1, 2)]
                assert [info[tag][1] for tag in (3, 4)] == [3, 3]
                raw = expand(body, raw_size) if codec else body
                assert len(raw) == raw_size
                reps, defs, _, suffix = section_suffix(raw, 2, 5, count)
            else:
                assert kind == 3
                info = header[8][1]
                count, nulls, row_count, encoding, dl, rl = [info[tag][1] for tag in range(1, 7)]
                reps, defs, suffix = sections_v2(info, body, 2, 5)
                flag = info.get(7, (TType.BOOL, True))[1]
                size = raw_size - dl - rl
                if codec and flag:
                    suffix = expand(suffix, size)
                assert len(suffix) == size
                live = 0
                v2 = count, nulls, row_count, dl, rl, flag
            present = defs.count(5)
            assert encoding in (0, 8) and len(reps) == len(defs) == count
            if encoding == 8:
                assert len(suffix) >= 1 and suffix[0] <= 32
                indices = HYBRID(suffix[1:], suffix[0], present)
                assert len(indices) == present and all(0 <= index < len(entries) for index in indices)
                words = [entries[index] for index in indices]
            else:
                words = [word for word, in struct.iter_unpack("<i" if width == 32 else "<q", suffix)]
                assert len(words) == present
            words = iter(words)
            events = [(r, d, next(words) if d == 5 else None) for r, d in zip(reps, defs, strict=True)]
            assert events == expected[slots:slots + count]
            for rep, definition, _ in events:
                reached = int(1 < definition) + int(3 < definition)
                assert 0 <= rep <= min(live, reached) and 0 <= definition <= 5
                live = reached
                rows += rep == 0
            cursor = slots + count, rows, 0 if v2 is not None else live
            pages.append(((at, payload, end, crc, before, cursor, events), v2, encoding))
        assert cursor[:2] == (len(expected), len(groups[group]))
        assert dictionary is not None and dictionary[2] == pages[0][0][0]
        assert pages[-1][0][2] == stop
        assert stored_total == meta[7][1] == stop - start and raw_total == meta[6][1]
        yield group, start, stop, cursor, dictionary, pages, raw_total


def varint(number):
    digits = []
    while number >= 128:
        digits.append(128 | (number & 127))
        number >>= 7
    return bytes(digits + [number])


def indexed_suffix(trace, entries):
    selected = [entries.index(value) for _, _, value in trace if value is not None]
    return b"\x08" + b"".join(bytes([2, index]) for index in selected)


def reframe(template, trace, entries, *, version, encoding):
    if version == 1:
        header, plain = header_body(BASE["CHUNK"]["frame"](template, trace, 32))
        _, _, levels, _ = section_suffix(plain, 2, 5, len(trace))
        header[5][1][2] = I32, encoding
    else:
        header, plain = header_body(BASE["v2_frame"](template, trace))
        info = header[8][1]
        levels = plain[:info[5][1] + info[6][1]]
        info[4] = I32, encoding
    body = levels + indexed_suffix(trace, entries) if encoding == 8 else plain
    return encode(header, body, len(body))


def fixtures():
    genuine, edited, positives = {}, {}, {}
    for width in (32, 64):
        rows = BASE["samples"](NULLABLE, width)
        rows[1][-1][0].extend([7, -9] * 96)
        rows.append([None, [], [None, [], [None]]])
        schema = BASE["schema_for"](NULLABLE, width)
        for codec in (0, 1):
            for version in (1, 2):
                label = f"native_{codec}_v{version}_{width}"
                genuine[label] = BASE["write"](schema, rows, compression="SNAPPY" if codec else "NONE",
                                                data_page_version=f"{version}.0", use_dictionary=True)
                positives[label] = width, rows, codec

    for codec in (0, 1):
        for version, width in ((1, 32), (2, 64)):
            label = f"fallback_{codec}_v{version}"
            rows = BASE["samples"](NULLABLE, width)
            rows[1] = [[[i + 100, -i - 3], [], None, [None]] for i in range(16)]
            genuine[label] = BASE["write"](BASE["schema_for"](NULLABLE, width), rows,
                                            compression="SNAPPY" if codec else "NONE",
                                            data_page_version=f"{version}.0", use_dictionary=True,
                                            dictionary_pagesize_limit=32)
            positives[label] = width, rows, codec

    identity = genuine["native_0_v1_32"]
    v2_template = raw_chunks(genuine["native_0_v2_32"])[GROUP][1]
    frames = raw_chunks(identity)[GROUP]
    v1_template = frames[1]
    _, _, _, _, dictionary, _, _ = list(inspect(identity, *positives["native_0_v1_32"][:2], 0))[1]
    entries = dictionary[-1]
    rows = positives["native_0_v1_32"][1]
    trace = BASE["expected_slots"](rows[1], NULLABLE)
    assert [rep for rep, _, _ in trace[:7]] == [0, 0, 1, 1, 1, 2, 0]
    last = max(i for i, (rep, _, _) in enumerate(trace) if rep == 0)
    sections = [trace[:3], trace[3:5], trace[5:6], trace[6:last], trace[last:]]
    versions, encodings = [1, 1, 1, 2, 1], [8, 0, 8, 8, 0]
    mixed = [frames[0]] + [reframe(v1_template if version == 1 else v2_template, segment, entries,
                                    version=version, encoding=encoding)
                           for version, encoding, segment in zip(versions, encodings, sections, strict=True)]

    # The first indexed page uses one index and seven ignored positions in
    # its final packed run. Padding does not cause a dictionary lookup.
    header, body = header_body(mixed[1])
    _, defs, packed_prefix, suffix = section_suffix(body, 2, 5, len(sections[0]))
    assert defs.count(5) == 1 and suffix[:2] == b"\x08\x02"
    padded = packed_prefix + b"\x08\x03" + suffix[2:3] + b"\xff" * 7
    mixed[1] = encode(header, padded, len(padded))

    def replace(wire, changed):
        return repack(wire, raw_chunks(wire) | {GROUP: changed})

    edited["mixed"] = replace(identity, mixed)
    positives["mixed"] = positives["native_0_v1_32"]
    changed = mixed.copy()
    changed[3] = reframe(v2_template, sections[2], entries, version=2, encoding=8)
    edited["v2_midrow"] = replace(identity, changed)
    first = (2, *sections[4][0][1:])
    changed = mixed.copy()
    changed[5] = reframe(v1_template, [first, *sections[4][1:]], entries, version=1, encoding=8)
    edited["after_v2"] = replace(identity, changed)

    snappy = genuine["native_1_v2_32"]
    frames = raw_chunks(snappy)[GROUP]
    header, stored = header_body(frames[-1])
    assert header[8][1][7][1]
    authored = SNAPPY["SNAPPY"]["raw_bypass"](header, stored)
    edited["snappy_raw_bypass"] = replace(snappy, frames[:-1] + [authored])
    positives["snappy_raw_bypass"] = positives["native_1_v2_32"]

    controls = [("v2_midrow", "mixed", 3, ".v2 (.v2RowBoundary 5 2)"),
                ("after_v2", "mixed", 5, f".level (.closedAncestor {last} 2 .closed)")]
    for version in (1, 2):
        label = f"native_1_v{version}_32"
        wire = genuine[label]
        frames = raw_chunks(wire)[GROUP]
        ordinal = len(frames) - 1
        header, stored = header_body(frames[ordinal])
        if version == 1:
            raw = expand(stored, header[2][1])
            count = header[5][1][1][1]
            _, defs, prefix, suffix = section_suffix(raw, 2, 5, count)
        else:
            info = header[8][1]
            _, defs, _ = sections_v2(info, stored, 2, 5)
            prefix = stored[:info[5][1] + info[6][1]]
            suffix = expand(stored[len(prefix):], header[2][1] - len(prefix))
            assert info[7][1]
        outside = b"\x08" + varint(defs.count(5) * 2) + b"\xff"
        for name, after, failure in (("late_index", outside, ".outOfBounds 255"),
                                     ("index_trailing", suffix + b"\0", ".hybrid .trailingBytes")):
            payload = compress(prefix + after) if version == 1 else prefix + compress(after)
            changed = encode(header, payload, len(prefix) + len(after))
            target = f"{name}_v{version}"
            edited[target] = replace(wire, frames[:ordinal] + [changed] + frames[ordinal+1:])
            controls.append((target, label, ordinal, f".dictionaryIndices ({failure})"))

    header, stored = header_body(frames[0])
    changed = stored[:-1] + bytes([stored[-1] ^ 1])
    crc = f".dictionary (.checksum (.mismatch {header[4][1] & 0xffffffff} {zlib.crc32(changed)}))"
    edited["late_dictionary_crc"] = replace(snappy, [encode(header, changed, header[2][1], crc=False)] + frames[1:])
    controls.append(("late_dictionary_crc", "native_1_v2_32", 0, crc))

    edited["duplicate_dictionary"] = replace(snappy, frames[:2] + frames[:1] + frames[2:])
    controls.append(("duplicate_dictionary", "native_1_v2_32", 2, ".dictionary .misplacedDictionary"))
    plain_wire = BASE["write"](BASE["schema_for"](NULLABLE, 32), rows)
    plain_frames = raw_chunks(plain_wire)[GROUP]
    plain_dictionary = raw_chunks(identity)[GROUP][0]
    edited["late_unadvertised_dictionary"] = replace(plain_wire,
                                                       plain_frames[:1] + [plain_dictionary] + plain_frames[1:])
    _, header, _, plain_body = original_frames(plain_wire)[0]
    count = header[5][1][1][1]
    reps, defs, _, _ = section_suffix(plain_body, 2, 5, count)
    plain_before = count, reps.count(0), int(1 < defs[-1]) + int(3 < defs[-1])
    footer = MIXED["metadata"](snappy)
    THRIFT["column_metadata"](footer, *GROUP).pop(11)
    edited["missing_dictionary_offset"] = repack(snappy, raw_chunks(snappy) | {GROUP: frames[1:]}, footer)
    controls.append(("missing_dictionary_offset", "native_1_v2_32", 0, ".dictionary .missingDictionary"))

    stripped = replace(snappy, frames[1:])
    footer = MIXED["metadata"](stripped)
    meta = THRIFT["column_metadata"](footer, *GROUP)
    meta[9] = I64, meta[9][1] + len(frames[1])
    edited["missing_dictionary_frame"] = SCHEMA["pack"](stripped, footer)
    controls.append(("missing_dictionary_frame", "native_1_v2_32", 0, ".dictionary .missingDictionary"))

    footer = MIXED["metadata"](snappy)
    meta = THRIFT["column_metadata"](footer, *GROUP)
    wrong = meta[9][1] + 1
    meta[9] = I64, wrong
    edited["wrong_data_offset"] = SCHEMA["pack"](snappy, footer)
    actual = wrong - 1
    controls.append(("wrong_data_offset", "native_1_v2_32", 1, f".dictionary (.dataOffset {wrong} {actual})"))

    footer = MIXED["metadata"](snappy)
    meta = THRIFT["column_metadata"](footer, *GROUP)
    meta[6] = I64, meta[6][1] + 1
    edited["raw_total"] = SCHEMA["pack"](snappy, footer)
    header, raw = header_body(raw_chunks(identity)[GROUP][0])
    edited["dictionary_word_extent"] = replace(identity, [encode(header, raw + b"\0", len(raw) + 1)] + raw_chunks(identity)[GROUP][1:])
    controls.append(("dictionary_word_extent", "native_0_v1_32", 0, ".dictionary (.plain .trailingBytes)"))

    wire = genuine["fallback_0_v1"]
    tail = raw_chunks(wire)[GROUP]
    header, raw = header_body(tail[-1])
    assert header[5][1][2][1] == 0
    edited["late_plain_tail"] = replace(wire, tail[:-1] + [encode(header, raw + b"\0", len(raw) + 1)])
    controls.append(("late_plain_tail", "fallback_0_v1", len(tail) - 1, ".plain .trailingBytes"))

    genuine["gzip_dictionary"] = BASE["write"](BASE["schema_for"](NULLABLE, 32), rows, compression="GZIP",
                                                use_dictionary=True)
    return genuine, edited, positives, controls, plain_before


def verify(scratch):
    genuine, edited, positives, controls, plain_before = fixtures()
    files = genuine | edited
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)
    code = [LEAN, *BASE["V1"]["ENTRY"]]
    observed, dictionaries, data_pages, empty = {}, 0, 0, 0
    for label, (width, rows, codec) in positives.items():
        wire = files[label]
        columns = list(inspect(wire, width, rows, codec))
        observed[label] = columns
        for group, lo, hi, end, dictionary, pages, raw_bytes in columns:
            at, payload, stop, crc, entries = dictionary
            terms = BASE["lst"](BASE["checked_page_term"]((page, v2), NULLABLE, width, encoding)
                                for page, v2, encoding in pages)
            position = BASE["state_term"](end)
            name = ".snappy" if codec else ".uncompressed"
            code.append(f'  checkChunk (← load folder "{label}") {group} [true, true, true] (1, 3, 5) '
                        f'.int{width} ⟨{lo}, {hi}⟩ {position} {terms} {name}')
            words = BASE["lst"](f"(.int{width} ({entry}))" for entry in entries)
            code.append(f'  checkDictionary (← load folder "{label}") {group} ({at}, {payload}, {stop}) {crc} '
                        f'{words} {raw_bytes} {hi-lo}')
            dictionaries += 1
            empty += not entries
            data_pages += len(pages)
            if group == GROUP[0] and label.startswith("fallback"):
                tags = [tag for _, _, tag in pages]
                assert set(tags) == {0, 8} and tags == sorted(tags, reverse=True)
            if group == GROUP[0] and label == "mixed":
                assert [page[-1][0][0] for page, _, _ in pages] == [0, 1, 2, 0, 0]
                assert [tag for _, _, tag in pages] == [8, 0, 8, 8, 0]
            if group == GROUP[0] and label == "snappy_raw_bypass":
                assert all(not v2[-1] for _, v2, _ in pages)
        fields, batches = IPC["observation"](wire, width)
        code.append(f'  checkFile folder "{label}" (← load folder "{label}") {fields} {batches}')
    assert empty > 0

    address = f"⟨1, 0, {json.dumps(PATH)}⟩"

    def page_error(label, reference, ordinal, cause, limits="{}", *, before=None):
        if before is None:
            pages = observed[reference][1][5]
            before = (0, 0, 0) if ordinal == 0 else pages[ordinal - 1][0][4]
        offset = original_frames(files[label])[ordinal][0]
        error = f'.page {address} {ordinal} {offset} {BASE["state_term"](before)} ({cause})'
        code.append(f'  refuse (← load folder "{label}") 1 {limits} ({error})')
        return error

    for label, reference, ordinal, cause in controls:
        before = (5, 2, 2) if label == "v2_midrow" else None
        error = page_error(label, reference, ordinal, cause, before=before)
        if label.startswith("late"):
            fields, batches = IPC["observation"](files[reference], 32, prefix=1)
            code.append(f'  sourceFailure (← load folder "{label}") {fields} {batches} '
                        f'(.group 1 (.chunk ({error})))')

    page_error("late_unadvertised_dictionary", None, 1, ".dictionary .misplacedDictionary", before=plain_before)

    v2 = "native_1_v2_32"
    _, lo, hi, _, _, pages, raw_total = observed[v2][1]
    _, header, _, body = original_frames(files[v2])[0]
    page_error(v2, v2, 0, f".dictionary (.dictionaryEntryLimit {header[7][1][1][1]})",
               "{ maxDictionaryEntries := 0 }")
    page_error(v2, v2, 0, f".dictionary (.dictionaryByteLimit {len(body)})", "{ maxDictionaryBytes := 0 }")
    v2_64 = "native_1_v2_64"
    _, header64, _, body64 = original_frames(files[v2_64])[0]
    assert len(body64) < header64[2][1]
    page_error(v2_64, v2_64, 0, f".dictionary (.dictionaryRawByteLimit {header64[2][1]})",
               f"{{ maxDictionaryBytes := {len(body64)} }}")
    page_error(v2, v2, 1, ".dictionaryIndices .indexByteLimit", "{ indices := { values := 1024, bytes := 0 } }")
    code.extend([
        f'  refuse (← load folder "{v2}") 1 {{ framing.maxPages := {len(pages)} }} '
        f'(.chunk {address} ⟨{lo}, {hi}⟩ (.framing .pageLimit))',
        f'  refuse (← load folder "raw_total") 1 {{}} (.chunk {address} ⟨{lo}, {hi}⟩ '
        f'(.uncompressedSize {raw_total + 1} {raw_total}))',
        f'  refuseCodec (← load folder "gzip_dictionary") (.column ⟨0, 0, {json.dumps(PATH)}⟩ (.codec 2))',
    ])

    V2["run_lean"](scratch, "TwoListDictionary.lean", code)
    emitted = BASE["readback"](scratch, {key: (NULLABLE, width, rows)
                                          for key, (width, rows, _) in positives.items()})
    for label, reference in (("mixed", "native_0_v1_32"), ("snappy_raw_bypass", "native_1_v2_32")):
        for selection in ("field", "empty"):
            assert emitted[f"{label}_{selection}"] == emitted[f"{reference}_{selection}"]
    print(f"Checked {dictionaries} dictionaries ({empty} empty), {data_pages} data frames, "
          f"{len(emitted)} IPC streams through exact EOS, and {len(controls) + 8} typed refusals")
    return {group: BASE["fingerprints"](items)
            for group, items in (("genuine", genuine), ("authored", edited), ("lean_ipc", emitted))}


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
