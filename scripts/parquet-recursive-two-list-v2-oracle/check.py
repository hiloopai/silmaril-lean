"""Inspect original two-LIST V1/V2 frames and read Lean IPC through exact EOS."""

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
CHUNK = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-oracle/check.py"))
IPC = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-to-ipc-oracle/check.py"))
(
    V1, V2, THRIFT, MIXED, FRAMES, SCHEMA, PATH, fingerprints, lst, raw_chunks, header_body,
    repack, encode, samples, schema_for, write, thresholds, expected_slots, state_term, page_term,
) = (CHUNK[name] for name in (
    "V1", "V2", "THRIFT", "MIXED", "FRAMES", "SCHEMA", "PATH", "fingerprints", "lst", "raw_chunks",
    "header_body", "repack", "encode", "samples", "schema_for", "write", "thresholds", "expected_slots",
    "state_term", "page_term",
))
GROUP = (1, 0)

# Keep the original frame-and-cursor comparison and add the V2 header and
# raw-section span comparison to each expected page.
CHUNK_CHECKS = CHUNK["LEAN"].split("private structure ExpectedPage", 1)[1].split(
    "private def refuseBind", 1
)[0]
LEAN = IPC["LEAN"] + """
open Silmaril.Formats.Parquet
open RecursiveSchema.TwoList
open RecursiveSchema.TwoList.Chunk

set_option maxHeartbeats 2000000

private def v2Header (frame : Page.Frame) : Option (Page.DataV2 × Page.V2Spans) := do
  let .dataV2 info := frame.value.kind | none
  return (info, ← frame.v2Spans)

private structure ExpectedPage""" + CHUNK_CHECKS.replace(
    "  words : List (Option Word)", "  words : List (Option Word)\n  v2 : Option (Page.DataV2 × Page.V2Spans)"
).replace(
    "(pages : List ExpectedPage) : IO Unit",
    "(pages : List ExpectedPage) (codec : Codec := .uncompressed) : IO Unit",
).replace(
    "unless observed.stop = stop",
    "unless binding.codec = codec ∧ observed.stop = stop",
).replace(
    "page.decoded.words = expected.words do",
    "page.decoded.words = expected.words ∧ v2Header frame = expected.v2 do",
)


def inspect(wire, nullable, width, groups, *, codecs=None, expand=None):
    """Read the original Compact headers, counted levels, and exact signed suffix."""
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.equals(schema_for(nullable, width))
    assert parquet.num_row_groups == len(groups)
    codecs = [0] * len(groups) if codecs is None else codecs
    assert len(codecs) == len(groups)
    outer, inner, maximum = thresholds(nullable)
    for (group, column), metadata, start, stop in V2["columns"](wire):
        codec = codecs[group]
        assert column == 0 and metadata[4][1] == codec and metadata[9][1] == start
        assert [name.decode() for name in metadata[3][1][1]] == PATH
        assert parquet.read_row_group(group).column(0).to_pylist() == groups[group]
        expected = expected_slots(groups[group], nullable)
        assert metadata[5][1] == len(expected)
        cursor, pages, stored_total, raw_total = (0, 0, 0), [], 0, 0
        for at, header, payload, body in FRAMES(wire, start, stop):
            crc = zlib.crc32(body)
            assert header[3][1] == len(body)
            assert header[4][1] & 0xffffffff == crc
            stored_total += payload - at + header[3][1]
            raw_total += payload - at + header[2][1]
            slots, rows, live = before = cursor
            tag = header[1][1]
            v2 = None
            if tag == 3:
                info = header[8][1]
                count, nulls, row_count, encoding, dl, rl = [info[i][1] for i in range(1, 7)]
                assert encoding == 0 and rl + dl <= len(body)
                reps = V2["HYBRID"](body[:rl], 2, count)
                defs = V2["HYBRID"](body[rl:rl + dl], maximum.bit_length(), count)
                suffix = body[rl + dl:]
                flag = info.get(7, (TType.BOOL, True))[1]
                extent = header[2][1] - rl - dl
                if codec != 0 and flag:
                    suffix = expand(codec, suffix, extent)
                assert len(suffix) == extent
                assert not reps or reps[0] == 0
                assert reps.count(0) == row_count and len(defs) - defs.count(maximum) == nulls
                v2 = (count, nulls, row_count, dl, rl, flag)
                live = 0
            else:
                assert tag == 0
                info = header[5][1]
                count = info[1][1]
                assert [info[i][1] for i in (2, 3, 4)] == [0, 3, 3]
                decoded = expand(codec, body, header[2][1]) if codec != 0 else body
                assert len(decoded) == header[2][1]
                reps, rest = CHUNK["CHUNK"]["level_section"](decoded, 2, count)
                defs, suffix = CHUNK["CHUNK"]["level_section"](rest, maximum, count)

            assert len(reps) == len(defs) == count
            assert len(suffix) == defs.count(maximum) * (width // 8)
            words = iter(word for word, in struct.iter_unpack("<i" if width == 32 else "<q", suffix))
            trace = [(rep, definition, next(words) if definition == maximum else None)
                     for rep, definition in zip(reps, defs, strict=True)]
            assert trace == expected[slots:slots + count]
            for rep, definition, _ in trace:
                reached = int(outer < definition) + int(inner < definition)
                assert rep <= min(live, reached) and 0 <= definition <= maximum
                live = reached
                rows += rep == 0
            cursor = slots + count, rows, 0 if v2 is not None else live
            pages.append(((at, payload, payload + len(body), crc, before, cursor, trace), v2))
        assert cursor[:2] == (len(expected), len(groups[group]))
        assert pages[0][0][0] == start and pages[-1][0][2] == stop
        assert stored_total == metadata[7][1] == stop - start and raw_total == metadata[6][1]
        yield group, start, stop, cursor, pages


def checked_page_term(page, nullable, width, encoding=0):
    original, data_v2 = page
    expected = page_term(original, nullable, width)
    v2 = "none"
    if data_v2 is not None:
        count, nulls, rows, dl, rl, compressed = data_v2
        _, payload, end, *_ = original
        rep_end, def_end = payload + rl, payload + rl + dl
        v2 = (f"some (⟨{count}, {nulls}, {rows}, {encoding}, {dl}, {rl}, {str(compressed).lower()}⟩, "
              f"⟨⟨{payload}, {rep_end}⟩, ⟨{rep_end}, {def_end}⟩, ⟨{def_end}, {end}⟩⟩)")
    return f"{expected[:-1]}, {v2}⟩"


def v2_frame(template, trace, *, flag=False, mutation=None, extra_rep=b"", extra_word=b"", crc=True):
    header, _ = header_body(template)
    reps = b"".join(bytes([2, rep]) for rep, _, _ in trace) + extra_rep
    defs = b"".join(bytes([2, definition]) for _, definition, _ in trace)
    words = b"".join(struct.pack("<i", word) for _, _, word in trace if word is not None) + extra_word
    values = [len(trace), sum(word is None for _, _, word in trace), sum(rep == 0 for rep, _, _ in trace),
              0, len(defs), len(reps)]
    info = {field: (TType.I32, value) for field, value in enumerate(values, 1)}
    if flag is not None:
        info[7] = TType.BOOL, flag
    if mutation is not None:
        field, delta = mutation
        info[field] = TType.I32, values[field - 1] + delta
    header[8] = TType.STRUCT, info
    return encode(header, reps + defs + words, crc=crc)


def fixtures():
    genuine, authored, positives, refusals = {}, {}, {}, []
    for width in (32, 64):
        for bits in range(8):
            nullable = tuple(bool(bits & (1 << bit)) for bit in range(3))
            groups = samples(nullable, width)
            label = f"native_{width}_{bits}"
            genuine[label] = write(schema_for(nullable, width), groups, data_page_version="2.0")
            positives[label] = nullable, width, groups

    nullable, width, groups = positives["native_32_7"]
    source = genuine["native_32_7"]
    genuine["native_v1"] = write(schema_for(nullable, width), groups)
    raw = raw_chunks(source)
    old_template = raw_chunks(genuine["native_v1"])[GROUP][0]
    new_template = raw[GROUP][0]
    trace = expected_slots(groups[1], nullable)
    assert [rep for rep, _, _ in trace[:7]] == [0, 0, 1, 1, 1, 2, 0]
    last_row = max(i for i, (rep, _, _) in enumerate(trace) if rep == 0)
    segments = [trace[:3], trace[3:5], trace[5:6], trace[6:last_row], trace[last_row:]]
    v1_frame = CHUNK["frame"]
    mixed = [v1_frame(old_template, segment, width) for segment in segments[:3]]
    mixed.extend([v2_frame(new_template, segments[3]), v1_frame(old_template, segments[4], width)])
    authored["mixed"] = repack(source, raw | {GROUP: mixed})
    positives["mixed"] = nullable, width, groups
    flag_pages = [v2_frame(new_template, trace[:6], flag=True), v2_frame(new_template, trace[6:], flag=None)]
    authored["identity_flags"] = repack(source, raw | {GROUP: flag_pages})
    positives["identity_flags"] = nullable, width, groups

    def patch(label, ordinal, changed, before, cause):
        pages = mixed[:ordinal] + [changed] + mixed[ordinal + 1:]
        authored[label] = repack(source, raw | {GROUP: pages})
        refusals.append((label, ordinal, before, cause))

    for ordinal, rep in ((1, 1), (2, 2)):
        before = (3, 2, 1) if rep == 1 else (5, 2, 2)
        patch(f"v2_starts_rep_{rep}", ordinal, v2_frame(new_template, segments[ordinal]), before,
              f".v2 (.v2RowBoundary {before[0]} {rep})")
    for rep in (1, 2):
        first = (rep, *segments[4][0][1:])
        changed = v1_frame(old_template, [first, *segments[4][1:]], width)
        patch(f"v1_after_v2_rep_{rep}", 4, changed, (last_row, len(groups[1]) - 1, 0),
              f".level (.closedAncestor {last_row} {rep} .closed)")

    suffix = segments[3]
    before = (6, 2, 2)
    nulls = sum(word is None for _, _, word in suffix)
    patch("late_rows", 3, v2_frame(new_template, suffix, mutation=(3, 1)), before, ".v2 (.v2Rows 2 1)")
    patch("late_nulls", 3, v2_frame(new_template, suffix, mutation=(2, 1)), before,
          f".v2 (.v2Nulls {nulls + 1} {nulls})")
    available = len(trace) - before[0]
    patch("slot_overrun", 3, v2_frame(new_template, suffix, mutation=(1, available - len(suffix) + 1)), before,
          f".v2 (.slotOverrun {available} {available + 1})")
    invalid_span = mixed[:3] + [v2_frame(new_template, suffix, mutation=(5, 1000))] + mixed[4:]
    authored["level_span"] = repack(source, raw | {GROUP: invalid_span})
    patch("trailing_level", 3, v2_frame(new_template, suffix, extra_rep=b"\x02\0"), before,
          ".v2 (.repetition (.hybrid .trailingBytes))")
    patch("late_suffix", 3, v2_frame(new_template, suffix, extra_word=b"\0"), before, ".plain .trailingBytes")
    corrupt_crc = v2_frame(new_template, suffix, extra_word=b"\0", crc=False)
    header, body = header_body(corrupt_crc)
    patch("late_crc", 3, corrupt_crc, before,
          f".v2 (.checksum (.mismatch {header[4][1] & 0xffffffff} {zlib.crc32(body)}))")
    header, body = header_body(v2_frame(new_template, suffix, flag=True))
    header[2] = TType.I32, len(body) + 1
    patch("page_sizes", 3, THRIFT["encode"](header) + body, before,
          f".v2 (.header (.pageSizes {len(body) + 1} {len(body)}))")
    for label, field in (("footer_raw_total", 6), ("footer_stored_total", 7), ("footer_offset", 9)):
        footer = MIXED["metadata"](authored["mixed"])
        metadata = THRIFT["column_metadata"](footer, *GROUP)
        delta = -1 if label == "footer_stored_total" else 1
        if label == "footer_offset":
            delta = len(authored["mixed"])
        metadata[field] = TType.I64, metadata[field][1] + delta
        authored[label] = SCHEMA["pack"](authored["mixed"], footer)
    return genuine, authored, positives, refusals


def chunk_span(wire, position):
    return next((start, stop) for key, _, start, stop in V2["columns"](wire) if key == position)


def verify(scratch):
    genuine, authored, positives, refusals = fixtures()
    files = genuine | authored
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)

    code = [LEAN, *V1["ENTRY"]]
    total = 0
    for label, (nullable, width, groups) in positives.items():
        fields, batches = IPC["observation"](files[label], width)
        for group, lo, hi, end, pages in inspect(files[label], nullable, width, groups):
            opts = lst(str(value).lower() for value in nullable)
            outer, inner, end_def = thresholds(nullable)
            terms = lst(checked_page_term(page, nullable, width) for page in pages)
            code.append(f'  checkChunk (← load folder "{label}") {group} {opts} ({outer}, {inner}, {end_def}) '
                        f'.int{width} ⟨{lo}, {hi}⟩ {state_term(end)} {terms}')
            if label.startswith("native"):
                assert len(pages) >= 2 and all(page[1] is not None and not page[1][-1] for page in pages)
            elif label == "mixed" and group == 1:
                assert [page[0][-1][0][0] for page in pages] == [0, 1, 2, 0, 0]
                assert [page[1] is not None for page in pages] == [False, False, False, True, False]
            elif label == "identity_flags" and group == 1:
                assert all(page[1][-1] for page in pages)
            total += len(pages)
        code.append(f'  checkFile folder "{label}" (← load folder "{label}") {fields} {batches}')

    fields, batches = IPC["observation"](genuine["native_32_7"], 32, prefix=1)
    address = f"⟨1, 0, {json.dumps(PATH)}⟩"
    for label, ordinal, before, cause in refusals:
        lo, hi = chunk_span(files[label], GROUP)
        at, *_ = list(FRAMES(files[label], lo, hi))[ordinal]
        page_error = f".page {address} {ordinal} {at} {state_term(before)} ({cause})"
        code.append(f'  refuse (← load folder "{label}") 1 {{}} ({page_error})')
        if label.startswith("late"):
            code.append(f'  sourceFailure (← load folder "{label}") {fields} {batches} '
                        f'(.group 1 (.chunk ({page_error})))')

    lo, hi = chunk_span(files["mixed"], GROUP)
    span_lo, span_hi = chunk_span(files["level_span"], GROUP)
    code.extend([
        f'  refuse (← load folder "level_span") 1 {{}} '
        f'(.chunk {address} ⟨{span_lo}, {span_hi}⟩ (.framing (.header .invalidV2Lengths)))',
        f'  refuse (← load folder "footer_raw_total") 1 {{}} '
        f'(.chunk {address} ⟨{lo}, {hi}⟩ (.uncompressedSize {hi - lo + 1} {hi - lo}))',
        f'  refuse (← load folder "footer_stored_total") 1 {{}} '
        f'(.chunk {address} ⟨{lo}, {hi - 1}⟩ (.uncompressedSize {hi - lo} {hi - lo - 1}))',
        '  deny (.snapshot (.invalidMetadata .pageInterval)) (openFile {} (← load folder "footer_offset"))',
        f'  refuse (← load folder "mixed") 1 {{ framing.maxPages := 4 }} '
        f'(.chunk {address} ⟨{lo}, {hi}⟩ (.framing .pageLimit))',
        f'  refuse (← load folder "native_32_7") 1 {{ maxBodyBytes := 0 }} '
        f'(.page {address} 0 {chunk_span(files["native_32_7"], GROUP)[0]} {{}} (.v2 (.checksum .byteLimit)))',
    ])
    V2["run_lean"](scratch, "TwoListV2.lean", code)

    emitted = readback(scratch, positives)
    for label in ("mixed", "identity_flags"):
        for selection in ("field", "empty"):
            assert emitted[f"{label}_{selection}"] == emitted[f"native_32_7_{selection}"]
    print(f"Checked {total} original frames, {len(emitted)} native IPC streams through exact EOS, "
          f"and {len(refusals) + 6} typed refusals")
    return {"genuine": fingerprints(genuine), "authored": fingerprints(authored), "lean_ipc": fingerprints(emitted)}


def readback(scratch, positives):
    emitted = {}
    stream = IPC["STREAM"]
    for label, (nullable, width, groups) in positives.items():
        for selection in ("field", "empty"):
            name = f"{label}_{selection}"
            wire = (scratch / f"{name}.arrow").read_bytes()
            reader = pa.ipc.open_stream(wire)
            assert reader.schema == (schema_for(nullable, width) if selection == "field" else pa.schema([]))
            batches = list(reader)
            assert [batch.num_rows for batch in batches] == list(map(len, groups))
            rows = [[{"series": row} for row in group] if selection == "field" else [{}] * len(group)
                    for group in groups]
            assert [batch.to_pylist() for batch in batches] == rows
            _, offset = stream["metadata"](wire)
            for count in map(len, groups):
                frame = stream["read_record"](wire, offset)
                assert frame.rows == count
                offset = frame.end
            assert wire[offset:] == stream["EOS"]
            emitted[name] = wire
    return emitted


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
