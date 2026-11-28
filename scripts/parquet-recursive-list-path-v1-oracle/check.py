"""Read native PyArrow LIST-path pages with Lean and compare original wire coordinates."""

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
CORE = runpy.run_path(str(HERE.parent / "parquet-recursive-list-path-oracle/check.py"))
TWO = CORE["TWO"]
V1, V2, FRAMES, lst, write, fingerprints = (CORE[k] for k in ("V1", "V2", "FRAMES", "lst", "write", "fingerprints"))
LEVEL, atom_term = CORE["LEVEL"], CORE["atom_term"]
schema_for, samples, levels = (CORE[k] for k in ("schema_for", "samples", "levels"))
metadata = TWO["MIXED"]["metadata"]
list_field = TWO["THRIFT"]["list_field"]
position = (1, 0)

LEAN = CORE["LEAN"].split("\nprivate def refuseRows", 1)[0].replace("module\n", """module

import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Defs
""", 1) + """
open RecursiveSchema.ListPath

private structure ExpectedPage where
  frame : Page.Frame
  sections : Chunk.Sections
  start : Chunk.State
  stop : Chunk.State
  atoms : List Atom

private structure ExpectedGroup where
  batch : Observation
  span : Footer.Span
  stop : Chunk.State
  pages : List ExpectedPage

private def checkNative (input : Bytes) (depth : Nat) (schema : Schema)
    (groups : List ExpectedGroup) : IO Unit := do
  let source ← take (openFile { maxSchemaDepth := 2 * depth + 2 } input)
  unless source.schema.plan.arrow == schema do throw (IO.userError "native Arrow schema differs")
  let actual ← take (Reader.readAll {} source.schema)
  unless actual == groups.map ExpectedGroup.batch do throw (IO.userError "native ordered row groups differ")
  for (expected, ordinal) in groups.zipIdx do
    let binding ← take (Chunk.bind source.schema ordinal)
    let original ← take (Chunk.read {} binding)
    unless binding.span = expected.span && original.stop = expected.stop &&
        original.pages.length = expected.pages.length do
      throw (IO.userError "native chunk span, counts or final state differ")
    for (found, page) in original.pages.zip expected.pages do
      unless found.frame = page.frame && found.decoded.sections = page.sections &&
          found.start = page.start && found.decoded.after = page.stop && found.decoded.atoms = page.atoms do
        throw (IO.userError "native frame, sections, cursor or slot trace differs")

private def refuse (input : Bytes) (ordinal : Nat) (limits : Chunk.Limits) (wanted : Chunk.Error) : IO Unit := do
  let source ← take (openFile {} input)
  let binding ← take (Chunk.bind source.schema ordinal)
  deny wanted (Chunk.read limits binding)

private def refuseBinding (input : Bytes) (wanted : Chunk.BindError) : IO Unit := do
  let source ← take (openFile {} input)
  deny wanted (Chunk.bind source.schema 0)

private def lateGroup (input : Bytes) (first : Observation) (wanted : Chunk.Error) : IO Unit := do
  let source ← take (openFile {} input)
  let original ← take (Reader.readGroup {} source.schema 0)
  unless original == first do throw (IO.userError "earlier original group differs")
  deny (.chunk wanted) (Reader.readAll {} source.schema)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
"""


def capture(wire, schema, nullable, width, groups, *, codecs=None, expand=None):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.equals(schema, check_metadata=True)
    assert parquet.num_row_groups == len(groups)
    row_groups = list_field(metadata(wire), 4)
    depth, maximum = len(nullable) - 1, len(nullable) - 1 + sum(nullable)
    stop_levels = [index + sum(nullable[:index + 1]) for index in range(depth)]
    path = ["chain"] + ["list", "element"] * depth
    manifest = []
    codecs = [0] * len(groups) if codecs is None else codecs
    assert len(codecs) == len(groups)
    for (group, column), footer, lo, hi in V2["columns"](wire):
        codec = codecs[group]
        assert column == 0 and footer[4][1] == codec and footer[9][1] == lo
        assert [name.decode() for name in list_field(footer, 3)] == path
        assert parquet.read_row_group(group).column(0).to_pylist() == groups[group]
        assert row_groups[group][3][1] == len(groups[group])
        slots, rows, live = 0, 0, 0
        expected = levels(groups[group], nullable)
        pages, stored, raw = [], 0, 0
        for header_at, header, body_at, body in FRAMES(wire, lo, hi):
            assert header[3][1] == len(body)
            crc = (header[4][1] & 0xffffffff) if 4 in header else None
            assert crc is None or crc == zlib.crc32(body)
            is_v2 = header[1][1] == 3
            start = (slots, rows, live)
            if is_v2:
                info = header[8][1]
                count, nulls, page_rows, encoding, dl, rl = (info[i][1] for i in range(1, 7))
                assert encoding == 0 and rl + dl <= len(body)
                reps = V2["HYBRID"](body[:rl], depth.bit_length(), count)
                defs = V2["HYBRID"](body[rl:rl + dl], maximum.bit_length(), count)
                suffix = body[rl + dl:]
                flag = info.get(7, (TType.BOOL, True))[1]
                assert rl + dl <= header[2][1]
                if codec != 0 and flag:
                    suffix = expand(codec, suffix, header[2][1] - rl - dl)
                assert rl + dl + len(suffix) == header[2][1]
                sections = body_at, body_at + rl, body_at + rl + dl, body_at + len(body)
                assert not reps or reps[0] == 0
                assert reps.count(0) == page_rows and len(defs) - defs.count(maximum) == nulls
                live = 0
            else:
                assert header[1][1] == 0
                count, *encodings = (header[5][1][i][1] for i in range(1, 5))
                assert encodings == [0, 3, 3]
                decoded = expand(codec, body, header[2][1]) if codec != 0 else body
                assert len(decoded) == header[2][1]
                reps, rest = LEVEL(decoded, depth, count)
                defs, suffix = LEVEL(rest, maximum, count)
                origin = 0 if codec != 0 else body_at
                sections = (origin, origin + len(decoded) - len(rest),
                            origin + len(decoded) - len(suffix), origin + len(decoded))
            assert len(reps) == len(defs) == count
            assert len(suffix) == defs.count(maximum) * (width // 8)
            signed = iter(word for word, in struct.iter_unpack("<i" if width == 32 else "<q", suffix))
            trace = [(rep, definition, next(signed) if definition == maximum else None)
                     for rep, definition in zip(reps, defs, strict=True)]
            assert trace == expected[slots:slots + count]
            for rep, definition, _ in trace:
                reached = sum(stop < definition for stop in stop_levels)
                assert rep <= min(live, reached) and 0 <= definition <= maximum
                rows += rep == 0
                live = reached
            slots += count
            if is_v2:
                live = 0
            stored += body_at - header_at + header[3][1]
            raw += body_at - header_at + header[2][1]
            pages.append((header_at, body_at, crc, len(body), sections, start, (slots, rows, live), trace))
        assert slots == footer[5][1] == len(expected) and rows == len(groups[group])
        assert stored == footer[7][1] == hi - lo and raw == footer[6][1]
        assert pages[0][0] == lo and pages[-1][1] + pages[-1][3] == hi
        manifest.append((lo, hi, (slots, rows, live), pages))
    assert len(manifest) == len(groups)
    return manifest


def triple(state):
    return "⟨" + ", ".join(map(str, state)) + "⟩"


def page_term(page, width, header=None, codec=0):
    at, body, crc, size, sections, start, stop, trace = page
    marker = "none" if crc is None else f"some {crc}"
    lo, p, q, hi = sections
    kind = f".dataV1 ⟨{len(trace)}, 0, 3, 3⟩"
    if header is not None and header[1][1] == 3:
        info = header[8][1]
        fields = ", ".join(str(info[i][1]) for i in range(1, 7))
        flag = str(info.get(7, (TType.BOOL, True))[1]).lower()
        kind = f".dataV2 ⟨{fields}, {flag}⟩"
    raw_size = header[2][1] if header is not None else size
    frame = f"⟨⟨{raw_size}, {size}, {marker}, {kind}⟩, ⟨{at}, {body}⟩, ⟨{body}, {body + size}⟩⟩"
    origin = ".decodedBody" if codec != 0 and kind.startswith(".dataV1") else ".file"
    spans = f"⟨⟨{lo}, {p}⟩, ⟨{p}, {q}⟩, ⟨{q}, {hi}⟩, {origin}⟩"
    return f"⟨{frame}, {spans}, {triple(start)}, {triple(stop)}, {lst(atom_term(slot, width) for slot in trace)}⟩"


def chunk(wire, target=position):
    return next((lo, hi) for key, _, lo, hi in V2["columns"](wire) if key == target)


def fixtures():
    genuine, positives, authored, genuine_controls = {}, {}, {}, {}
    for width, nullable in CORE["cases"]():
        depth = len(nullable) - 1
        bits = sum(1 << i for i, optional in enumerate(nullable) if optional)
        label = f"signed_{width}_depth_{depth}_{bits}"
        schema, groups = schema_for(nullable, width), samples(nullable, width)
        genuine[label] = write(schema, groups, max_rows_per_page=1)
        positives[label] = schema, nullable, width, groups
    schema, nullable, width, groups = positives["signed_32_depth_3_15"]
    source = genuine["signed_32_depth_3_15"]
    genuine["schema_only"] = write(schema, [])
    positives["schema_only"] = schema, nullable, width, []
    genuine["crc_absent"] = write(schema, groups, write_page_checksum=False)
    positives["crc_absent"] = schema, nullable, width, groups

    carrier = TWO["raw_chunks"](source)
    template = carrier[position][0]
    trace = levels(groups[1], nullable)
    cuts = [0]
    for repetition in (1, 2, 3):
        cuts.append(next(i for i in range(cuts[-1] + 1, len(trace)) if trace[i][0] == repetition))
    parts = [trace[lo:hi] for lo, hi in zip(cuts, cuts[1:] + [len(trace)], strict=True)]
    parts.append([])
    frames = [TWO["frame"](template, part, width) for part in parts]
    authored["deep_reframed"] = TWO["repack"](source, carrier | {position: frames})
    positives["deep_reframed"] = positives["signed_32_depth_3_15"]
    base = authored["deep_reframed"]
    lo, hi, end, pages = capture(base, schema, nullable, width, groups)[1]
    assert [page[-1][0][0] if page[-1] else None for page in pages] == [0, 1, 2, 3, None]
    assert pages[3][-2] == pages[4][-3] == pages[4][-2]
    address = "⟨1, 0, " + json.dumps(["chain", "list", "element", "list", "element", "list", "element"]) + "⟩"
    span = f"⟨{lo}, {hi}⟩"
    negatives = []

    def page_edit(label, ordinal, changed, cause, *, late=False):
        copy = frames.copy()
        copy[ordinal] = changed
        authored[label] = TWO["repack"](source, carrier | {position: copy})
        start = list(FRAMES(authored[label], *chunk(authored[label])))[ordinal][0]
        error = f".page {address} {ordinal} {start} {triple(pages[ordinal][-3])} ({cause})"
        negatives.append(f'  refuse (← load folder "{label}") 1 {{}} ({error})')
        if late:
            observation = CORE["ROWS"]["batch_term"](groups[0], width)
            negatives.append(f'  lateGroup (← load folder "{label}") {observation} ({error})')

    def edit_slot(label, part, change, cause):
        altered = [change, *parts[part][1:]]
        page_edit(label, part, TWO["frame"](template, altered, width), cause)

    slot = pages[2][-3][0]
    assert pages[2][-3][2] < 3 and parts[2][0][1] >= 4
    edit_slot("closed_deep_ancestor", 2, (3, *parts[2][0][1:]),
              f".level (.closedAncestor {slot} 3 {pages[2][-3][2]})")
    slot = pages[3][-3][0]
    assert pages[3][-3][2] == 3
    edit_slot("unreached_deep_ancestor", 3, (3, 0, None), f".level (.unreachedAncestor {slot} 3 0)")
    page_edit("late_words", 3, TWO["frame"](template, parts[3], width, extra_word=b"\0"),
              ".plain .trailingBytes", late=True)
    page_edit("rep_trailing", 3, TWO["frame"](template, parts[3], width, extra_rep=b"\x02\0"),
              ".repetition (.hybrid .trailingBytes)")
    header, body = TWO["header_body"](frames[3])
    long_length = struct.pack("<I", len(body) + 1) + body[4:]
    page_edit("rep_extent", 3, TWO["encode"](header, long_length),
              ".repetition (.section .truncatedDefinitions)")
    header, body = TWO["header_body"](frames[3])
    corrupted = body + b"\0"
    old_crc = header[4][1] & 0xffffffff
    page_edit("late_crc", 3, TWO["encode"](header, corrupted, crc=False),
              f".checksum (.mismatch {old_crc} {zlib.crc32(corrupted)})", late=True)
    header, body = TWO["header_body"](frames[3])
    header[2] = TType.I32, len(body) + 1
    page_edit("size_mismatch", 3, TWO["THRIFT"]["encode"](header) + body,
              f".header (.pageSizes {len(body) + 1} {len(body)})")

    def footer_edit(label, field, value):
        footer = metadata(base)
        col = TWO["THRIFT"]["column_metadata"](footer, *position)
        col[field] = TType.I64, value
        authored[label] = TWO["SCHEMA"]["pack"](base, footer)

    footer_edit("footer_raw", 6, hi - lo + 1)
    footer_edit("footer_stored", 7, hi - lo - 1)
    footer_edit("footer_slots", 5, end[0] + 1)
    footer_edit("slot_overrun", 5, end[0] - 1)
    footer_edit("footer_offset", 9, len(base))
    footer = metadata(base)
    original_group = list_field(footer, 4)[1]
    original_group[3] = TType.I64, end[1] + 1
    footer[3] = TType.I64, footer[3][1] + 1
    authored["footer_rows"] = TWO["SCHEMA"]["pack"](base, footer)
    for label, span_term, cause in (
        ("footer_raw", span, f".rawSize {hi - lo + 1} {hi - lo}"),
        ("footer_stored", f"⟨{lo}, {hi - 1}⟩", ".framing .payloadBounds"),
        ("footer_slots", span, f".slotCount {end[0] + 1} {end[0]}"),
        ("footer_rows", span, f".rowCount {end[1] + 1} {end[1]}"),
    ):
        negatives.append(f'  refuse (← load folder "{label}") 1 {{}} (.chunk {address} {span_term} ({cause}))')
    negatives.append(f'  refuse (← load folder "slot_overrun") 1 {{}} (.page {address} 3 {pages[3][0]} '
                     f'{triple(pages[3][-3])} (.slotOverrun {len(parts[3]) - 1} {len(parts[3])}))')
    negatives.append('  deny (.original (.snapshot (.invalidMetadata .pageInterval))) '
                     '(openFile {} (← load folder "footer_offset"))')
    for limit, cause in (("maxSlots", ".slotLimit"), ("maxRows", ".rowLimit"), ("maxChunkBytes", ".chunkLimit"),
                         ("framing.maxPages", "(.framing .pageLimit)")):
        negatives.append(f'  refuse (← load folder "deep_reframed") 1 {{ {limit} := 0 }} '
                         f'(.chunk {address} {span} {cause})')
    page_start = pages[0][0]
    negatives.append(f'  refuse (← load folder "deep_reframed") 1 {{ maxBodyBytes := 0 }} '
                     f'(.page {address} 0 {page_start} {{}} (.checksum .byteLimit))')

    original_address = address.replace("⟨1,", "⟨0,", 1)
    genuine_controls["brotli"] = write(schema, groups, compression="brotli")
    genuine_controls["indexed"] = write(schema, groups, write_page_index=True)
    genuine_controls["dictionary"] = write(schema, groups, use_dictionary=True)
    dictionary = next(V2["columns"](genuine_controls["dictionary"]))[1]
    for label, cause in (("brotli", "(.codec 4)"), ("indexed", ".pageIndex"),
                         ("dictionary", f"(.encodings {list_field(dictionary, 2)})")):
        negatives.append(f'  refuseBinding (← load folder "{label}") (.column {original_address} {cause})')

    wide = "signed_32_depth_4_10"
    wide_source = genuine[wide]
    wide_schema, wide_nullable, _, wide_groups = positives[wide]
    wide_pages = capture(wide_source, wide_schema, wide_nullable, 32, wide_groups)[0][-1]
    wide_carrier = TWO["raw_chunks"](wide_source)
    wide_path = json.dumps(["chain"] + ["list", "element"] * 4)
    for label, rep, definition, cause in (("rep_outside_plan", 5, 0, ".repetition 0 5 4"),
                                           ("def_outside_plan", 0, 7, ".definition 0 7 6")):
        original = wide_carrier[0, 0]
        changed = [(rep, definition, None), *wide_pages[0][-1][1:]]
        page = TWO["frame"](original[0], changed, 32)
        authored[label] = TWO["repack"](wide_source, wide_carrier | {(0, 0): [page, *original[1:]]})
        at = chunk(authored[label], (0, 0))[0]
        negatives.append(f'  refuse (← load folder "{label}") 0 {{}} '
                         f'(.page ⟨0, 0, {wide_path}⟩ 0 {at} {{}} (.level ({cause})))')

    return genuine, authored, genuine_controls, positives, negatives


def verify(folder):
    genuine, authored, genuine_controls, positives, negatives = fixtures()
    code = [LEAN, *V1["ENTRY"]]
    files = genuine | authored | genuine_controls
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)
    total_frames = 0
    batch_term = CORE["ROWS"]["batch_term"]
    for label, (decl, optional, bits, values) in positives.items():
        observed = capture(files[label], decl, optional, bits, values)
        depth = len(optional) - 1
        field = CORE["ROWS"]["field_term"](decl.field(0))
        groups_term = []
        for (start, end, cursor, original), batch in zip(observed, values, strict=True):
            terms = lst(page_term(page, bits) for page in original)
            groups_term.append(f"⟨{batch_term(batch, bits)}, ⟨{start}, {end}⟩, {triple(cursor)}, {terms}⟩")
            total_frames += len(original)
        code.append(f'  checkNative (← load folder "{label}") {depth} ⟨[{field}]⟩ {lst(groups_term)}')
        if depth <= 2:
            steps, traces, _ = CORE["inspect"](files[label], decl, optional, bits, values)
            expected = lst(f"({batch_term(batch, bits)}, {lst(atom_term(slot, bits) for slot in trace)})"
                           for batch, trace in zip(values, traces, strict=True))
            code.append(f'  checkFile (← load folder "{label}") {depth} ⟨[{field}]⟩ {lst(steps)} {expected}')
    V2["run_lean"](folder, "ListPathV1.lean", code + negatives)
    print(f"Checked {len(positives)} native files, {total_frames} original pages and {len(negatives)} typed controls")
    return {kind: fingerprints(items) for kind, items in {
        "genuine_parquet": genuine, "authored_parquet": authored, "genuine_controls": genuine_controls,
    }.items()}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for kind, expected in captured.items():
        assert expected == pins[kind], f"{kind} fixture pins changed"


if __name__ == "__main__":
    main()
