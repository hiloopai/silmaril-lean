"""Verify native LIST-path V2 and mixed Parquet through Lean Events and IPC."""

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
IPC = runpy.run_path(str(HERE.parent / "parquet-recursive-list-path-to-ipc-oracle/check.py"))
NATIVE, RAW = IPC["NATIVE"], IPC["RAW"]
V1, V2, FRAMES, lst, write, fingerprints = (NATIVE[k] for k in ("V1", "V2", "FRAMES", "lst", "write", "fingerprints"))
capture, chunk, levels, schema_for, samples, page_term, triple, metadata = (
    NATIVE[key] for key in ("capture", "chunk", "levels", "schema_for", "samples", "page_term", "triple", "metadata")
)
EVENTS, TWO = IPC["EVENTS"], NATIVE["TWO"]
TWOV2 = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-v2-oracle/check.py"))
v2_frame = TWOV2["v2_frame"]
raw_chunks, v1_frame, repack, header_body, encode = (
    TWO[key] for key in ("raw_chunks", "frame", "repack", "header_body", "encode")
)
GROUP = (1, 0)


LEAN = NATIVE["LEAN"].replace("module\n", """module

import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Defs
""", 1) + """
open Silmaril Silmaril.Formats
open Silmaril.Formats.Arrow.RecursiveSchema (Field)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events (Value declarations eraseBatch)
open Parquet.Reader.Recursive (Selection)
open Parquet.RecursiveSchema.ListPath.Reader.ToIpc (convert)

private def compareTwoList (input : Bytes) : IO Unit := do
  let generic ← take (openFile {} input)
  let previous ← take (RecursiveSchema.TwoList.openFile {} input)
  let genericRows ← take (Reader.readAll {} generic.schema)
  let previousRows ← take (RecursiveSchema.TwoList.Rows.readAll {} previous.schema)
  unless generic.schema.plan.arrow == RecursiveSchema.TwoList.Rows.arrowSchema previous.schema.plan &&
      genericRows == previousRows do throw (IO.userError "depth-two schema or groups differ")
  for ordinal in List.range generic.snapshot.groupCount do
    let found ← take (Chunk.read {} (← take (Chunk.bind generic.schema ordinal)))
    let earlier ← take (RecursiveSchema.TwoList.Chunk.read {} (← take
      (RecursiveSchema.TwoList.Chunk.bind previous.schema ordinal)))
    let expected := (RecursiveSchema.TwoList.Rows.atoms earlier.pages).map fun atom =>
      ({ repetition := atom.repetition, definition := atom.definition, word := atom.word } : Atom)
    unless found.atoms = expected do throw (IO.userError "depth-two atoms differ")
""" + "private def selected" + IPC["LEAN"].split("private def selected", 1)[1].split("private def openFailure", 1)[0]


def fixtures():
    genuine, positive, authored, controls = {}, {}, {}, {}
    for width in (32, 64):
        for depth in (1, 2, 3, 4, 6, 16):
            nullable = (True,) * (depth + 1) if depth <= 3 else tuple(
                (i + (width == 32)) % 2 == 0 for i in range(depth + 1))
            schema, rows = schema_for(nullable, width), samples(nullable, width)
            if depth == 3 and width == 32:
                # A live V2 row followed by an empty row in the mixed reframe.
                rows[1] = [rows[1][0], rows[1][2], rows[1][1]]
            label = f"native_{width}_depth_{depth}"
            crc = depth != 6
            genuine[label] = write(schema, rows, data_page_version="2.0", write_page_checksum=crc,
                                   max_rows_per_page=1)
            positive[label] = schema, nullable, width, rows

        nullable = (False,) * 4
        schema, rows = schema_for(nullable, width), samples(nullable, width)
        label = f"native_{width}_depth_3_required"
        genuine[label] = write(schema, rows, data_page_version="2.0", max_rows_per_page=1)
        positive[label] = schema, nullable, width, rows

    source_label = "native_32_depth_3"
    schema, nullable, width, groups = positive[source_label]
    genuine["schema_only"] = write(schema, [], data_page_version="2.0")
    positive["schema_only"] = schema, nullable, width, []
    original = genuine[source_label]
    old = write(schema, groups, max_rows_per_page=1)
    genuine["native_v1"] = old
    positive["native_v1"] = positive[source_label]

    carrier = raw_chunks(original)
    v1_template, v2_template = raw_chunks(old)[GROUP][0], carrier[GROUP][0]
    row1, row2, row3 = [levels([row], nullable) for row in groups[1]]
    cuts = [0]
    for repetition in (1, 2, 3):
        cuts.append(next(i for i in range(cuts[-1] + 1, len(row1)) if row1[i][0] == repetition))
    pieces = [row1[lo:hi] for lo, hi in zip(cuts, cuts[1:] + [len(row1)], strict=True)]
    empty_v2 = v2_frame(v2_template, [])
    mixed = [v1_frame(v1_template, trace, width) for trace in pieces]
    mixed += [v2_frame(v2_template, row2, flag=True), v1_frame(v1_template, row3, width), empty_v2]
    authored["mixed"] = repack(original, carrier | {GROUP: mixed})
    positive["mixed"] = positive[source_label]
    authored["omitted_flag"] = repack(original, carrier | {GROUP: [
        v2_frame(v2_template, row1, flag=None), v2_frame(v2_template, row2), v2_frame(v2_template, row3)
    ]})
    positive["omitted_flag"] = positive[source_label]

    lo, hi, end, pages = capture(authored["mixed"], *positive["mixed"])[1]
    address = f'⟨1, 0, {json.dumps(["chain"] + ["list", "element"] * 3)}⟩'
    refusals = []

    def refuse_page(label, ordinal, start, cause):
        at = list(FRAMES(authored[label], *chunk(authored[label])))[ordinal][0]
        error = f".page {address} {ordinal} {at} {triple(start)} ({cause})"
        refusals.append((label, error))

    def patch(label, ordinal, frame, cause):
        replacements = mixed[:ordinal] + [frame] + mixed[ordinal + 1:]
        authored[label] = repack(original, carrier | {GROUP: replacements})
        refuse_page(label, ordinal, pages[ordinal][-3], cause)

    for ordinal, rep in enumerate((1, 2, 3), 1):
        slot = pages[ordinal][-3][0]
        assert pages[ordinal][-3][2] >= rep
        patch(f"v2_starts_inside_{rep}", ordinal, v2_frame(v2_template, pieces[ordinal]),
              f".v2 (.v2RowBoundary {slot} {rep})")
    slot = pages[5][-3][0]
    for rep in (1, 2, 3):
        trace = [(rep, *row3[0][1:]), *row3[1:]]
        patch(f"v1_continues_v2_{rep}", 5, v1_frame(v1_template, trace, width),
              f".level (.closedAncestor {slot} {rep} 0)")
    slot, rows, live = pages[1][-3]
    assert live >= 1
    authored["v1_continues_empty_v2"] = repack(original, carrier | {GROUP: mixed[:1] + [empty_v2] + mixed[1:]})
    refuse_page("v1_continues_empty_v2", 2, (slot, rows, 0), f".level (.closedAncestor {slot} 1 0)")

    nulls = sum(word is None for _, _, word in row2)
    patch("late_row_count", 4, v2_frame(v2_template, row2, mutation=(3, 1)), ".v2 (.v2Rows 2 1)")
    patch("late_null_count", 4, v2_frame(v2_template, row2, mutation=(2, 1)), f".v2 (.v2Nulls {nulls + 1} {nulls})")
    patch("slot_overrun", 6, v2_frame(v2_template, [], mutation=(1, 1)), ".v2 (.slotOverrun 0 1)")
    patch("trailing_level", 4, v2_frame(v2_template, row2, extra_rep=b"\x02\0"),
          ".v2 (.repetition (.hybrid .trailingBytes))")
    patch("late_signed_extent", 4, v2_frame(v2_template, row2, extra_word=b"\0"), ".plain .trailingBytes")
    bad_crc = v2_frame(v2_template, row2, extra_word=b"\0", crc=False)
    header, body = header_body(bad_crc)
    patch("late_crc", 4, bad_crc, f".v2 (.checksum (.mismatch {header[4][1] & 0xffffffff} {zlib.crc32(body)}))")
    header, body = header_body(mixed[4])
    header[8][1][4] = TType.I32, 8
    patch("bad_encoding", 4, encode(header, body), ".dictionary .missingDictionary")
    header, body = header_body(mixed[4])
    header[2] = TType.I32, len(body) + 1
    patch("size_mismatch", 4, TWO["THRIFT"]["encode"](header) + body,
          f".v2 (.header (.pageSizes {len(body) + 1} {len(body)}))")

    bad = v2_frame(v2_template, row2, mutation=(5, 1000))
    authored["level_span"] = repack(original, carrier | {GROUP: mixed[:4] + [bad] + mixed[5:]})
    span = triple(chunk(authored["level_span"]))
    refusals.append(("level_span", f".chunk {address} {span} (.framing (.header .invalidV2Lengths))"))
    footer = metadata(authored["mixed"])
    TWO["THRIFT"]["column_metadata"](footer, *GROUP)[6] = TType.I64, hi - lo + 1
    authored["raw_total"] = TWO["SCHEMA"]["pack"](authored["mixed"], footer)
    refusals.append(("raw_total", f".chunk {address} ⟨{lo}, {hi}⟩ (.rawSize {hi - lo + 1} {hi - lo})"))
    assert end[0] == sum(map(len, (row1, row2, row3)))

    controls["compressed"] = write(schema, groups, data_page_version="2.0", compression="brotli")
    controls["dictionary"] = write(schema, groups, data_page_version="2.0", use_dictionary=True)
    return genuine, positive, authored, controls, refusals


def inspect_ipc(wire, schema, groups, selection):
    expected_schema = schema if selection == "field" else pa.schema([])
    reader = pa.ipc.open_stream(wire)
    assert reader.schema.equals(expected_schema, check_metadata=True)
    fields, cursor = RAW["raw_schema"](wire)
    assert fields == [RAW["STREAM"]["SCHEMA"]["pyarrow_field"](pa, field) for field in expected_schema]
    for group, batch in zip(groups, reader, strict=True):
        record = RAW["read_record"](wire, cursor)
        expected = [group] if selection == "field" else []
        assert record.rows == batch.num_rows == len(group) and RAW["columns"](pa, batch) == expected
        RAW["check_record"](pa, expected_schema, record, expected)
        cursor = record.end
    assert cursor + 8 == len(wire) and wire[cursor:] == RAW["eos"]


def verify(folder):
    genuine, positive, authored, controls, refusals = fixtures()
    files = genuine | authored | controls
    for label, wire in files.items():
        (folder / f"{label}.parquet").write_bytes(wire)
    code = [LEAN, *V1["ENTRY"]]
    total_frames = 0
    terms = NATIVE["CORE"]["ROWS"]
    for label, (schema, nullable, width, groups) in positive.items():
        wire = files[label]
        frames = []
        for (lo, hi, stop, pages), group in zip(capture(wire, schema, nullable, width, groups), groups, strict=True):
            headers = [header for _, header, _, _ in FRAMES(wire, lo, hi)]
            if label.startswith("native_") and label != "native_v1":
                assert len(pages) >= 2 and all(header[1][1] == 3 for header in headers)
                assert all(header[8][1][7][1] is False for header in headers)
            page_terms = lst(page_term(page, width, header) for page, header in zip(pages, headers, strict=True))
            frames.append(f"⟨{terms['batch_term'](group, width)}, ⟨{lo}, {hi}⟩, {triple(stop)}, {page_terms}⟩")
            total_frames += len(pages)
        depth = len(nullable) - 1
        field = terms["field_term"](schema.field(0))
        code.append(f'  checkNative (← load folder "{label}") {depth} ⟨[{field}]⟩ {lst(frames)}')
        if depth == 2:
            code.append(f'  compareTwoList (← load folder "{label}")')
        code.append(f'  checkIpc folder "{label}" (← load folder "{label}") {depth} '
                    f'{EVENTS["declarations"](schema)} {EVENTS["batch_terms"](groups, width)}')

    schema, _, width, groups = positive["native_32_depth_3"]
    for label, error in refusals:
        code.append(f'  refuse (← load folder "{label}") 1 {{}} ({error})')
        if label.startswith("late_"):
            code.append(f'  sourceFailure (← load folder "{label}") {EVENTS["declarations"](schema)} '
                        f'{EVENTS["batch_terms"](groups[:1], width)} (.group 1 (.chunk ({error})))')
    address = f'⟨0, 0, {json.dumps(["chain"] + ["list", "element"] * 3)}⟩'
    code.append(f'  refuseBinding (← load folder "compressed") (.column {address} (.codec 4))')
    dict_groups = []
    dictionary = controls["dictionary"]
    nullable = positive["native_32_depth_3"][1]
    for (lo, hi, stop, pages), group in zip(
            capture(dictionary, schema, nullable, width, groups, dictionaries={}), groups, strict=True):
        headers = [header for _, header, _, _ in FRAMES(dictionary, lo, hi)][1:]
        expected = lst(page_term(page, width, header) for page, header in zip(pages, headers, strict=True))
        dict_groups.append(f"⟨{terms['batch_term'](group, width)}, ⟨{lo}, {hi}⟩, {triple(stop)}, {expected}⟩")
        total_frames += len(pages)
    code.append(f'  checkNative (← load folder "dictionary") 3 ⟨[{terms["field_term"](schema.field(0))}]⟩ '
                f'{lst(dict_groups)}')
    V2["run_lean"](folder, "ListPathV2.lean", code)

    emitted = {}
    for label, (schema, _, _, groups) in positive.items():
        for selection in ("field", "empty"):
            name = f"{label}_{selection}"
            wire = emitted[name] = (folder / f"{name}.arrow").read_bytes()
            inspect_ipc(wire, schema, groups, selection)
    for selection in ("field", "empty"):
        for label in ("mixed", "omitted_flag", "native_v1"):
            assert emitted[f"{label}_{selection}"] == emitted[f"native_32_depth_3_{selection}"]
    print(f"Checked {len(positive) + 1} native inputs, {total_frames} original pages, {len(emitted)} IPC streams "
          f"through exact EOS, and {len(refusals) + 1} typed controls")
    return {kind: fingerprints(values) for kind, values in {
        "genuine_parquet": genuine, "authored_parquet": authored, "genuine_controls": controls, "lean_ipc": emitted,
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
