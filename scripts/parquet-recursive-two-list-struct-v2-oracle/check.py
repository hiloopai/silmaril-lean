"""Check both TwoListStruct columns across original V1 and V2 boundaries."""

from copy import deepcopy
from importlib.metadata import version
from itertools import product
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
ROOT = HERE.parents[1]
IPC = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-to-ipc-oracle/check.py"))
WRITER = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-writer-oracle/check.py"))
EVENTS, NATIVE = IPC["EVENTS"], WRITER["NATIVE"]
V2 = NATIVE["V2"]
FRAME = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-v2-oracle/check.py"))
v2_frame, header_body = FRAME["v2_frame"], FRAME["header_body"]
THRIFT, frames_in, raw_chunks, repack, lst, page_term, triple = (
    NATIVE[key] for key in ("THRIFT", "frames_in", "raw_chunks", "repack", "lst", "page_term", "triple")
)


LEAN = NATIVE["LEAN"].replace("module\n", """module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Defs
""", 1) + """
open Arrow.RecursiveSchema (Field)
open Arrow.RecursiveSchema.Stream.Events (declarations eraseBatch)
open Parquet.Reader.Recursive (Selection)
open Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc (convert)

private def checkDirect (input : Bytes) (fields : List (Option String × Field))
    (batches : List Observation) : IO Unit := do
  for selection in [Selection.field, .empty] do
    let ⟨source, trace⟩ ← take (Reader.Events.readProjected {} {} input selection)
    let expected := if selection = .field then fields else []
    unless declarations source == expected && trace.batches.map eraseBatch == batches.map selection.batch &&
        trace.termination == .eos do throw (IO.userError "native Events differ from the complete groups")
""" + IPC["LEAN"][IPC["LEAN"].index("private def checkIpc"):]


def empty_v2_group(wire):
    footer = NATIVE["metadata"](wire)
    groups = THRIFT["list_field"](footer, 4)
    empty = deepcopy(groups[0])
    empty[3] = TType.I64, 0
    groups.insert(1, empty)
    source = raw_chunks(wire)
    chunks = {}
    for side, width in enumerate(NATIVE["WIDTHS"]):
        THRIFT["column_metadata"](footer, 1, side)[5] = TType.I64, 0
        chunks[0, side] = source[0, side]
        chunks[1, side] = [v2_frame(source[0, side][0], [], width=width)]
        chunks[2, side] = source[1, side]
    return repack(wire, chunks, footer)


def fixtures():
    genuine = {}
    for optional in (False, True):
        prefix = "optional" if optional else "required"
        for flags in product((False, True), repeat=4):
            tag = "".join(str(int(flag)) for flag in flags)
            genuine[f"{prefix}_{tag}"] = NATIVE["native"](flags, struct_nullable=optional, data_page_version="2.0")

    schema, groups, wire = genuine["optional_1111"]
    previous = NATIVE["native"]((True,) * 4, struct_nullable=True)
    assert previous[:2] == (schema, groups)
    genuine["native_v1"] = previous
    genuine["schema_only"] = schema, [], NATIVE["write"](schema, [], data_page_version="2.0")
    _, renamed, named_rows, _ = next(case for case in WRITER["cases"](optional_element=True)
                                     if case[0] == "renamed_no_crc_empty_group")
    genuine["renamed_no_crc"] = renamed, named_rows[:1], NATIVE["write"](
        renamed, named_rows[:1], data_page_version="2.0", write_page_checksum=False, use_compliant_nested_type=False
    )

    carrier = raw_chunks(wire)
    v1 = raw_chunks(previous[2])
    trace = NATIVE["trace"]
    widths = NATIVE["WIDTHS"]
    optional = (True,) * 4
    rows = [[trace([row], optional, side, optional_element=True) for row in groups[1]] for side in (0, 1)]

    def newer(side, trace, **options):
        return v2_frame(carrier[1, side][0], trace, width=widths[side], **options)

    def older(side, trace):
        return NATIVE["frame"](v1[1, side][0], trace, widths[side])

    left, right = rows
    independent = ([
        newer(0, left[0], flag=None), newer(0, left[1] + left[2]),
    ], [
        newer(1, right[0] + right[1], flag=True), newer(1, right[2]),
    ])
    cuts = (2, len(groups[1][0][0]))
    first = left[0]
    assert [first[cut][0] for cut in cuts] == [2, 1]
    parts = [first[lo:hi] for lo, hi in zip((0, *cuts), (*cuts, len(first)), strict=True)]
    mixed = ([older(0, part) for part in parts] + [newer(0, left[1]), older(0, left[2])],
             [newer(1, right[0]), older(1, right[1]), newer(1, right[2])])

    def reframe(columns):
        return repack(wire, carrier | {(1, side): pages for side, pages in enumerate(columns)})

    empty = empty_v2_group(wire)
    authored = {"independent_v2": reframe(independent), "mixed_versions": reframe(mixed), "physical_empty": empty}
    positives = genuine | {"independent_v2": (schema, groups, authored["independent_v2"]),
                           "mixed_versions": (schema, groups, authored["mixed_versions"]),
                           "physical_empty": (schema, [groups[0], [], groups[1]], empty)}

    shared = NATIVE["steps"](optional)[2] + 1
    changed = next(i for i, atom in enumerate(right[2]) if atom[1] == shared and atom[2] is None)
    assert min(left[2][changed][1], shared) == shared
    rep = right[2][changed][0]
    slot = len(right[0]) + len(right[1]) + changed
    bad = right[2].copy()
    bad[changed] = rep, shared - 1, None
    damaged = authored["late_presence"] = reframe((independent[0], [independent[1][0], newer(1, bad)]))
    point = NATIVE["point"]
    presence = (f".topology (.conflict {slot} {point(damaged, 1, 0, slot)} {point(damaged, 1, 1, slot)} "
                f"({rep}, {shared}) ({rep}, {shared - 1}))")

    _, inspected = NATIVE["inspect"](authored["mixed_versions"], schema, groups, versions=(0, 3))
    refusals = []

    def patch(label, side, ordinal, changed, cause, *, chunk=False):
        pages = list(mixed)
        pages[side] = [*pages[side][:ordinal], changed, *pages[side][ordinal + 1:]]
        edited = authored[label] = reframe(pages)
        addr = NATIVE["address"](1, side)
        if chunk:
            span = next((lo, hi) for key, _, lo, hi in V2["columns"](edited) if key == (1, side))
            error = f".chunk (.chunk {addr} {triple(span)} ({cause}))"
        else:
            byte = frames_in(edited, 1, side)[ordinal][0]
            start = triple(inspected[1, side][1][ordinal][-3])
            error = f".chunk (.page {addr} {ordinal} {byte} {start} ({cause}))"
        refusals.append((label, error))

    for page, rep in ((1, 2), (2, 1)):
        slot = inspected[1, 0][1][page][-3][0]
        patch(f"v2_starts_rep_{rep}", 0, page, newer(0, parts[page]), f".v2 (.v2RowBoundary {slot} {rep})")
    for rep in (1, 2):
        early = [(rep, *right[1][0][1:]), *right[1][1:]]
        start = inspected[1, 1][1][1][-3]
        assert start[2] == 0
        patch(f"v1_after_v2_rep_{rep}", 1, 1, older(1, early), f".level (.closedAncestor {start[0]} {rep} 0)")

    late = right[2]
    nulls = sum(word is None for _, _, word in late)
    patch("late_rows", 1, 2, newer(1, late, mutation=(3, 1)), ".v2 (.v2Rows 2 1)")
    patch("late_nulls", 1, 2, newer(1, late, mutation=(2, 1)), f".v2 (.v2Nulls {nulls + 1} {nulls})")
    patch("late_lengths", 1, 2, newer(1, late, mutation=(5, 1000)),
          ".framing (.header .invalidV2Lengths)", chunk=True)
    patch("late_level_extent", 1, 2, newer(1, late, extra_rep=b"\x02\0"),
          ".v2 (.repetition (.hybrid .trailingBytes))")
    patch("late_words", 1, 2, newer(1, late, extra_word=b"\0"), ".plain .trailingBytes")
    broken = newer(1, late, extra_word=b"\0", crc=False)
    header, body = header_body(broken)
    given, actual = header[4][1] & 0xffffffff, zlib.crc32(body)
    assert given != actual
    patch("late_crc", 1, 2, broken, f".v2 (.checksum (.mismatch {given} {actual}))")

    controls = {}
    for label, options in (("compressed", {"compression": "snappy"}), ("dictionary", {"use_dictionary": True})):
        controls[label] = NATIVE["native"]((True,) * 4, struct_nullable=True, data_page_version="2.0", **options)[2]
    return genuine, authored, positives, controls, presence, refusals


def verify(folder):
    genuine, authored, positives, controls, presence, refusals = fixtures()
    sources = {label: case[2] for label, case in genuine.items()}
    for label, wire in (sources | authored | controls).items():
        (folder / f"{label}.parquet").write_bytes(wire)

    commands = [LEAN.replace("public def main ", "set_option maxHeartbeats 2000000 in\npublic def main ")]
    expected, v1_pages, v2_pages = {}, 0, 0
    for label, (schema, groups, wire) in positives.items():
        if label == "native_v1":
            versions = (0,)
        elif label == "mixed_versions":
            versions = (0, 3)
        else:
            versions = (3,)
        ceiling, columns = NATIVE["inspect"](wire, schema, groups, checksums=label != "renamed_no_crc",
                                             versions=versions)
        logical = EVENTS["pyarrow_groups"](wire, schema, groups)
        expected[label] = schema, logical
        outer = schema.field(0)
        inner = outer.type.value_field
        element = inner.type.value_field
        for (group, side), ((lo, hi), pages) in columns.items():
            headers = [header for _, header, _, _ in frames_in(wire, group, side)]
            if label.startswith(("required_", "optional_")):
                assert len(pages) > 1
            width = element.type[side].type.bit_width
            terms = lst(page_term(page, width, header) for page, header in zip(pages, headers, strict=True))
            tag = ".left" if side == 0 else ".right"
            path = [outer.name, "list", inner.name, "list", element.name, element.type[side].name]
            commands.append(f'  checkColumn (← load folder "{label}") {group} {tag} {NATIVE["path_term"](path)} '
                            f'{ceiling} ⟨{lo}, {hi}⟩ {terms}')
            v1_pages += sum(header[1][1] == 0 for header in headers)
            v2_pages += sum(header[1][1] == 3 for header in headers)
        fields, batches = IPC["fields_term"](schema), IPC["batches_term"](schema, logical)
        commands.extend([f'  checkRows (← load folder "{label}") {batches}',
                         f'  checkDirect (← load folder "{label}") {fields} {batches}',
                         f'  checkIpc folder "{label}" {fields} {batches}'])

    schema, logical = expected["optional_1111"]
    prefix = IPC["batches_term"](schema, logical[:1])
    commands.append(f'  inconsistent (← load folder "late_presence") 1 ({presence})')
    for label, error in [("late_presence", presence), *refusals]:
        commands.append(f'  groupRefusal (← load folder "{label}") 1 {{}} ({error})')
        commands.append(f'  sourceFailure (← load folder "{label}") {prefix} (.group 1 ({error}))')
    addr = NATIVE["address"](0, 0)
    commands.append(f'  groupRefusal (← load folder "compressed") 0 {{}} (.binding (.column {addr} (.codec 1)))')
    footer = THRIFT["column_metadata"](NATIVE["metadata"](controls["dictionary"]), 0, 0)
    encodings = lst(map(str, THRIFT["list_field"](footer, 2)))
    commands.append(f'  groupRefusal (← load folder "dictionary") 0 {{}} '
                    f'(.binding (.column {addr} (.encodings {encodings})))')
    for selection in ("field", "empty"):
        commands.append(f'  writerFailure (← load folder "physical_empty") .{selection} '
                        '{ schema.ipc.batches := 2 } (.batchLimit 3 2)')

    driver = folder / "TwoListStructV2.lean"
    driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
    subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                    "--run", str(driver), str(folder)], cwd=ROOT, check=True)
    ipc = {}
    for label, (schema, logical) in expected.items():
        for selection, projected in (("field", schema), ("empty", pa.schema([]))):
            name = f"{label}_{selection}"
            output = ipc[name] = (folder / f"{name}.arrow").read_bytes()
            IPC["inspect_ipc"](output, projected, logical)
    for selection in ("field", "empty"):
        want = ipc[f"optional_1111_{selection}"]
        for label in ("native_v1", "independent_v2", "mixed_versions"):
            assert ipc[f"{label}_{selection}"] == want
    print(f"Checked {len(positives)} accepted sources, {v1_pages} original V1 and {v2_pages} original V2 pages, "
          f"{len(ipc)} exact IPC streams and {len(refusals) + 5} typed controls")
    pins = NATIVE["fingerprints"]
    return {key: pins(data) for key, data in {
        "genuine_parquet": sources, "authored_parquet": authored, "genuine_refusals": controls, "lean_ipc": ipc,
    }.items()}


def producer():
    assert platform.python_implementation() == "CPython"
    return {"cpython": platform.python_version(), "pyarrow": pa.__version__, "thrift": version("thrift")}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert producer() == pins["producer"]
    with tempfile.TemporaryDirectory() as directory:
        assert verify(Path(directory)) == {key: data for key, data in pins.items() if key != "producer"}


if __name__ == "__main__":
    main()
