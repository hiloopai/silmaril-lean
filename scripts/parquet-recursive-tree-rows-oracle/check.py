"""Check the generic native row join against PyArrow and original addressed leaf pages."""

from collections import Counter
import json
from pathlib import Path
import runpy
import struct
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
COMPILER = runpy.run_path(str(HERE.parent / "parquet-recursive-tree-compiler-oracle/check.py"))
NATIVE, V2 = COMPILER["NATIVE"], COMPILER["V2"]
FRAMES, LEVEL, THRIFT, lst, page_term = (
    COMPILER[key] for key in ("FRAMES", "LEVEL", "THRIFT", "lst", "page_term")
)
PATHS, DEPTHS, DEFINITIONS, WIDTHS = (
    COMPILER[key] for key in ("PATHS", "DEPTHS", "DEFINITIONS", "WIDTHS")
)
FRAME = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-v2-oracle/check.py"))
RUNNER = COMPILER["LEAN"].split("public def main", 1)[0].replace("module\n", """module

import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Defs
""", 1) + """
open Arrow.RecursiveSchema.Batch.Rows (Observation)
open RecursiveSchema.Tree.Occurrences (Addressed)

private def checkGroup (file : Bytes) (group : Nat) (expected : Observation)
    (slots : List (List Addressed)) : IO Unit := do
  let source ← take (openFile {} file)
  let result ← take (Rows.readGroupChecked source.schema {} group)
  unless result.observation == expected && result.inputs.map (·.tape.slots.toList) == slots do
    throw (IO.userError s!"joined group {group} differs from the original rows or addressed slots")

private def refuseGroup (file : Bytes) (group : Nat) (limits : Rows.Limits) (expected : Rows.Error) : IO Unit := do
  let source ← take (openFile {} file)
  refuse (Rows.readGroup source.schema limits group) expected

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture directory")
"""


def trace_map(groups):
    return {(group, side): list(COMPILER["expected_trace"](rows, side))
            for group, rows in enumerate(groups) for side in range(len(PATHS))}


def independent_roots():
    deep = pa.list_(pa.field("element", pa.list_(pa.field(
        "element", pa.list_(pa.field("element", pa.int32())), nullable=False))))
    other = pa.list_(pa.field("element", pa.int64(), nullable=False))
    schema = pa.schema([pa.field("deep", deep, nullable=False), pa.field("other", other)])
    groups = [
        [([], [1, 2, 3]), ([None, [], [[None, -1], [], [2, 3]]], None)],
        [([[[4, None, 7]]], []), ([[], None, [[8]]], [-2**63, 2**63 - 1])],
    ]
    layout = (
        (("deep", "list", "element", "list", "element", "list", "element"), 3, 5, 32, (0, 2, 3)),
        (("other", "list", "element"), 1, 2, 64, (1,)),
    )

    def trace(value, nullable, rep=0, definition=0, depth=0):
        if value is None:
            assert nullable[0]
            yield rep, definition, None
        elif len(nullable) == 1:
            yield rep, definition + nullable[0], value
        elif not value:
            yield rep, definition + nullable[0], None
        else:
            for i, child in enumerate(value):
                yield from trace(child, nullable[1:], rep if i == 0 else depth + 1,
                                 definition + nullable[0] + 1, depth + 1)

    expected = {(group, side): [slot for row in rows for slot in trace(row[side], flags)]
                for group, rows in enumerate(groups)
                for side, flags in enumerate(((False, True, False, True), (True, False)))}
    rows = [[dict(zip(schema.names, row, strict=True)) for row in group] for group in groups]
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, compression="NONE", use_dictionary=False, data_page_version="2.0",
                          store_schema=False, write_page_checksum=True, data_page_size=64,
                          write_batch_size=1, max_rows_per_page=1) as writer:
        for group in rows:
            writer.write_table(pa.Table.from_pylist(group, schema=schema))
    wire = sink.getvalue().to_pybytes()
    return schema, rows, layout, expected, wire


def create():
    schema, original, _, compiler_files = COMPILER["create"]()
    genuine = {name: compiler_files[name] for name in ("branch_v1", "branch_v2")}
    positives = {name: original for name in genuine}
    # End the second group with a two-occurrence row so the short leaf's
    # missing occurrence is reached at the original end of its chunk.
    groups = [original[0], [original[1][0], [], *original[1][1:2]]]
    v1 = NATIVE["write"](schema, groups, data_page_version="1.0", max_rows_per_page=1)
    v2 = NATIVE["write"](schema, groups, data_page_version="2.0", max_rows_per_page=1)
    raw = NATIVE["raw_chunks"](v1)
    v2_raw = NATIVE["raw_chunks"](v2)
    expected = trace_map(groups)

    def repack(changes, cuts, versions=None):
        metadata = NATIVE["metadata"](v1)
        chunks = raw.copy()
        for key, atoms in changes.items():
            _, side = key
            points = cuts[key]
            segments = [atoms[lo:hi] for lo, hi in zip([0, *points], [*points, len(atoms)], strict=True)]
            chunks[key] = []
            for i, part in enumerate(segments):
                use_v2 = versions is not None and versions.get((key, i), 1) == 2
                assert part
                if use_v2:
                    assert part[0][0] == 0
                    page = FRAME["v2_frame"](v2_raw[key][0], part, width=WIDTHS[side], flag=False)
                else:
                    page = NATIVE["frame"](raw[key][0], part, WIDTHS[side])
                chunks[key].append(page)
            THRIFT["column_metadata"](metadata, *key)[5] = TType.I64, len(atoms)
        return NATIVE["repack"](v1, chunks, metadata)

    edited = {key: atoms for key, atoms in expected.items() if key[0] == 1}
    # The b stream cuts at a rep-2 continuation. The a stream cuts at a
    # different occurrence, and c begins with a complete V2 row range.
    cuts = {(1, 0): [1, 4], (1, 1): [2, 4, 6], (1, 2): [4]}
    assert [edited[1, 0][point][0] for point in cuts[1, 0]] == [1, 0]
    assert [edited[1, 1][point][0] for point in cuts[1, 1]] == [2, 1, 0]
    assert edited[1, 2][4][0] == 0
    independent = repack(edited, cuts, {((1, 2), 0): 2})
    positives["independent_mixed"] = groups
    started_last = {key: max(i for i, (rep, _, _) in enumerate(atoms) if rep == 0)
                    for key, atoms in edited.items()}
    # Exchange present and null Struct markers at consecutive elements.
    # The reader must choose the earlier disagreement.
    changed_slot = 1
    a = edited[1, 0]
    assert a[changed_slot:changed_slot + 2] == [(1, 3, None), (1, 2, None)]
    presence = a.copy()
    presence[changed_slot:changed_slot + 2] = [(1, 2, None), (1, 3, None)]
    presence_map = expected | {(1, 0): presence}
    # The final outer occurrence is missing from column a. The other
    # columns still contain it even though b and c have different lengths.
    assert len(a) == started_last[1, 0] + 2 and a[-1][0] == 1
    short_map = expected | {(1, 0): a[:-1]}
    # Remove an occurrence before the group end as a second boundary
    # case. Column a's following row start carries the absence address.
    short_mid = a[:2] + a[3:]
    assert a[2] == (1, 2, None) and short_mid[2][0] == 0
    short_mid_map = expected | {(1, 0): short_mid}
    authored = {
        "independent_mixed": independent,
        "late_presence": repack(edited | {(1, 0): presence}, cuts),
        "late_end_cardinality": repack(edited | {(1, 0): a[:-1]}, cuts),
        "late_row_cardinality": repack(edited | {(1, 0): short_mid}, cuts),
    }
    controls = {name: compiler_files[name] for name in ("leading_struct", "unsupported_double")}
    return schema, genuine, authored, controls, positives, {
        "late_presence": presence_map,
        "late_end_cardinality": short_map,
        "late_row_cardinality": short_mid_map,
    }, changed_slot


BRANCH_LAYOUT = tuple(zip(PATHS, DEPTHS, DEFINITIONS, WIDTHS, ((1,), (1, 4), (1, 3)), strict=True))


def inspect(wire, expected, layout=BRANCH_LAYOUT):
    retained, counts = {}, Counter()
    for key, meta, lo, hi in V2["columns"](wire):
        group, side = key
        path, depth, maximum, width, stops = layout[side]
        assert meta[4][1] == 0 and meta[9][1] == lo
        assert [piece.decode() for piece in THRIFT["list_field"](meta, 3)] == list(path)
        points, pages = [], []
        slots = rows = live = 0
        for page, (at, header, body_at, body) in enumerate(FRAMES(wire, lo, hi)):
            version = header[1][1]
            count = header[8 if version == 3 else 5][1][1][1]
            crc = header[4][1] & 0xffffffff
            assert crc == zlib.crc32(body)
            assert header[2][1] == header[3][1] == len(body)
            if version == 0:
                reps, after_reps = LEVEL(body, depth, count)
                defs, suffix = LEVEL(after_reps, maximum, count)
                rep_end = len(body) - len(after_reps)
                def_end = len(body) - len(suffix)
            else:
                assert version == 3
                info = header[8][1]
                rep_end = info[6][1]
                def_end = rep_end + info[5][1]
                reps = V2["HYBRID"](body[:rep_end], depth.bit_length(), count)
                defs = V2["HYBRID"](body[rep_end:def_end], maximum.bit_length(), count)
                suffix = body[def_end:]
                assert (not reps or reps[0] == 0) and reps.count(0) == info[3][1]
                assert count - defs.count(maximum) == info[2][1]
                live = 0
            start = slots, rows, live
            sections = body_at, body_at + rep_end, body_at + def_end, body_at + len(body)
            values = [word for word, in struct.iter_unpack("<i" if width == 32 else "<q", suffix)]
            assert len(values) == defs.count(maximum)
            words = iter(values)
            trace = [(rep, definition, next(words) if definition == maximum else None)
                     for rep, definition in zip(reps, defs, strict=True)]
            assert trace == expected[key][slots:slots + count]
            for index, (rep, definition, word) in enumerate(trace, slots):
                reached = sum(stop < definition for stop in stops)
                assert rep <= min(live, reached)
                rows += rep == 0
                live = reached
                points.append((page, at, index, rep, definition, word))
            if version == 3:
                live = 0
            slots += count
            pages.append(page_term((at, body_at, crc, len(body), sections, start, (slots, rows, live), trace), width, header))
            counts[version] += 1
        assert slots == meta[5][1] == len(expected[key])
        assert hi - lo == meta[6][1] == meta[7][1]
        assert rows == sum(rep == 0 for rep, _, _ in expected[key])
        retained[key] = ((lo, hi), pages, points)
    assert retained.keys() == expected.keys()
    return retained, counts


def address(group, side, layout):
    return f"⟨{group}, {side}, {json.dumps(layout[side][0])}⟩"


def point(group, side, page, at, slot, layout=BRANCH_LAYOUT):
    return f"⟨{address(group, side, layout)}, {page}, {at}, {slot}⟩"


def signed(width, word):
    return "none" if word is None else f"some (.int{width} ({word}))"


def addressed(group, side, points, layout=BRANCH_LAYOUT):
    return lst(f"⟨{point(group, side, page, at, slot, layout)}, ⟨{rep}, {df}, {signed(layout[side][3], word)}⟩⟩"
               for page, at, slot, rep, df, word in points)


def verify(folder, genuine, authored, controls, schema, positives, invalid, changed_slot):
    lines = [RUNNER]
    totals = Counter()
    for label, wire in (genuine | authored | controls).items():
        (folder / f"{label}.parquet").write_bytes(wire)
        if label in controls:
            continue
        carrier = f'(← load folder "{label}")'
        groups = positives.get(label)
        if groups is not None:
            parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
            assert parquet.schema_arrow.equals(schema, check_metadata=True)
            rows = [parquet.read_row_group(g).column(0).to_pylist() for g in range(parquet.num_row_groups)]
            assert rows == groups
            expected = trace_map(rows)
        else:
            expected = invalid[label]
        checked, counts = inspect(wire, expected)
        totals.update(counts)
        for (group, side), ((lo, hi), pages, _) in checked.items():
            lines.append(f'  checkLeaf {carrier} {group} {side} ⟨{lo}, {hi}⟩ {json.dumps(PATHS[side])} {lst(pages)}')

        admitted = groups if groups is not None else positives["independent_mixed"][:1]
        for group, rows in enumerate(admitted):
            observation = NATIVE["expected_observation"](schema, [{"items": row} for row in rows])
            slots = lst(addressed(group, side, checked[group, side][2]) for side in range(len(PATHS)))
            lines.append(f"  checkGroup {carrier} {group} {observation} {slots}")

        if groups is None:
            group = 1
            wrapper = COMPILER["location"](2, COMPILER["WRAPPER"])
            site = COMPILER["location"](1, COMPILER["OUTER"])
            struct_site = COMPILER["location"](3, COMPILER["ELEMENT"])
            def boundary(side, slot):
                return f".slot {point(group, side, *checked[group, side][2][slot][:3])}"

            if label == "late_presence":
                position = f"⟨0, [({wrapper}, 1)]⟩"
                b = next(i for i, value in enumerate(expected[1, 1]) if value[0] == 1)
                error = f".presence {position} {struct_site} ({boundary(0, changed_slot)}) ({boundary(1, b)}) .null .present"
            else:
                if label == "late_end_cardinality":
                    position = f"⟨2, [({wrapper}, 1)]⟩"
                    present = max(i for i, value in enumerate(expected[1, 1]) if value[0] == 1)
                    (lo, hi), pages, slots = checked[1, 0]
                    absent = f".end {point(1, 0, len(pages), hi, len(slots))}"
                else:
                    position = f"⟨0, [({wrapper}, 2)]⟩"
                    present = [i for i, value in enumerate(expected[1, 1]) if value[0] == 1][1]
                    absent = boundary(0, 2)
                error = f".cardinality {position} (some {site}) ({boundary(1, present)}) ({absent})"
            lines.append(f"  refuseGroup {carrier} {group} {{}} (.join ({error}))")

    extra_schema, extra_groups, layout, expected, wire = independent_roots()
    (folder / "independent_roots_v2.parquet").write_bytes(wire)
    carrier = '(← load folder "independent_roots_v2")'
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.equals(extra_schema, check_metadata=True)
    assert [parquet.read_row_group(g).to_pylist() for g in range(parquet.num_row_groups)] == extra_groups
    checked, counts = inspect(wire, expected, layout)
    totals.update(counts)
    for (group, side), ((lo, hi), pages, _) in checked.items():
        lines.append(f'  checkLeaf {carrier} {group} {side} ⟨{lo}, {hi}⟩ {json.dumps(layout[side][0])} {lst(pages)}')
    for group, rows in enumerate(extra_groups):
        observation = NATIVE["expected_observation"](extra_schema, rows)
        slots = lst(addressed(group, side, checked[group, side][2], layout) for side in range(len(layout)))
        lines.append(f"  checkGroup {carrier} {group} {observation} {slots}")

    lines.extend([
        '  refuseGroup (← load folder "branch_v1") 0 { maxColumns := 2 } (.input (.columnLimit 0 3))',
        '  refuseGroup (← load folder "branch_v1") 0 { maxSlots := 25 } (.input (.slotLimit 0 26))',
        '  refuseGroup (← load folder "branch_v1") 0 { chunk := { maxRows := 2 } } (.input (.rowLimit 0 3))',
        '  refuseGroup (← load folder "branch_v1") 2 {} (.input (.group 2))',
        '  refuseGroup (← load folder "leading_struct") 0 {} (.input (.leaf 0 (.representation 0)))',
        '  refuse (openFile {} (← load folder "unsupported_double"))',
        '    (.original (.physical ⟨4, ["items", "list", "element", "a"]⟩ .double))',
    ])
    V2["run_lean"](folder, "RecursiveTreeRows.lean", lines)
    print(f"Checked {len(positives) + 1} accepted branching carriers, {totals[0]} V1 and {totals[3]} V2 original pages, "
          "and nine typed refusal controls")


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert pins["producer"] == COMPILER["BASE"]["producer"]()
    schema, genuine, authored, controls, positives, invalid, changed_slot = create()
    fingerprints = NATIVE["fingerprints"]
    assert pins["genuine_parquet"] == fingerprints(genuine | controls | {"independent_roots_v2": independent_roots()[-1]})
    assert pins["authored_parquet"] == fingerprints(authored)
    with tempfile.TemporaryDirectory() as scratch:
        verify(Path(scratch), genuine, authored, controls, schema, positives, invalid, changed_slot)


if __name__ == "__main__":
    main()
