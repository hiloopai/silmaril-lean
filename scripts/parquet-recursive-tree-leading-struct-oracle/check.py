"""Check original signed paths with leading Structs through native rows, Events and IPC."""

from collections import Counter
import json
from pathlib import Path
import runpy
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
EVENTS = runpy.run_path(str(HERE.parent / "parquet-recursive-tree-events-oracle/check.py"))
IPC = runpy.run_path(str(HERE.parent / "parquet-recursive-tree-to-ipc-oracle/check.py"))
JOIN, NATIVE, V2, THRIFT, lst = (EVENTS[key] for key in ("JOIN", "NATIVE", "V2", "THRIFT", "lst"))
LAYOUT = (
    (("bundle", "west", "list", "reading"), 1, 4, 32, (2,)),
    (("bundle", "east", "list", "segment", "list", "sample"), 2, 5, 64, (1, 3)),
    (("marks", "list", "marker"), 1, 1, 32, (0,)),
)


def expected_trace(row, side):
    bundle = row["bundle"]
    if side == 2:
        marks = row["marks"]
        if not marks:
            yield 0, 0, None
        else:
            for i, mark in enumerate(marks):
                yield int(i > 0), 1, mark
    elif bundle is None:
        yield 0, 0, None
    elif side == 0:
        west = bundle["west"]
        if west is None:
            yield 0, 1, None
        elif not west:
            yield 0, 2, None
        else:
            for i, reading in enumerate(west):
                yield int(i > 0), 4 - int(reading is None), reading
    else:
        east = bundle["east"]
        if not east:
            yield 0, 1, None
        for i, segment in enumerate(east):
            outer_rep = int(i > 0)
            if segment is None:
                yield outer_rep, 2, None
            elif not segment:
                yield outer_rep, 3, None
            else:
                for j, sample in enumerate(segment):
                    yield 2 if j > 0 else outer_rep, 5 - int(sample is None), sample


def traces(groups):
    return {(group, side): [atom for row in rows for atom in expected_trace(row, side)]
            for group, rows in enumerate(groups) for side in range(len(LAYOUT))}


def create():
    west = pa.list_(pa.field("reading", pa.int32()))
    inner = pa.list_(pa.field("sample", pa.int64()))
    east = pa.list_(pa.field("segment", inner))
    bundle = pa.struct([pa.field("west", west), pa.field("east", east, nullable=False)])
    marks = pa.list_(pa.field("marker", pa.int32(), nullable=False))
    schema = pa.schema([pa.field("bundle", bundle), pa.field("marks", marks, nullable=False)])

    def row(west, east, marks):
        return {"bundle": {"west": west, "east": east}, "marks": marks}

    groups = [
        [{"bundle": None, "marks": []}, row(None, [], [1, 2]), row([], [None, [], [None, -2**63, 7]], [3]),
         row([-2**31, None, 2**31 - 1], [[2**63 - 1], []], [])],
        [row(None, [], [9]), row([-7, None, 11], [[10, None, 13], [15], [20, None]], [8, 7]),
         {"bundle": None, "marks": [3]}, row([], [None], [])],
    ]

    def make(version):
        sink = pa.BufferOutputStream()
        with pq.ParquetWriter(sink, schema, compression="NONE", use_dictionary=False, data_page_version=version,
                              store_schema=False, use_compliant_nested_type=False, write_page_checksum=True,
                              data_page_size=64, max_rows_per_page=1, write_batch_size=1) as writer:
            for group in groups:
                writer.write_table(pa.Table.from_pylist(group, schema=schema))
        return sink.getvalue().to_pybytes()

    genuine = {f"leading_v{version}": make(f"{version}.0") for version in (1, 2)}
    old, new = genuine["leading_v1"], genuine["leading_v2"]
    raw = NATIVE["raw_chunks"](old)
    v2 = NATIVE["raw_chunks"](new)
    expected = traces(groups)
    west_atoms, east_atoms = expected[1, 0], expected[1, 1]
    assert [west_atoms[i][0] for i in (2, 4)] == [1, 0]
    assert [east_atoms[i][0] for i in (3, 5, 7)] == [2, 1, 0]

    def reframe(west):
        changed = raw.copy()
        changed[1, 0] = [NATIVE["frame"](raw[1, 0][0], west[lo:hi], 32)
                         for lo, hi in ((0, 2), (2, 4), (4, len(west)))]
        changed[1, 1] = [NATIVE["frame"](raw[1, 1][0], east_atoms[lo:hi], 64)
                         for lo, hi in ((0, 3), (3, 5), (5, 7))]
        changed[1, 1].append(JOIN["FRAME"]["v2_frame"](v2[1, 1][0], east_atoms[7:], width=64, flag=False))
        return NATIVE["repack"](old, changed)

    assert west_atoms[:3] == [(0, 1, None), (0, 4, -7), (1, 3, None)]
    presence = [(0, 0, None), *west_atoms[1:]]
    unreached = [*west_atoms[:2], (1, 2, None), *west_atoms[3:]]
    authored = {"independent_cuts": reframe(west_atoms), "late_presence": reframe(presence),
                "late_unreached": reframe(unreached)}
    return schema, groups, genuine, authored, expected | {(1, 0): presence}


def source_errors(authored, presence_wire):
    group = 1
    left = JOIN["point"](group, 0, *presence_wire[group, 0][2][0][:3], LAYOUT)
    right = JOIN["point"](group, 1, *presence_wire[group, 1][2][0][:3], LAYOUT)
    site = '⟨1, ["bundle"]⟩'
    presence = f".group {group} (.join (.presence ⟨0, []⟩ {site} (.slot {left}) (.slot {right}) .null .present))"

    wire = authored["late_unreached"]
    lo, hi = next((lo, hi) for key, _, lo, hi in V2["columns"](wire) if key == (group, 0))
    frames = list(JOIN["FRAMES"](wire, lo, hi))
    at = frames[1][0]
    address = JOIN["address"](group, 0, LAYOUT)
    reached = (f".group {group} (.input (.leaf 0 (.chunk "
               f"(.page {address} 1 {at} ⟨2, 2, 1⟩ (.level (.unreachedAncestor 2 1 0))))))")
    return {"late_presence": presence, "late_unreached": reached}


def verify(folder):
    schema, groups, genuine, authored, differing = create()
    expected = traces(groups)
    native, events, ipc = [JOIN["RUNNER"]], [EVENTS["LEAN"]], [IPC["LEAN"]]
    frames, checked, emitted = Counter(), {}, {}
    accepted = genuine | {"independent_cuts": authored["independent_cuts"]}

    for label, wire in (genuine | authored).items():
        (folder / f"{label}.parquet").write_bytes(wire)
        parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
        assert parquet.schema_arrow.equals(schema, check_metadata=True)
        assert parquet.num_row_groups == len(groups)
        if label in accepted:
            assert [parquet.read_row_group(i).to_pylist() for i in range(parquet.num_row_groups)] == groups
        else:
            assert parquet.read_row_group(0).to_pylist() == groups[0]
        if label == "late_unreached":
            continue
        inspected, counts = JOIN["inspect"](wire, differing if label == "late_presence" else expected, LAYOUT)
        checked[label] = inspected
        frames.update(counts)
        carrier = f'(← load folder "{label}")'
        for (group, side), ((lo, hi), pages, _) in inspected.items():
            path = json.dumps(LAYOUT[side][0])
            native.append(f"  checkLeaf {carrier} {group} {side} ⟨{lo}, {hi}⟩ {path} {lst(pages)}")
        for group, rows in enumerate(groups if label in accepted else groups[:1]):
            observation = NATIVE["expected_observation"](schema, rows)
            slots = lst(JOIN["addressed"](group, side, inspected[group, side][2], LAYOUT) for side in range(len(LAYOUT)))
            native.append(f"  checkGroup {carrier} {group} {observation} {slots}")

    for label in accepted:
        EVENTS["append_views"](events, label, schema, groups, ".eos")
        for view, selection in IPC["views"](schema):
            ipc.append(f'  checkIpc folder "{label}" .{view} "{view}" '
                       f'{IPC["fields_term"](selection)} {IPC["batches_term"](selection, groups)}')
            emitted[f"{label}_{view}"] = selection

    for label, cause in source_errors(authored, checked["late_presence"]).items():
        EVENTS["append_views"](events, label, schema, groups[:1], f".readError ({cause})")
        for view, selection in IPC["views"](schema):
            ipc.append(f'  sourceFailure (← load folder "{label}") .{view} '
                       f'{IPC["batches_term"](selection, groups[:1])} ({cause})')

    V2["run_lean"](folder, "LeadingStructRows.lean", native)
    V2["run_lean"](folder, "LeadingStructEvents.lean", events)
    V2["run_lean"](folder, "LeadingStructToIpc.lean", ipc)
    wires = {}
    for label, selection in emitted.items():
        wire = (folder / f"{label}.arrow").read_bytes()
        IPC["IPC"]["inspect_ipc"](wire, selection, groups)
        wires[label] = wire
    for view, _ in IPC["views"](schema):
        assert wires[f"leading_v1_{view}"] == wires[f"leading_v2_{view}"] == wires[f"independent_cuts_{view}"]
    print(f"Checked {len(accepted)} accepted carriers, {frames[0]} original V1 and {frames[3]} V2 pages, "
          f"{len(wires)} strict IPC streams, and two addressed refusals")
    fingerprint = NATIVE["fingerprints"]
    return dict(producer=EVENTS["COMPILER"]["BASE"]["producer"](), genuine_parquet=fingerprint(genuine),
                authored_parquet=fingerprint(authored), emitted_ipc=fingerprint(wires))


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    with tempfile.TemporaryDirectory() as scratch:
        assert verify(Path(scratch)) == pins


if __name__ == "__main__":
    main()
