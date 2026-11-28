"""Check original omitted scalar levels in mixed signed Tree row groups."""

from collections import Counter
import json
from pathlib import Path
import runpy
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
EVENTS = runpy.run_path(str(HERE.parent / "parquet-recursive-tree-events-oracle/check.py"))
IPC = runpy.run_path(str(HERE.parent / "parquet-recursive-tree-to-ipc-oracle/check.py"))
JOIN, NATIVE, V2, lst = (EVENTS[key] for key in ("JOIN", "NATIVE", "V2", "lst"))
LAYOUT = (
    (("identity",), 0, 0, 64, ()),
    (("tag",), 0, 1, 32, ()),
    (("maybe", "low"), 0, 2, 32, ()),
    (("maybe", "high"), 0, 2, 64, ()),
    (("maybe", "samples", "list", "sample"), 1, 4, 32, (2,)),
    (("fixed", "required"), 0, 0, 32, ()),
    (("fixed", "optional"), 0, 1, 64, ()),
    (("series", "list", "reading"), 1, 1, 64, (0,)),
)


def expected_trace(row, side):
    if side in (0, 1, 5, 6):
        path, _, maximum, _, _ = LAYOUT[side]
        value = row
        for name in path:
            value = value[name]
        yield 0, maximum if value is not None else 0, value
    elif side == 7:
        if not row["series"]:
            yield 0, 0, None
        for i, value in enumerate(row["series"]):
            yield int(i > 0), 1, value
    elif row["maybe"] is None:
        yield 0, 0, None
    elif side in (2, 3):
        value = row["maybe"]["low" if side == 2 else "high"]
        yield 0, 1 + int(value is not None), value
    else:
        samples = row["maybe"]["samples"]
        if samples is None:
            yield 0, 1, None
        elif not samples:
            yield 0, 2, None
        else:
            for i, value in enumerate(samples):
                yield int(i > 0), 3 + int(value is not None), value


def traces(groups):
    return {(group, side): [atom for row in rows for atom in expected_trace(row, side)]
            for group, rows in enumerate(groups) for side in range(len(LAYOUT))}


def create():
    maybe = pa.struct([pa.field("low", pa.int32()), pa.field("high", pa.int64()),
                       pa.field("samples", pa.list_(pa.field("sample", pa.int32())))])
    fixed = pa.struct([pa.field("required", pa.int32(), nullable=False), pa.field("optional", pa.int64())])
    series = pa.list_(pa.field("reading", pa.int64(), nullable=False))
    schema = pa.schema([pa.field("identity", pa.int64(), nullable=False), pa.field("tag", pa.int32()),
                        pa.field("maybe", maybe), pa.field("fixed", fixed, nullable=False),
                        pa.field("series", series, nullable=False)])

    def cell(low, high, samples):
        return {"low": low, "high": high, "samples": samples}

    def row(identity, tag, maybe, required, optional, series):
        return {"identity": identity, "tag": tag, "maybe": maybe,
                "fixed": {"required": required, "optional": optional}, "series": series}

    groups = [
        [row(-2**63, None, None, -2**31, None, []),
         row(2**63 - 1, -2**31, cell(None, None, None), 2**31 - 1, -2**63, [7, 8, 9]),
         row(0, 2**31 - 1, cell(4, None, []), 11, 2**63 - 1, [10]),
         row(18, None, cell(-2**31, 2**63 - 1, [2**31 - 1, None, -4]), -17, None, [])],
        [row(27, -3, cell(None, None, None), 22, 12, [11]),
         row(-59, None, cell(None, -2**63, [None, 13, 14]), -23, None, [15, 16, 17, 18]),
         row(71, 19, None, 24, 20, []),
         row(73, 21, cell(2**31 - 1, 23, []), 25, None, [22])],
    ]

    def write(version):
        sink = pa.BufferOutputStream()
        with pq.ParquetWriter(sink, schema, compression="NONE", use_dictionary=False, data_page_version=version,
                              store_schema=False, use_compliant_nested_type=False, write_page_checksum=True,
                              data_page_size=64, max_rows_per_page=1, write_batch_size=1) as writer:
            for group in groups:
                writer.write_table(pa.Table.from_pylist(group, schema=schema))
        return sink.getvalue().to_pybytes()

    genuine = {f"scalar_v{version}": write(f"{version}.0") for version in (1, 2)}
    v1, v2 = genuine["scalar_v1"], genuine["scalar_v2"]
    old, new = NATIVE["raw_chunks"](v1), NATIVE["raw_chunks"](v2)
    mixed = NATIVE["repack"](v1, old | {(1, side): new[1, side] for side in (0, 2, 4, 5)})
    authored = {"mixed_versions": mixed}
    expected = traces(groups)
    refused = {}

    def physical(wire, side, ordinal):
        lo, hi = next((lo, hi) for key, _, lo, hi in V2["columns"](wire) if key == (1, side))
        return list(JOIN["FRAMES"](wire, lo, hi))[ordinal]

    def patch(label, base, side, ordinal, page, cause=None):
        carrier = old if base == v1 else new
        original = carrier[1, side]
        wire = authored[label] = NATIVE["repack"](base, carrier | {
            (1, side): [*original[:ordinal], page, *original[ordinal + 1:]]})
        if cause is not None:
            byte = physical(wire, side, ordinal)[0]
            address = JOIN["address"](1, side, LAYOUT)
            # Every scalar page in this group has one row and a closed reader state.
            refused[label] = (f".group 1 (.input (.leaf {side} (.chunk "
                              f"(.page {address} {ordinal} {byte} ⟨{ordinal}, {ordinal}, 0⟩ ({cause})))))")

    _, header, _, words = physical(v2, 0, 1)
    info = header[8][1]
    assert [info[i][1] for i in (1, 2, 3, 5, 6)] == [1, 0, 1, 0, 0] and len(words) == 8

    def frame(rep=b"", defs=b"", rows=1, nulls=0):
        return V2["v2_frame"](rep, defs, words, rows, nulls, 1, crc=True)

    patch("v2_repetition_bytes", v2, 0, 1, frame(rep=b"\0"), ".v2 (.repetition (.unexpectedV2Levels 1))")
    patch("v2_definition_bytes", v2, 0, 1, frame(defs=b"\0"), ".v2 (.definition (.unexpectedV2Levels 1))")
    patch("v2_rows", v2, 0, 1, frame(rows=0), ".v2 (.v2Rows 0 1)")
    patch("v2_nulls", v2, 0, 1, frame(nulls=1), ".v2 (.v2Nulls 1 0)")

    _, header, _, body = physical(v1, 0, 1)
    assert len(body) == 8 and header[5][1][1][1] == 1
    page = V2["encode"](header, body + b"\0"*4, resize=True)
    patch("v1_extra_bytes", v1, 0, 1, page, ".plain .trailingBytes")

    # The first scalar in this group is absent inside a present all-null Struct.
    # Rewrite only its valid definition marker to make the shared Struct absent.
    assert expected[1, 2][0] == (0, 1, None)
    page = V2["v2_frame"](b"", b"\x02\x00", b"", 1, 1, 1, crc=True)
    patch("late_presence", v2, 2, 0, page)
    differing = expected | {(1, 2): [(0, 0, None), *expected[1, 2][1:]]}
    return schema, groups, genuine, authored, refused, differing


def verify(folder):
    schema, groups, genuine, authored, refused, differing = create()
    expected = traces(groups)
    native, events, ipc = [JOIN["RUNNER"]], [EVENTS["LEAN"]], [IPC["LEAN"]]
    accepted = genuine | {"mixed_versions": authored["mixed_versions"]}
    frames, selected_outputs = Counter(), {}
    for label, wire in (genuine | authored).items():
        (folder / f"{label}.parquet").write_bytes(wire)
        parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
        assert parquet.schema_arrow.equals(schema, check_metadata=True)
        assert parquet.num_row_groups == len(groups)
        if label in accepted:
            assert [parquet.read_row_group(i).to_pylist() for i in range(parquet.num_row_groups)] == groups
        else:
            assert parquet.read_row_group(0).to_pylist() == groups[0]
        if label in refused:
            continue

        inspected, counts = JOIN["inspect"](wire, differing if label == "late_presence" else expected, LAYOUT)
        frames.update(counts)
        carrier = f'(← load folder "{label}")'
        for (group, side), ((lo, hi), pages, _) in inspected.items():
            path = json.dumps(LAYOUT[side][0])
            native.append(f"  checkLeaf {carrier} {group} {side} ⟨{lo}, {hi}⟩ {path} {lst(pages)}")
        for group, rows in enumerate(groups if label in accepted else groups[:1]):
            observation = NATIVE["expected_observation"](schema, rows)
            slots = lst(JOIN["addressed"](group, side, inspected[group, side][2], LAYOUT) for side in range(len(LAYOUT)))
            native.append(f"  checkGroup {carrier} {group} {observation} {slots}")

        if label == "late_presence":
            left = JOIN["point"](1, 2, *inspected[1, 2][2][0][:3], LAYOUT)
            right = JOIN["point"](1, 3, *inspected[1, 3][2][0][:3], LAYOUT)
            refused[label] = (f'.group 1 (.join (.presence ⟨0, []⟩ ⟨3, ["maybe"]⟩ '
                              f'(.slot {left}) (.slot {right}) .null .present))')

    for label in accepted:
        EVENTS["append_views"](events, label, schema, groups, ".eos")
        for view, selection in IPC["views"](schema):
            ipc.append(f'  checkIpc folder "{label}" .{view} "{view}" '
                       f'{IPC["fields_term"](selection)} {IPC["batches_term"](selection, groups)}')
            selected_outputs[f"{label}_{view}"] = selection

    for label, cause in refused.items():
        EVENTS["append_views"](events, label, schema, groups[:1], f".readError ({cause})")
        for view, selection in IPC["views"](schema):
            ipc.append(f'  sourceFailure (← load folder "{label}") .{view} '
                       f'{IPC["batches_term"](selection, groups[:1])} ({cause})')

    V2["run_lean"](folder, "ScalarTreeRows.lean", native)
    V2["run_lean"](folder, "ScalarTreeEvents.lean", events)
    V2["run_lean"](folder, "ScalarTreeToIpc.lean", ipc)
    emitted = {}
    for label, selection in selected_outputs.items():
        wire = (folder / f"{label}.arrow").read_bytes()
        IPC["IPC"]["inspect_ipc"](wire, selection, groups)
        emitted[label] = wire
    for view, _ in IPC["views"](schema):
        assert emitted[f"scalar_v1_{view}"] == emitted[f"scalar_v2_{view}"] == emitted[f"mixed_versions_{view}"]
    print(f"Checked {len(accepted)} accepted carriers, {frames[0]} original V1 and {frames[3]} V2 pages, "
          f"{len(emitted)} strict IPC streams and {len(refused)} addressed refusals")
    fingerprint = NATIVE["fingerprints"]
    return dict(producer=EVENTS["COMPILER"]["BASE"]["producer"](), genuine_parquet=fingerprint(genuine),
                authored_parquet=fingerprint(authored), emitted_ipc=fingerprint(emitted))


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    with tempfile.TemporaryDirectory() as scratch:
        assert verify(Path(scratch)) == pins


if __name__ == "__main__":
    main()
