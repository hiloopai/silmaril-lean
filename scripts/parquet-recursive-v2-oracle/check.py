"""Inspect recursive signed V2 pages and the original Lean Events and IPC routes."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BRIDGE = runpy.run_path(str(HERE.parent / "parquet-recursive-repeated-ipc-events-oracle/check.py"))
WRITER = runpy.run_path(str(HERE.parent / "parquet-recursive-leaf-page-writer-oracle/check.py"))
STREAM = runpy.run_path(str(HERE.parent / "arrow-recursive-stream-oracle/check.py"))
CHUNK = WRITER["CHUNK"]
SCHEMA, THRIFT, MIXED, FRAMES, HYBRID, fingerprints, lst = (
    CHUNK[key] for key in ("SCHEMA", "THRIFT", "MIXED", "FRAMES", "HYBRID", "fingerprints", "lst")
)
wrap_pages = WRITER["wrap_pages"]
Page, Column = CHUNK["Page"], CHUNK["Column"]


LEAN = CHUNK["LEAN"] + """\

private def spans (file : Bytes) (group column : Nat)
    (wanted : List (Option (Parquet.Page.DataV2 × Parquet.Page.V2Spans))) : IO Unit := do
  let source ← take (openFile {} file)
  let binding ← take (bindChunk source.schema group column)
  let seen ← take (Parquet.RecursiveSchema.Repeated.Chunk.read {} binding)
  let original := seen.pages.map fun page =>
    match page.frame.value.kind with
    | .dataV2 info => page.frame.v2Spans.map (fun regions => (info, regions))
    | _ => none
  unless original = wanted do throw (IO.userError "original V2 subspans or counts differ")

private def bindFailure (file : Bytes) (group column : Nat) (wanted : BindError) : IO Unit := do
  let source ← take (openFile {} file)
  deny wanted (bindChunk source.schema group column)
"""


def write(schema, groups, *, checksum=False, compression="NONE", indexed=False, small_pages=False):
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, compression=compression, use_dictionary=False,
                          use_compliant_nested_type=False, store_schema=False, data_page_version="2.0",
                          write_page_checksum=checksum, write_page_index=indexed, write_statistics=True,
                          data_page_size=40 if small_pages else 1 << 20,
                          write_batch_size=2 if small_pages else 1,
                          max_rows_per_page=(1 << 20) if small_pages else 1) as writer:
        for rows in groups:
            writer.write_table(pa.Table.from_pylist(rows, schema=schema))
    return sink.getvalue().to_pybytes()


def columns(wire):
    footer = MIXED["metadata"](wire)
    for group, row_group in enumerate(THRIFT["list_field"](footer, 4)):
        for index, column in enumerate(THRIFT["list_field"](row_group, 1)):
            metadata = column[3][1]
            start, stop = MIXED["column_extent"](metadata)
            yield (group, index), metadata, start, stop


def edit_page(wire, group, column, ordinal, edit):
    chunks = {}
    for key, _, start, stop in columns(wire):
        if key == (group, column):
            frames = list(FRAMES(wire, start, stop))
            header, fields, payload, body = frames[ordinal]
            assert header >= start
            changed = edit(fields, body)
            chunks[key] = wire[start:header] + changed + wire[payload + len(body):stop]
        else:
            chunks[key] = wire[start:stop]
    return wrap_pages(wire, chunks)


def i32(value):
    return TType.I32, value


def encode(fields, body, *, resize=False):
    if resize:
        fields[2] = fields[3] = i32(len(body))
        if 4 in fields:
            crc = zlib.crc32(body)
            fields[4] = i32(crc if crc < 2**31 else crc - 2**32)
    return THRIFT["encode"](fields) + body


def v2_frame(rep, defs, values, rows, nulls, slots, *, crc=False):
    info = {1: i32(slots), 2: i32(nulls), 3: i32(rows), 4: i32(0),
            5: i32(len(defs)), 6: i32(len(rep)), 7: (TType.BOOL, False)}
    fields = {1: i32(3), 8: (TType.STRUCT, info)}
    if crc:
        fields[4] = i32(0)
    return encode(fields, rep + defs + values, resize=True)


def from_v1(fields, body):
    count = fields[5][1][1][1]
    rep, tail = CHUNK["level_section"](body, 1, count)
    defs, values = CHUNK["level_section"](tail, 3, count)
    raw_rep = body[4:len(body) - len(tail)]
    raw_defs = tail[4:len(tail) - len(values)]
    return v2_frame(raw_rep, raw_defs, values, rep.count(0), sum(d != 3 for d in defs), count)


def schema_term(fields):
    return "⟨" + ", ".join(str(fields[i][1]) for i in (1, 2, 3, 4, 5, 6)) + ", " + str(
        fields.get(7, (None, True))[1]).lower() + "⟩"


def snappy_block(codec, stored, size):
    assert codec == 1
    return pa.Codec("snappy").decompress(stored, size).to_pybytes()


def capture(wire, schema, rows, *, codec=0, decode_block=snappy_block):
    _, leaves = SCHEMA["describe"](wire, schema, rows)
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    for (group, index), metadata, start, stop in columns(wire):
        column_codec = metadata[4][1] if codec is None else codec
        assert column_codec in (0, 1, 2, 6, 7) and metadata[4][1] == column_codec
        (_, path), scalar, steps, repeated = leaves[index]
        group_rows = parquet.read_row_group(group).to_pylist()
        expected = [event for row in group_rows
                    for event in CHUNK["from_arrow"](row[path[0]], schema.field(path[0]), path[1:])]
        slot, row, raw_size, live, seen, v2 = 0, 0, 0, False, [], []
        for ordinal, (header, fields, payload, body) in enumerate(FRAMES(wire, start, stop)):
            assert fields[3][1] == len(body)
            raw_size += payload - header + fields[2][1]
            crc = fields[4][1] & 0xffffffff if 4 in fields else None
            if crc is not None:
                assert crc == zlib.crc32(body)
            tag = fields[1][1]
            if tag == 3:
                info = fields[8][1]
                count, nulls, rows_on_page, encoding, dl, rl = [info[i][1] for i in (1, 2, 3, 4, 5, 6)]
                scalar_at = rl + dl
                assert encoding == 0 and scalar_at <= len(body)

                def raw_levels(raw, maximum):
                    if maximum == 0:
                        assert raw == b""
                        return [0] * count
                    return HYBRID(raw, maximum.bit_length(), count)

                rep = raw_levels(body[:rl], int(repeated is not None))
                defs = raw_levels(body[rl:scalar_at], len(steps))
                values = body[scalar_at:]
                raw_values = fields[2][1] - scalar_at
                assert raw_values >= 0
                if column_codec != 0 and info.get(7, (None, True))[1]:
                    values = decode_block(column_codec, values, raw_values)
                assert len(values) == raw_values
                assert not rep or rep[0] == 0
                assert rep.count(0) == rows_on_page and sum(d != len(steps) for d in defs) == nulls
                v2.append(f"(some ({schema_term(info)}, ⟨⟨{payload}, {payload+rl}⟩, "
                          f"⟨{payload+rl}, {payload+scalar_at}⟩, ⟨{payload+scalar_at}, {payload+len(body)}⟩⟩))")
            else:
                assert tag == 0
                raw = body if column_codec == 0 else decode_block(column_codec, body, fields[2][1])
                assert len(raw) == fields[2][1]
                count = fields[5][1][1][1]
                rep, rest = CHUNK["level_section"](raw, int(repeated is not None), count)
                defs, values = CHUNK["level_section"](rest, len(steps), count)
                v2.append("none")
            fmt = "<i" if scalar.type.bit_width == 32 else "<q"
            words = [value for value, in struct.iter_unpack(fmt, values)]
            assert len(words) == defs.count(len(steps))
            ordered = iter(words)
            events = [(r, d, next(ordered) if d == len(steps) else None) for r, d in zip(rep, defs, strict=True)]
            assert events == expected[slot:slot + count]
            before = (slot, row, live)
            for r, d, _ in events:
                assert r == 0 or live
                live = repeated is not None and d > repeated[2]
                row += r == 0
            if tag == 3:
                live = False
            slot += count
            seen.append(Page(ordinal, header, payload, payload + len(body), crc, before,
                             (slot, row, live), events))
        assert seen[-1].stop == stop and metadata[5][1] == slot == len(expected)
        assert metadata[6][1] == raw_size and metadata[7][1] == stop - start
        assert row == len(group_rows)
        yield Column(group, index, path, scalar.type.bit_width, start, stop, slot, row, steps, seen), v2


def fixtures(scratch):
    _, samples, _ = SCHEMA["fixtures"]()
    schema, rows = samples["nullable_lists"]
    required, required_rows = samples["required_lists"]
    _, many = CHUNK["multipage"](schema)
    genuine = {
        "nested": write(schema, [rows[:3], rows[3:]], checksum=True),
        "required_lists": write(required, [required_rows]),
        "unequal_siblings": write(schema, [many[:18], many[18:]], checksum=True, small_pages=True),
        "pageless_zero": write(schema, [rows[:3], [], rows[3:]], checksum=True),
        "snappy": write(schema, [rows], compression="SNAPPY"),
        "indexed": write(schema, [rows], indexed=True),
    }
    pageless = genuine["pageless_zero"]
    blank = v2_frame(b"", b"", b"", 0, 0, 0, crc=True)
    assert [stop - start for (g, _), _, start, stop in columns(pageless) if g == 1] == [0] * 4
    footer = MIXED["metadata"](pageless)
    zero = THRIFT["list_field"](footer, 4)[1]
    for chunk in THRIFT["list_field"](zero, 1):
        chunk[3][1][2] = TType.LIST, (TType.I32, [0, 3])
    framed = wrap_pages(SCHEMA["pack"](pageless, footer), {
        key: blank if key[0] == 1 else pageless[start:stop] for key, _, start, stop in columns(pageless)
    })

    native, _, prior = CHUNK["continuation_fixtures"](scratch)
    mixed_schema = pq.ParquetFile(pa.BufferReader(native)).schema_arrow
    mixed_rows = [{"items": value} for value in CHUNK["CONT"]["ROWS"]]
    native_mixed = edit_page(native, 0, 0, 2, from_v1)
    labeled = {"framed_zero": framed, "mixed_boundary": native_mixed}
    positive = {"nested": (schema, rows), "required_lists": (required, required_rows),
                "unequal_siblings": (schema, many), "framed_zero": (schema, rows),
                "mixed_boundary": (mixed_schema, mixed_rows)}

    nested = genuine["nested"]

    def change_value(field, value):
        def edit(fields, body):
            fields[8][1][field] = i32(value)
            return encode(fields, body)
        return edit

    def default_flag(fields, body):
        del fields[8][1][7]
        return encode(fields, body)

    labeled["identity_default_flag"] = edit_page(nested, 1, 0, 0, default_flag)
    positive["identity_default_flag"] = schema, rows

    def mutate(fields, body, kind):
        info = fields[8][1]
        rep = info[6][1]
        if kind == "header_sizes":
            info[7] = TType.BOOL, True
            fields[2] = i32(len(body) + 1)
            return encode(fields, body)
        if kind == "zero_width":
            info[5] = i32(2)
            body = b"\x02\0" + body
        if kind == "extra_rep":
            info[6] = i32(rep + 1)
            body = body[:rep] + b"\0" + body[rep:]
        if kind == "short_word":
            body = body[:-1]
        if kind == "extra_word":
            body += b"\0" * 4
        if kind == "crc":
            return encode(fields, body[:-1] + bytes([body[-1] ^ 1]))
        return encode(fields, body, resize=True)

    def at_leaf(name, edit, column=0):
        labeled[name] = edit_page(nested, 1, column, 0, edit)

    at_leaf("late_nulls", change_value(2, 2))
    at_leaf("row_count", change_value(3, 2))
    at_leaf("bad_header_count", change_value(3, 5))
    at_leaf("bad_level_extent", change_value(5, 100))
    at_leaf("slot_overrun", change_value(1, 6))
    at_leaf("encoding", change_value(4, 2))
    for kind in ("header_sizes", "extra_rep", "short_word", "extra_word", "crc"):
        at_leaf(kind, lambda fields, body, kind=kind: mutate(fields, body, kind))
    at_leaf("zero_width", lambda fields, body: mutate(fields, body, "zero_width"), 3)
    authored = prior["authored_continuation"]
    labeled["v2_starts_mid_row"] = edit_page(authored, 0, 0, 3, from_v1)
    labeled["v1_continues_v2"] = edit_page(authored, 0, 0, 2, from_v1)

    return genuine, labeled, positive


def run_lean(scratch, filename, lines):
    driver = scratch / filename
    driver.write_text("\n".join(lines) + "\n", encoding="utf-8")
    subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                    "--run", str(driver), str(scratch)], cwd=ROOT, check=True)


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    producer = pins["producer"]
    assert platform.python_implementation() == "CPython" and platform.python_version() == producer["cpython"]
    assert pa.__version__ == producer["pyarrow"] and version("thrift") == producer["thrift"]
    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        genuine, labeled, positive = fixtures(scratch)
        files = genuine | labeled
        for name, wire in files.items():
            (scratch / f"{name}.parquet").write_bytes(wire)
        start = ["public def main (args : List String) : IO Unit := do",
                 '  let [folder] := args | throw (IO.userError "expected fixture folder")']
        code, bridge = [LEAN, *start], [BRIDGE["LEAN"], *start]
        for name, (schema, rows) in positive.items():
            captured = list(capture(files[name], schema, rows))
            for column, v2 in captured:
                code.append(CHUNK["check_term"](column, name))
                code.append(f'  spans (← load folder "{name}") {column.group} {column.index} {lst(v2)}')
            fields, groups, counts = BRIDGE["observed"](files[name])
            bridge.append(f'  emit folder "{name}" (← load folder "{name}") {fields} {groups}')
            print(f"{name}: {len(captured)} chunks, {sum(len(col.pages) for col, _ in captured)} pages, groups {counts}")
            if name == "unequal_siblings":
                lo, hi = captured[0][0], captured[1][0]
                assert [page.before[1] for page in lo.pages] != [page.before[1] for page in hi.pages]

        leaf_path = '["packet", "items", "list", "élément", "lo"]'

        def page_error(label, cause, *, group=1, column=0, ordinal=0, state="{}", path=leaf_path):
            wire = files[label]
            _, _, begin, end = next(entry for entry in columns(wire) if entry[0] == (group, column))
            at = list(FRAMES(wire, begin, end))[ordinal][0]
            error = f'.page ⟨{group}, {column}, {path}⟩ ⟨{ordinal}, {at}, {state}⟩ ({cause})'
            code.append(f'  refuse (← load folder "{label}") {group} {column} {{}} ({error})')
            return error

        late = page_error("late_nulls", ".v2Nulls 2 1")
        page_error("row_count", ".v2Rows 2 1")
        page_error("bad_header_count", ".framing (.header .invalidV2Counts)")
        page_error("bad_level_extent", ".framing (.header .invalidV2Lengths)")
        page_error("slot_overrun", ".slotOverrun 5 6")
        page_error("encoding", ".v2Encoding 2")
        _, _, begin, end = next(entry for entry in columns(files["header_sizes"]) if entry[0] == (1, 0))
        expect_sizes = next(FRAMES(files["header_sizes"], begin, end))[1]
        page_error("header_sizes", f".header (.pageSizes {expect_sizes[2][1]} {expect_sizes[3][1]})")
        page_error("extra_rep", ".repetition (.hybrid .trailingBytes)")
        page_error("short_word", ".plain .truncated")
        page_error("extra_word", ".plain .trailingBytes")
        page_error("zero_width", ".definition (.unexpectedV2Levels 2)", column=3, path='["seq"]')
        _, _, begin, end = next(entry for entry in columns(files["crc"]) if entry[0] == (1, 0))
        _, crc_header, _, changed = next(FRAMES(files["crc"], begin, end))
        page_error("crc", f".checksum (.mismatch {crc_header[4][1] & 0xffffffff} {zlib.crc32(changed)})")
        for label, cause, live in (("v2_starts_mid_row", ".v2RowBoundary 4 1", "true"),
                                   ("v1_continues_v2", ".continuationWithoutList 4", "false")):
            page_error(label, cause, group=0, ordinal=3, state=f"⟨4, 3, {live}⟩",
                       path='["items", "list", "element"]')
        code.extend([
            f'  bindFailure (← load folder "indexed") 0 0 (.column ⟨0, 0, {leaf_path}⟩ .pageIndex)',
            '  deny (.invalidMetadata .pageInterval) (Parquet.Snapshot.check (Failure := Unit) {} (← load folder "pageless_zero"))',
        ])
        fields, groups, _ = BRIDGE["observed"](files["nested"], limit=1)
        bridge.extend([
            f'  check "late V2 null count" (direct (← load folder "late_nulls")) {fields} {groups} '
            f'(.readError (.group 1 (.chunk ({late}))))',
            f'  sourceFailure (← load folder "late_nulls") (.chunk ({late}))',
        ])
        run_lean(scratch, "Chunk.lean", code)
        run_lean(scratch, "Bridge.lean", bridge)

        returned = {}
        for name in positive:
            raw = (scratch / f"{name}.arrow").read_bytes()
            source = pq.ParquetFile(pa.BufferReader(files[name]))
            reader = pa.ipc.open_stream(raw)
            assert reader.schema == source.schema_arrow
            _, cursor = STREAM["metadata"](raw)
            assert [batch.to_pylist() for batch in reader] == [
                source.read_row_group(group).to_pylist() for group in range(source.num_row_groups)
            ]
            for group in range(source.num_row_groups):
                record = STREAM["read_record"](raw, cursor)
                assert record.rows == source.metadata.row_group(group).num_rows
                cursor = record.end
            assert raw[cursor:] == STREAM["EOS"]
            returned[name] = raw
        captured = {"genuine_parquet": fingerprints(genuine), "labeled_edits": fingerprints(labeled),
                    "lean_ipc": fingerprints(returned)}
        for kind, values in captured.items():
            assert values == pins[kind], f"{kind} fixture pins changed"
    print("Checked native V2 pages, direct Events, exact IPC and sixteen typed source refusals")


if __name__ == "__main__":
    main()
