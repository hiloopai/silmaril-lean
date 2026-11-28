"""Pin a branching LIST/Struct footer and read its original leaves independently."""

from collections import Counter
import json
from pathlib import Path
import runpy
import struct
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
BASE = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-v2-oracle/check.py"))
NATIVE, EVENTS = BASE["NATIVE"], BASE["EVENTS"]
FRAMES, LEVEL, THRIFT, V2, lst, page_term = (NATIVE[key] for key in
                                           ("FRAMES", "LEVEL", "THRIFT", "V2", "lst", "page_term"))
OUTER = ("items",)
WRAPPER = (*OUTER, "list")
ELEMENT = (*WRAPPER, "element")
B, C = (*ELEMENT, "b"), (*ELEMENT, "c")
PATHS = ((*ELEMENT, "a"), (*B, "list", "element"), (*C, "list", "element"))
DEPTHS, DEFINITIONS, WIDTHS = (1, 2, 2), (4, 6, 5), (32, 64, 32)


LEAN = """
module

import Silmaril.Formats.Parquet.RecursiveSchema.Tree.ListPath.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Tree.ListPath.Defs

open Silmaril.Formats Silmaril.Formats.Parquet
open RecursiveSchema.Tree

set_option maxRecDepth 8192

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def refuse {ε α : Type} [BEq ε] [Repr ε] (result : Except ε α) (wanted : ε) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError "expected a typed refusal")
  | .error error =>
    unless error == wanted do throw (IO.userError s!"wanted {repr wanted}, got {repr error}")

private structure ExpectedPage where
  frame : Page.Frame
  sections : RecursiveSchema.ListPath.Chunk.Sections
  start : RecursiveSchema.ListPath.Chunk.State
  stop : RecursiveSchema.ListPath.Chunk.State
  atoms : List RecursiveSchema.ListPath.Rows.Atom

private def checkLeaf (file : Bytes) (group column : Nat) (span : Footer.Span) (path : List String)
    (pages : List ExpectedPage) : IO Unit := do
  let source ← take (openFile {} file)
  let bound ← take (bindLeaf source.schema group column)
  let observed ← take (readLeaf source.schema {} group column)
  let plan := bound.leaf.path
  unless bound.carrier.address = ⟨group, column, path⟩ && bound.span = span &&
      bound.plan.shape.repetitions = plan.maxRepetition && bound.plan.shape.definitions = plan.maxDefinition &&
      bound.plan.shape.steps {} == plan.steps &&
      RecursiveSchema.ListPath.Chunk.wrappers bound.plan == plan.repeated.map (·.emptyLevel) &&
      observed.dictionary.isNone && observed.pages.length = pages.length do
    throw (IO.userError "original carrier or thresholds differ")
  for (page, expected) in observed.pages.zip pages do
    unless page.frame = expected.frame && page.decoded.sections = expected.sections &&
        page.start = expected.start && page.decoded.after = expected.stop && page.decoded.atoms = expected.atoms do
      throw (IO.userError "original frame, level spans, cursors or words differ")

private def checkTree (file : Bytes) (want : List Arrow.RecursiveSchema.Field)
    (declarations : List Nat) (expected : List LeafPlan) : IO Unit := do
  let source ← take (openFile {} file)
  unless source.schema.arrow.fields == want && source.schema.leaves.toList == expected &&
      source.schema.declarations.map (·.location.ordinal) == declarations do
    throw (IO.userError "checked declaration, original order or leaf ancestry differs")

private def checkLevels (file : Bytes) : IO Unit := do
  let source ← take (openFile {} file)
  let plans := source.schema.leaves
  unless plans.map (·.path.maxRepetition) == #[1, 2, 2] &&
      plans.map (·.path.maxDefinition) == #[4, 6, 5] &&
      plans.map (fun plan => plan.path.repeated.map (·.wrapper.ordinal)) == #[[2], [2, 6], [2, 9]] &&
      plans.map (fun plan => plan.path.repeated.map (·.emptyLevel)) == #[[1], [1, 4], [1, 3]] &&
      plans.map (fun plan => plan.path.nullable.map (fun (loc, _, level) => (loc.ordinal, level))) ==
        #[
          [(1, 0), (3, 2), (4, 3)],
          [(1, 0), (3, 2), (5, 3), (7, 5)],
          [(1, 0), (3, 2), (10, 4)]
        ] do throw (IO.userError "definition and repetition thresholds differ")
  refuse (RecursiveSchema.Repeated.compile {} source.snapshot)
    (.nestedRepeated ⟨5, ["items", "list", "element", "b"]⟩ ⟨2, ["items", "list"]⟩)
  refuse (compile { maxSchemaDepth := 6 } source.snapshot)
    (.original (.depth ⟨7, ["items", "list", "element", "b", "list", "element"]⟩))

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture directory")
"""


def create():
    b = pa.list_(pa.field("element", pa.int64()))
    c = pa.list_(pa.field("element", pa.int32()))
    fields = [pa.field("a", pa.int32()), pa.field("b", b), pa.field("c", c, nullable=False)]
    def schema(children):
        return pa.schema([pa.field("items", pa.list_(pa.field("element", pa.struct(children))))])

    def item(a, b, c):
        return {"a": a, "b": b, "c": c}

    groups = [
        [None, [], [None, item(None, [], [7, None]), item(-2**31, [None, -2**63, 8], []),
                    item(0, None, [2**31 - 1]), item(34, [2**63 - 1], [1, 2, 3])]],
        [[item(3, [11, 12, 13, 14], []), item(None, None, [None, 1]), None],
         [item(7, [], [None]), item(12, [None, 17], [])], []],
    ]
    kind = schema(fields)
    fixtures = {f"branch_v{version}": NATIVE["write"](kind, groups, data_page_version=f"{version}.0",
                                                     max_rows_per_page=1, write_batch_size=1)
                for version in (1, 2)}
    unsupported = schema([pa.field("a", pa.float64()), *fields[1:]])
    fixtures["unsupported_double"] = NATIVE["write"](unsupported, [[[], None, [item(1.0, [3], [])]]])
    leading = pa.schema([pa.field("payload", pa.struct([
        pa.field("nested", c, nullable=False), pa.field("id", pa.int64(), nullable=False)]))])
    fixtures["leading_struct"] = NATIVE["write"](leading, [[None, {"nested": [3, None], "id": -4}]])
    return kind, groups, leading, fixtures


def expected_trace(rows, side):
    for row in rows:
        if row is None or not row:
            yield (0, int(row is not None), None)
            continue
        for ordinal, element in enumerate(row):
            rep = int(ordinal != 0)
            if element is None:
                yield rep, 2, None
                continue
            child = element[("a", "b", "c")[side]]
            maximum = DEFINITIONS[side]
            if side == 0:
                yield rep, maximum - int(child is None), child
            elif child is None:
                assert side == 1
                yield rep, 3, None
            elif not child:
                yield rep, maximum - 2, None
            else:
                for index, value in enumerate(child):
                    yield rep if index == 0 else 2, maximum - int(value is None), value


def inspect(wire, schema, groups, version):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.equals(schema, check_metadata=True)
    assert [parquet.read_row_group(i).column(0).to_pylist() for i in range(parquet.num_row_groups)] == groups
    footer = NATIVE["metadata"](wire)
    nodes = THRIFT["list_field"](footer, 2)
    assert [node[4][1].decode() for node in nodes[1:]] == [
        "items", "list", "element", "a", "b", "list", "element", "c", "list", "element"]
    assert [node[3][1] for node in nodes[1:]] == [1, 2, 1, 1, 1, 2, 1, 0, 2, 1]
    assert [(i, node[1][1]) for i, node in enumerate(nodes) if 1 in node] == [(4, 1), (7, 2), (10, 1)]
    assert [parquet.schema.column(i).path for i in range(3)] == [".".join(path) for path in PATHS]
    assert [(parquet.schema.column(i).max_repetition_level, parquet.schema.column(i).max_definition_level)
            for i in range(3)] == list(zip(DEPTHS, DEFINITIONS, strict=True))

    result = {}
    for (group, side), metadata, lo, hi in V2["columns"](wire):
        assert metadata[4][1] == 0 and metadata[9][1] == lo
        assert set(THRIFT["list_field"](metadata, 2)) == {0, 3} and 11 not in metadata
        assert [piece.decode() for piece in THRIFT["list_field"](metadata, 3)] == list(PATHS[side])
        depth, maximum, width = DEPTHS[side], DEFINITIONS[side], WIDTHS[side]
        expected = list(expected_trace(groups[group], side))
        slots, rows, live = 0, 0, 0
        pages = []
        for at, header, body_at, body in FRAMES(wire, lo, hi):
            assert header[1][1] == (0 if version == 1 else 3)
            assert header[2][1] == header[3][1] == len(body)
            crc = header[4][1] & 0xffffffff
            assert crc == zlib.crc32(body)
            start = slots, rows, live
            if version == 1:
                count, physical, defs_kind, reps_kind = (header[5][1][i][1] for i in range(1, 5))
                assert (physical, defs_kind, reps_kind) == (0, 3, 3)
                reps, rest = LEVEL(body, depth, count)
                defs, suffix = LEVEL(rest, maximum, count)
                sections = body_at, body_at + len(body) - len(rest), body_at + len(body) - len(suffix), body_at + len(body)
            else:
                count, nulls, new_rows, physical, dl, rl = (header[8][1][i][1] for i in range(1, 7))
                assert physical == 0 and 0 <= dl and 0 <= rl and rl + dl <= len(body)
                reps = V2["HYBRID"](body[:rl], depth.bit_length(), count)
                defs = V2["HYBRID"](body[rl:rl + dl], maximum.bit_length(), count)
                suffix = body[rl + dl:]
                assert (not reps or reps[0] == 0) and reps.count(0) == new_rows
                assert nulls == count - defs.count(maximum)
                sections = body_at, body_at + rl, body_at + rl + dl, body_at + len(body)
                live = 0
            assert len(reps) == len(defs) == count
            assert len(suffix) == defs.count(maximum) * (width // 8)
            words = iter(word for word, in struct.iter_unpack("<i" if width == 32 else "<q", suffix))
            trace = [(rep, definition, next(words) if definition == maximum else None)
                     for rep, definition in zip(reps, defs, strict=True)]
            assert trace == expected[slots:slots + count]
            wrapper_stops = [1] if side == 0 else ([1, 4] if side == 1 else [1, 3])
            for rep, definition, _ in trace:
                reached = sum(stop < definition for stop in wrapper_stops)
                assert rep <= min(live, reached)
                live = reached
                rows += rep == 0
            slots += count
            if version == 2:
                live = 0
            pages.append(page_term((at, body_at, crc, len(body), sections, start, (slots, rows, live), trace), width, header))
        assert rows == len(groups[group]) and slots == len(expected) == metadata[5][1]
        assert metadata[6][1] == metadata[7][1] == hi - lo
        result[group, side] = (lo, hi), pages
    assert [len(list(expected_trace(groups[0], side))) for side in range(3)] == [7, 9, 10]
    assert len(result) == len(groups) * 3
    return result


def location(ordinal, path):
    return f"⟨{ordinal}, {json.dumps(path)}⟩"


def site(ordinal, path, nullable=True):
    return f"⟨{location(ordinal, path)}, {json.dumps(path[-1])}, {str(nullable).lower()}⟩"


def expected_plans():
    outer = f".list {site(1, OUTER)} {location(2, WRAPPER)}"
    element = f".struct {site(3, ELEMENT)}"
    inner_b = f".list {site(5, B)} {location(6, (*B, 'list'))}"
    inner_c = f".list {site(8, C, False)} {location(9, (*C, 'list'))}"
    return lst(f"⟨{column}, ⟨{site(ordinal, PATHS[column])}, .int{width}, {lst(ancestors)}⟩⟩"
               for column, ordinal, width, ancestors in (
                   (0, 4, 32, [outer, element]), (1, 7, 64, [outer, element, inner_b]),
                   (2, 10, 32, [outer, element, inner_c])))


def verify(folder):
    schema, groups, leading, fixtures = create()
    for label, wire in fixtures.items():
        (folder / f"{label}.parquet").write_bytes(wire)

    lines = [LEAN]
    counts = Counter()
    fields = lst(map(EVENTS["field_term"], schema))
    for version in (1, 2):
        label = f"branch_v{version}"
        lines.append(f'  checkTree (← load folder "{label}") {fields} {lst(map(str, range(1, 11)))} {expected_plans()}')
        lines.append(f'  checkLevels (← load folder "{label}")')
        for (group, side), ((lo, hi), pages) in inspect(fixtures[label], schema, groups, version).items():
            counts[version] += len(pages)
            lines.append(f'  checkLeaf (← load folder "{label}") {group} {side} ⟨{lo}, {hi}⟩ '
                         f'{json.dumps(PATHS[side])} {lst(pages)}')

    leading_anc = f".struct {site(1, ('payload',))}"
    leading_list = f".list {site(2, ('payload', 'nested'), False)} {location(3, ('payload', 'nested', 'list'))}"
    nested = site(4, ("payload", "nested", "list", "element"))
    identifier = site(5, ("payload", "id"), False)
    lines.extend([
        f'  checkTree (← load folder "leading_struct") {lst(map(EVENTS["field_term"], leading))} [1, 2, 3, 4, 5] '
        f'[⟨0, ⟨{nested}, .int32, [{leading_anc}, {leading_list}]⟩⟩, ⟨1, ⟨{identifier}, .int64, [{leading_anc}]⟩⟩]',
        '  let leading ← take (openFile {} (← load folder "leading_struct"))',
        '  let nested ← take (bindLeaf leading.schema 0 0)',
        '  let observed ← take (nested.read {})',
        '  unless nested.leaf.path.listPlan.isNone && observed.atoms == '
        '[⟨0, 0, none⟩, ⟨0, 3, some (.int32 3)⟩, ⟨1, 2, none⟩] do',
        '    throw (IO.userError "leading Struct definition or signed atoms differ")',
        '  refuse (bindLeaf leading.schema 0 1) (.representation 1)',
        '  refuse (openFile {} (← load folder "unsupported_double"))',
        '    (.original (.physical ⟨4, ["items", "list", "element", "a"]⟩ .double))',
    ])
    V2["run_lean"](folder, "RecursiveTreeCompiler.lean", lines)
    print(f"Checked {len(fixtures)} native carriers, {counts[1]} V1 and {counts[2]} V2 original leaf pages, "
          "ordered leaf ancestry, typed schema and depth refusals and the legacy nested-list gate")
    return NATIVE["fingerprints"](fixtures)


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert pins["producer"] == BASE["producer"]()
    with tempfile.TemporaryDirectory() as directory:
        assert pins["genuine_parquet"] == verify(Path(directory))


if __name__ == "__main__":
    main()
