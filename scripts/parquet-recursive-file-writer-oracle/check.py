"""Inspect complete Lean-generated recursive Parquet files with PyArrow and Thrift."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ROWS = runpy.run_path(str(HERE.parent / "parquet-recursive-repeated-rows-oracle/check.py"))
CHUNK = ROWS["CHUNK"]
SCHEMA = ROWS["SCHEMA"]
THRIFT, MIXED, fingerprints, lst = (
    SCHEMA[key] for key in ("THRIFT", "MIXED", "fingerprints", "lst")
)
ARROW = ROWS["ARROW"]["BATCH"]["SCHEMA_ORACLE"]


LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Defs

open Silmaril Silmaril.Formats
open Parquet.RecursiveSchema.Repeated.Writer

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"unexpected refusal: {repr cause}")

private def deny {ε α : Type} [DecidableEq ε] [Repr ε] (wanted : ε) (result : Except ε α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"accepted input expecting {repr wanted}")
  | .error actual =>
    unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")

private def flat : Arrow.RecursiveSchema.Schema := ⟨[.node (some "v") false .int32 []]⟩
private def nestedList : Arrow.RecursiveSchema.Schema :=
  ⟨[.node (some "outer") true .list [.node (some "inner") true .list flat.fields]]⟩

private def controls : IO Unit := do
  let signed : Group := ⟨⟨1, [[some (.int32 (-7))]]⟩, none⟩
  let input : Input := ⟨flat, [signed, signed], false⟩
  deny (.schema .emptyRoot) (emit {} { input with schema := ⟨[]⟩ })
  deny (.schema (.missingName [])) (emit {} { input with schema := ⟨[.node none true .int64 []]⟩ })
  deny (.schema (.duplicate ["v"])) (emit {} { input with schema.fields := flat.fields ++ flat.fields })
  deny (.schema (.arity ["g"] .struct 0))
    (emit {} { input with schema := ⟨[.node (some "g") true .struct []]⟩ })
  deny (.schema (.arity ["ls"] .list 0))
    (emit {} { input with schema := ⟨[.node (some "ls") false .list []]⟩ })
  deny (.schema (.arity ["bad"] .int64 1))
    (emit {} { input with schema := ⟨[.node (some "bad") false .int64 flat.fields]⟩ })
  deny (.schema (.nestedList ["outer", "list", "inner"])) (emit {} { input with schema := nestedList })
  deny (.schema (.depth [])) (emit { schema.snapshot.maxSchemaDepth := 1 } input)
  deny (.schema .fieldLimit) (emit { schema.maxFields := 1 } input)
  deny (.schema (.nameBudget [])) (emit { schema.snapshot.footer.compact.maxBinaryBytes := 5 } input)
  deny (.groups 2) (emit { maxGroups := 1 } input)
  deny (.totalRows 2) (emit { maxTotalRows := 1 } input)
  deny (.rowCount 1 2 1) (emit {} { input with groups := [signed, { signed with data.rowCount := 2 }] })
  deny (.rows 0 1) (emit { rows.chunk.maxRows := 0 } input)
  deny (.columns 1) (emit { rows.maxColumns := 0 } input)
  deny (.projection 1 0)
    (emit {} { input with groups := [signed, { signed with data.rows := [[some (.int64 3)]] }] })
  deny (.projection 0 0)
    (emit {} { input with groups := [{ signed with data.rows := [[none]] }] })
  deny (.cutWidth 0 1 0) (emit {} { input with groups := [{ signed with cuts := some [] }] })
  deny (.cuts 1 0) (emit {} { input with groups := [signed, { signed with cuts := some [[2]] }] })
  deny (.cuts 0 0) (emit {} { input with groups := [{ signed with cuts := some [[0]] }] })
  deny (.slots 0 0 1) (emit { rows.maxSlots := 0 } input)
  deny (.totalSlots 1 0 2) (emit { maxTotalSlots := 1 } input)
  deny (.chunk 1 0 (.pageLimit 1 0)) (emit { maxTotalPages := 1 } input)
  let output ← take (emit {} input)
  let tight ← take (emit {
    schema.maxFileBytes := output.bytes.length, maxTotalPages := 2, maxTotalSlots := 2, maxTotalRows := 2 } input)
  unless tight.bytes = output.bytes do throw (IO.userError "exact cumulative limits changed the file")
  deny (.footer (.compact .byteLimit)) (emit { schema.maxFileBytes := output.bytes.length - 1 } input)
  deny (.chunk 1 0 (.page 0 (.limit .chunk)))
    (emit { schema.maxFileBytes := output.footer.start + 7 } input)

private def write (folder : System.FilePath) (name : String) (input : Input) : IO Unit := do
  let output ← take (emit {} input)
  IO.FS.writeBinFile (folder / (name ++ ".parquet")) output.bytes.data
  IO.FS.writeFile (folder / (name ++ ".extent"))
    s!"{output.footer.start} {output.footer.stop} {output.metadata.numRows} {output.metadata.rowGroups.length}"

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected output folder")
  let directory := System.FilePath.mk folder
"""


def leaf_paths(field, parent=()):
    path = parent + (field.name,)
    if pa.types.is_list(field.type):
        yield from leaf_paths(field.type.value_field, path + ("list",))
    elif pa.types.is_struct(field.type):
        for child in field.type:
            yield from leaf_paths(child, path)
    else:
        yield path


def fixtures():
    _, samples, _ = SCHEMA["fixtures"]()
    nested, nested_rows = samples["nullable_lists"]
    required, required_rows = samples["required_lists"]
    cases = {
        "nullable_multi": (nested, [nested_rows[:3], [], nested_rows[3:]], True),
        "required_lists": (required, [required_rows], False),
        "schema_only": (pa.schema([pa.field("", pa.int32(), nullable=False),
                                   pa.field("présent", pa.list_(pa.field("entry", pa.int64())))]), [], False),
    }
    return cases


def page_cuts(schema, groups):
    paths = [path for field in schema for path in leaf_paths(field)]
    for group, rows in enumerate(groups):
        cuts = []
        for column, path in enumerate(paths):
            field = schema.field(path[0])
            events = [event for row in rows
                      for event in CHUNK["from_arrow"](row[path[0]], field, path[1:])]
            if group == 2 and column in (0, 1):
                cut = column + 1
                assert events[cut][0] == 1
                cuts.append([cut, len(events) - cut])
            else:
                cuts.append([len(events)])
        yield cuts


def term(schema, groups, checksum, cuts):
    fields = ARROW["fields_term"]([ARROW["pyarrow_field"](pa, field) for field in schema])
    group_terms = []
    for ordinal, rows in enumerate(groups):
        observed = ROWS["expected_observation"](schema, rows)
        sizes = "none" if cuts is None else f"(some {lst(lst(map(str, leaf)) for leaf in cuts[ordinal])})"
        group_terms.append(f"⟨{observed}, {sizes}⟩")
    return f"⟨⟨{fields}⟩, {lst(group_terms)}, {str(checksum).lower()}⟩"


def inspect(path, schema, groups, checksum, cuts):
    wire = path.read_bytes()
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow == schema
    assert parquet.num_row_groups == len(groups)
    assert [parquet.read_row_group(i).to_pylist() for i in range(len(groups))] == groups
    rows = [row for group in groups for row in group]
    assert wire[:4] == wire[-4:] == b"PAR1"
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - footer_size
    assert [int(value) for value in path.with_suffix(".extent").read_text().split()] == [
        footer_start, len(wire) - 8, len(rows), len(groups)
    ]
    footer = MIXED["metadata"](wire)
    assert footer[3][1] == len(rows)
    groups_meta = THRIFT["list_field"](footer, 4)
    cursor = 4
    columns = list(CHUNK["capture"](wire, schema, rows, checksum))
    for column in columns:
        assert column.start == cursor
        cursor = column.stop
        if cuts is not None:
            assert [len(page.events) for page in column.pages] == cuts[column.group][column.index]
        if not groups[column.group]:
            assert len(column.pages) == 1 and column.pages[0].events == []
    assert cursor == footer_start
    for group, (expected, metadata) in enumerate(zip(groups, groups_meta, strict=True)):
        size = sum(column.stop - column.start for column in columns if column.group == group)
        assert metadata[2][1] == size and metadata[3][1] == len(expected)
    if cuts is not None:
        one, two = [column for column in columns if column.group == 2][:2]
        assert one.pages[1].events[0][0] == two.pages[1].events[0][0] == 1
        assert one.pages[1].before[0] != two.pages[1].before[0]
    print(f"{path.stem}: row groups {list(map(len, groups))}, {len(columns)} chunks, "
          f"{sum(len(column.pages) for column in columns)} frames")
    return wire


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert platform.python_version() == pins["producer"]["cpython"]
    assert pa.__version__ == pins["producer"]["pyarrow"]
    assert version("thrift") == pins["producer"]["thrift"]
    cases = fixtures()
    plans = {name: (list(page_cuts(schema, groups)) if name == "nullable_multi" else None)
             for name, (schema, groups, _) in cases.items()}
    with tempfile.TemporaryDirectory() as temporary:
        folder = Path(temporary)
        driver = folder / "Write.lean"
        commands = [LEAN, "  controls"]
        for name, sample in cases.items():
            commands.append(f'  write directory "{name}" {term(*sample, plans[name])}')
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        "--run", str(driver), str(folder)], cwd=ROOT, check=True)
        outputs = {name: inspect(folder / f"{name}.parquet", *sample, plans[name])
                   for name, sample in cases.items()}
        assert fingerprints(outputs) == pins["lean_parquet"]
    print("Checked complete native Lean files and 25 typed refusals")


if __name__ == "__main__":
    main()
