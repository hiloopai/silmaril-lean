"""Check genuine PyArrow IPC through complete Lean Parquet and returned IPC."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FILE = runpy.run_path(str(HERE.parent / "parquet-recursive-file-writer-oracle/check.py"))
STREAM = runpy.run_path(str(HERE.parent / "arrow-recursive-stream-oracle/check.py"))
EOS = STREAM["EOS"]
lst, fingerprints = FILE["lst"], FILE["fingerprints"]


LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Defs

open Silmaril Silmaril.Formats
open Parquet.RecursiveSchema
open Parquet.RecursiveSchema.Repeated.Writer.FromIpc
open Arrow.RecursiveSchema.Stream (Trace Completed)

set_option maxRecDepth 4096

private def load (folder : System.FilePath) (name : String) : IO KBytes := do
  let bytes ← IO.FS.readBinFile (folder / (name ++ ".arrows"))
  return KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"unexpected refusal: {repr cause}")

private def poison (ipc : Arrow.RecursiveSchema.Batch.Limits) : Limits :=
  { ipc := ipc, parquet.maxGroups := 0, parquet.schema.maxFileBytes := 0 }

private def invalidCuts : Options := ⟨true, some []⟩

private def expectOpen (folder : System.FilePath) (name : String)
    (wanted : Arrow.RecursiveSchema.Error) : IO Unit := do
  match convert (poison {}) invalidCuts (← load folder name) with
  | .error (.openError actual) =>
    unless actual = wanted do throw (IO.userError s!"wrong open refusal for {name}: {repr actual}")
  | .error other => throw (IO.userError s!"wrong stage for {name}: {repr other}")
  | .ok _ => throw (IO.userError s!"unexpected Parquet for {name}")

private def expectTerminal (folder : System.FilePath) (name : String)
    (ipc : Arrow.RecursiveSchema.Batch.Limits) (wanted : Trace) : IO Unit := do
  match convert (poison ipc) invalidCuts (← load folder name) with
  | .error (.terminal actual) =>
    unless actual == wanted do throw (IO.userError s!"changed original prefix or cause for {name}: {repr actual}")
  | .error other => throw (IO.userError s!"wrong stage for {name}: {repr other}")
  | .ok _ => throw (IO.userError s!"unexpected Parquet for {name}")

private def expectWriter (folder : System.FilePath) (name : String)
    (limits : Limits) (options : Options) (wanted : Repeated.Writer.Error) : IO Unit := do
  match convert limits options (← load folder name) with
  | .error (.writer actual) =>
    unless actual = wanted do throw (IO.userError s!"wrong writer refusal for {name}: {repr actual}")
  | .error other => throw (IO.userError s!"wrong stage for {name}: {repr other}")
  | .ok _ => throw (IO.userError s!"unexpected Parquet for {name}")

private def expectCutCount (folder : System.FilePath) : IO Unit := do
  match convert {} invalidCuts (← load folder "nullable_multi") with
  | .error (.cutGroups 3 0) => pure ()
  | .error cause => throw (IO.userError s!"wrong cut count refusal: {repr cause}")
  | .ok _ => throw (IO.userError "accepted an incomplete cut vector")

private def roundTrip (folder : System.FilePath) (name : String) (options : Options)
    (wanted : Trace) : IO Unit := do
  let wire ← load folder name
  let original ← take (Arrow.RecursiveSchema.Stream.read {} wire)
  unless original == wanted do throw (IO.userError s!"original trace differs for {name}")
  let output ← take (convert {} options wire)
  let file ← take (Repeated.openFile {} output.bytes)
  let groups ← take (Repeated.Rows.readAll {} file.schema)
  unless file.schema.arrow == original.schema && groups == original.batches.map Completed.observed &&
      file.snapshot.groupCount == original.batches.length do
    throw (IO.userError s!"Parquet declarations or groups differ for {name}")
  let returned ← take (Repeated.Rows.ToIpc.convert {} {} file.schema)
  let again ← take (Arrow.RecursiveSchema.Stream.read {} returned)
  unless again.schema == original.schema && again.batches.map Completed.observed == groups do
    throw (IO.userError s!"returned IPC observations differ for {name}")
  IO.FS.writeBinFile (folder / (name ++ ".parquet")) output.bytes.data
  IO.FS.writeFile (folder / (name ++ ".extent"))
    s!"{output.footer.start} {output.footer.stop} {output.metadata.numRows} {output.metadata.rowGroups.length}"
  IO.FS.writeBinFile (folder / (name ++ ".returned.arrows")) returned.toByteArray

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture folder")
  let directory := System.FilePath.mk folder
"""


def ipc(schema, batches, *, legacy=False):
    sink = pa.BufferOutputStream()
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5, use_legacy_format=legacy)
    with pa.ipc.new_stream(sink, schema, options=options) as writer:
        for batch in batches:
            writer.write_batch(batch)
    return sink.getvalue().to_pybytes()


def fixtures(cases):
    genuine = {name: ipc(schema, [pa.RecordBatch.from_pylist(rows, schema=schema) for rows in groups])
               for name, (schema, groups, _) in cases.items()}
    nested = pa.schema([pa.field("outer", pa.list_(pa.field("inner", pa.list_(
        pa.field("value", pa.int32())))))])
    list_batch = pa.RecordBatch.from_pylist(
        [{"outer": [[-(2**31), None], [], None]}, {"outer": None}], schema=nested)
    genuine["nested_lists"] = ipc(nested, [list_batch])
    genuine["zero_width"] = ipc(pa.schema([]), [
        pa.RecordBatch.from_struct_array(pa.array([{}] * length, type=pa.struct([])))
        for length in (2, 0, 1)
    ])
    schema, _, _ = cases["nullable_multi"]
    genuine["legacy"] = ipc(schema, [], legacy=True)
    return genuine


def trace_term(observed, count, terminal):
    schema, schema_end, _, terms, _ = observed
    return f"⟨⟨{schema}⟩, {schema_end}, {lst(terms[:count])}, {terminal}⟩"


def edits_of(raw, observed):
    _, _, records, _, end = observed
    first, empty, late = records
    assert (first.rows, empty.rows, late.rows) == (3, 0, 2)
    assert late.start == empty.end and late.end == end
    index, actual = next((i, nulls) for i, (length, nulls) in enumerate(late.nodes) if 0 < nulls < length)
    edit = STREAM["BATCH"]["edit_record"]
    unaligned = bytearray(raw)
    struct.pack_into("<I", unaligned, late.start + 4, len(late.metadata) + 1)
    edits = {
        "late_null_count": (edit(raw, late, late.node_start + 16 * index + 8, "q", actual + 1),
                            2, late.start, f".rows (.source (.nullCount {index} {actual + 1} {actual}))"),
        "late_node_length": (edit(raw, late, late.node_start, "q", late.rows + 1),
                             2, late.start, f".batch (.nodeLength 0 {late.rows} {late.rows + 1})"),
        "late_truncated_body": (raw[:late.end - 1], 2, late.start, ".batch (.body (.malformed .truncated))"),
        "late_unaligned_metadata": (bytes(unaligned), 2, late.start, ".envelope (.malformed .metadataLength)"),
        "missing_eos": (raw[:-8], 3, end, ".envelope (.malformed .truncated)"),
        "trailing_byte": (raw + b"\0", 3, end, ".trailingBytes"),
        "legacy_at_eos": (raw[:-8] + struct.pack("<II", 8, 0), 3, end,
                          ".envelope (.unsupported .legacyFraming)"),
    }
    for data, _, cursor, _ in edits.values():
        assert data[:cursor] == raw[:cursor]
    return edits, {"eos_without_schema": EOS}


def options(checksum, cuts):
    if cuts is None:
        return f"⟨{str(checksum).lower()}, none⟩"
    pages = lst(lst(lst(map(str, leaf)) for leaf in group) for group in cuts)
    return f"⟨{str(checksum).lower()}, some {pages}⟩"


def check_returned(wire, schema, groups):
    reader = pa.ipc.open_stream(wire)
    assert reader.schema == schema
    batches = list(reader)
    assert [batch.num_rows for batch in batches] == [len(group) for group in groups]
    assert [batch.to_pylist() for batch in batches] == groups
    _, cursor = STREAM["metadata"](wire)
    for group in groups:
        record = STREAM["read_record"](wire, cursor)
        assert record.rows == len(group) and len(record.body) % 8 == 0
        cursor = record.end
    assert cursor + 8 == len(wire) and wire[cursor:] == EOS


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert platform.python_version() == pins["producer"]["cpython"]
    assert pa.__version__ == pins["producer"]["pyarrow"] and version("thrift") == pins["producer"]["thrift"]
    cases = FILE["fixtures"]()
    genuine = fixtures(cases)
    observed = {name: STREAM["observe"](pa, raw) for name, raw in genuine.items() if name != "legacy"}
    assert [record.rows for record in observed["zero_width"][2]] == [2, 0, 1]
    common = observed["nullable_multi"]
    edited, bad_open = edits_of(genuine["nullable_multi"], common)
    labeled = {name: item[0] for name, item in edited.items()} | bad_open
    plans = {name: (list(FILE["page_cuts"](schema, groups)) if name == "nullable_multi" else None)
             for name, (schema, groups, _) in cases.items()}

    with tempfile.TemporaryDirectory() as directory:
        folder = Path(directory)
        for name, raw in (genuine | labeled).items():
            (folder / f"{name}.arrows").write_bytes(raw)
        commands = [LEAN]
        for name, (_, groups, checksum) in cases.items():
            native = observed[name]
            trace = trace_term(native, len(groups), f".eos {len(groups)} {native[4]}")
            commands.append(f'  roundTrip directory "{name}" {options(checksum, plans[name])} {trace}')
        commands.extend([
            '  expectOpen directory "legacy" (.envelope (.unsupported .legacyFraming))',
            '  expectOpen directory "eos_without_schema" .expectedSchema',
        ])
        for name, (_, completed, offset, cause) in edited.items():
            trace = trace_term(common, completed, f".failed {completed} {offset} ({cause})")
            commands.append(f'  expectTerminal directory "{name}" {{}} {trace}')
        late_start = common[2][-1].start
        capped = "{ schema.ipc.batches := 2 }"
        batch_limit = trace_term(common, 2, f".failed 2 {late_start} .batchLimit")
        bad_envelope = trace_term(common, 2, f".failed 2 {late_start} (.envelope (.malformed .metadataLength))")
        commands.extend([
            f'  expectTerminal directory "nullable_multi" {capped} {batch_limit}',
            f'  expectTerminal directory "late_unaligned_metadata" {capped} {bad_envelope}',
            '  expectWriter directory "nested_lists" {} {} (.schema (.nestedList ["outer", "list", "inner"]))',
            '  expectWriter directory "zero_width" {} {} (.schema .emptyRoot)',
            '  expectWriter directory "nullable_multi" (poison {}) {} (.groups 3)',
            '  expectWriter directory "required_lists" {} ⟨false, some [[[999], [1], [1]]]⟩ (.cuts 0 0)',
            '  expectCutCount directory',
        ])
        driver = folder / "Check.lean"
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        "--run", str(driver), str(folder)], cwd=ROOT, check=True)

        parquet, returned = {}, {}
        for name, (schema, groups, checksum) in cases.items():
            parquet[name] = FILE["inspect"](folder / f"{name}.parquet", schema, groups, checksum, plans[name])
            returned[name] = (folder / f"{name}.returned.arrows").read_bytes()
            check_returned(returned[name], schema, groups)
        captured = {"genuine_ipc": fingerprints(genuine), "labeled_edits": fingerprints(labeled),
                    "lean_parquet": fingerprints(parquet), "returned_ipc": fingerprints(returned)}
        for kind, values in captured.items():
            assert values == pins[kind], f"{kind} fixture pins changed"
    print("Checked three complete round trips and sixteen typed stage refusals")


if __name__ == "__main__":
    main()
