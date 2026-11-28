"""Check both strict IPC bridges on the optional TwoListStruct profile."""

import json
from pathlib import Path
import runpy
import struct
import subprocess
import tempfile

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
IMPORT = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-from-ipc-oracle/check.py"))
OPTIONAL = runpy.run_path(str(HERE.parent / "parquet-recursive-two-list-struct-optional-element-oracle/check.py"))
WRITER, FORWARD, STREAM, BRIDGE = (IMPORT[key] for key in ("WRITER", "FORWARD", "STREAM", "BRIDGE"))
EVENTS, NATIVE = FORWARD["EVENTS"], OPTIONAL["NATIVE"]
fingerprints = NATIVE["fingerprints"]


RETURN_PARQUET = """\
private def returnParquet (folder : System.FilePath) (label : String)
    (schema : Arrow.RecursiveSchema.Schema) (batches : List Observation) : IO Unit := do
  let bytes ← IO.FS.readBinFile (folder / (label ++ "_field.arrow"))
  let wire := Silmaril.KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)
  let output ← take (Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.convert {} wire true)
  let opened ← take (Parquet.RecursiveSchema.TwoListStruct.openFile {} output.bytes)
  let read ← take (Parquet.RecursiveSchema.TwoListStruct.Reader.readAll {} opened.schema)
  unless opened.schema.plan.arrow == schema && opened.snapshot.groupCount == batches.length && read == batches do
    throw (IO.userError "full-field Parquet round trip differs")
  IO.FS.writeBinFile (folder / (label ++ ".returned.parquet")) output.bytes.data
"""


def hidden_required_case(schema):
    outer = schema.field(0)
    inner = outer.type.value_field
    element = inner.type.value_field
    left, right = element.type
    assert element.nullable and not left.nullable and not right.nullable
    assert (left.type, right.type) == (pa.int64(), pa.int32())
    left_words = (4123, -2**63, -9123)
    right_words = (9234, 2**31 - 1, -4234)
    pairs = pa.StructArray.from_arrays(
        [pa.array(left_words, type=left.type), pa.array(right_words, type=right.type)],
        fields=[left, right], mask=pa.array([True, False, True]),
    )
    inside = pa.ListArray.from_arrays([0, 3], pairs, type=inner.type)
    outside = pa.ListArray.from_arrays([0, 1], inside, type=outer.type)
    raw = BRIDGE["ipc"](schema, [pa.RecordBatch.from_arrays([outside], schema=schema)])
    _, start = STREAM["metadata"](raw)
    record = STREAM["read_record"](raw, start)
    assert record.nodes[-3:] == [(3, 2), (3, 0), (3, 0)]
    assert len(record.buffers) == 9
    valid, extent = record.buffers[4]
    assert extent == 1 and record.body[valid] & 7 == 2
    for index, fmt, expected in ((6, "<3q", left_words), (8, "<3i", right_words)):
        at, extent = record.buffers[index]
        assert extent == struct.calcsize(fmt) and struct.unpack_from(fmt, record.body, at) == expected
    rows = [[[None, {left.name: left_words[1], right.name: right_words[1]}, None]]]
    return raw, [rows]


def import_cases(folder):
    cases = list(WRITER["cases"](optional_element=True))
    common = "renamed_no_crc_empty_group"
    positives = [(label, schema, [groups[0], [], [None, groups[2][-1]]] if label == common else groups, crc)
                 for label, schema, groups, crc in cases]
    schema = next(schema for label, schema, _, _ in cases if label == "32_64_1000")
    positives.append(("optional_struct", schema, [[[[None]]]], True))
    hidden_schema = next(schema for label, schema, _, _ in cases if label == "64_32_0000")
    hidden_raw, hidden = hidden_required_case(hidden_schema)
    positives.append(("hidden_required_values", hidden_schema, hidden, True))
    genuine, observed, code = IMPORT["prepare_cases"](positives, {"hidden_required_values": hidden_raw})
    raw, original = genuine[common], observed[common]
    edits, _ = BRIDGE["edits_of"](raw, original)
    edits["second_eos"] = (raw + STREAM["EOS"], 3, original[4], ".trailingBytes")
    authored = {}
    for label, (wire, count, at, cause) in edits.items():
        authored[label] = wire
        trace = BRIDGE["trace_term"](original, count, f".failed {count} {at} ({cause})")
        code.append(f'  expectTerminal directory "{label}" {{}} {trace}')
    cap = BRIDGE["trace_term"](original, 2, f".failed 2 {original[2][-1].start} .batchLimit")
    code.extend([
        f'  expectTerminal directory "{common}" {{ schema.ipc.batches := 2 }} {cap}',
        f'  expectWriter directory "{common}" (exhausted {{}}) (.groupLimit 3)',
        f'  expectWriter directory "{common}" {{ parquet.chunk.maxBodyBytes := 0 }} (.column 0 .left (.bodyLimit 0))',
    ])
    parquet, returned = IMPORT["run_cases"](folder, genuine | authored, positives, code)
    pages = 2 * sum(len(groups) for _, _, groups, _ in positives)
    print(f"Imported {len(genuine)} genuine optional V5 streams into {pages} V1 pages, "
          f"checked {len(returned)} selected IPC returns and {len(edits) + 3} typed controls")
    return {key: fingerprints(value) for key, value in {
        "genuine_ipc": genuine, "authored_ipc": authored, "imported_parquet": parquet, "returned_ipc": returned,
    }.items()}


def export_cases(folder):
    genuine, reframe, damaged, cause = OPTIONAL["fixtures"]()
    schema, groups, wire = genuine["optional_1111"]
    empty = EVENTS["physical_empty"](wire)
    schema_only = NATIVE["write"](schema, [])
    _, renamed_schema, renamed_groups, _ = next(
        case for case in WRITER["cases"](optional_element=True) if case[0] == "renamed_no_crc_empty_group"
    )
    renamed_rows = [renamed_groups[0]]
    renamed = NATIVE["write"](renamed_schema, renamed_rows, use_compliant_nested_type=False, write_page_checksum=False)
    genuine |= {"schema_only": (schema, [], schema_only), "renamed_no_crc": (renamed_schema, renamed_rows, renamed)}
    positives = genuine | {"independent_cuts": (schema, groups, reframe),
                           "physical_empty": (schema, [groups[0], [], groups[1]], empty)}
    authored = {"independent_cuts": reframe, "physical_empty": empty, "late_struct_presence": damaged}
    for label, data in {key: case[2] for key, case in genuine.items()}.items():
        (folder / f"{label}.parquet").write_bytes(data)
    for label, data in authored.items():
        (folder / f"{label}.parquet").write_bytes(data)

    additional_import = "Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.Defs"
    source = FORWARD["LEAN"].replace("module\n", f"module\n\nimport {additional_import}\nmeta import {additional_import}\n")
    code = [source.replace("public def main", RETURN_PARQUET + "\npublic def main")]
    pages = 0
    for label, (decl, values, original) in positives.items():
        _, columns = NATIVE["inspect"](original, decl, values, checksums=label != "renamed_no_crc")
        pages += sum(len(frames) for _, frames in columns.values())
        batches = FORWARD["batches_term"](decl, IMPORT["rows_for"](decl, values))
        code.append(f'  checkIpc folder "{label}" {FORWARD["fields_term"](decl)} {batches}')
        fields = NATIVE["lst"](EVENTS["field_term"](field) for field in decl)
        code.append(f'  returnParquet folder "{label}" ⟨{fields}⟩ {batches}')

    prefix = FORWARD["batches_term"](schema, IMPORT["rows_for"](schema, groups[:1]))
    code.append(f'  sourceFailure (← load folder "late_struct_presence") {prefix} (.group 1 ({cause}))')
    for selection in ("field", "empty"):
        code.append(f'  writerFailure (← load folder "physical_empty") .{selection} {{ schema.ipc.batches := 2 }} '
                    '(.batchLimit 3 2)')
    driver = folder / "OptionalElementToIpc.lean"
    driver.write_text("\n".join(code) + "\n", encoding="utf-8")
    subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                    "--run", str(driver), str(folder)], cwd=ROOT, check=True)

    emitted, returned = {}, {}
    for label, (decl, values, _) in positives.items():
        returned[label] = (folder / f"{label}.returned.parquet").read_bytes()
        WRITER["inspect"](returned[label], decl, values, True)
        for selection, projected in (("field", decl), ("empty", pa.schema([]))):
            name = f"{label}_{selection}"
            emitted[name] = (folder / f"{name}.arrow").read_bytes()
            FORWARD["inspect_ipc"](emitted[name], projected, IMPORT["rows_for"](decl, values))
    for selection in ("field", "empty"):
        assert emitted[f"optional_1111_{selection}"] == emitted[f"independent_cuts_{selection}"]
    print(f"Exported {len(positives)} optional sources with {pages} original pages to {len(emitted)} exact IPC streams, "
          f"checked {len(returned)} full-field Parquet returns, the late presence refusal and two writer limits")
    return {key: fingerprints(value) for key, value in {
        "genuine_parquet": {label: case[2] for label, case in genuine.items()}, "authored_parquet": authored,
        "exported_ipc": emitted, "returned_parquet": returned,
    }.items()}


def verify(folder):
    imports, exports = folder / "import", folder / "export"
    imports.mkdir()
    exports.mkdir()
    return import_cases(imports) | export_cases(exports)


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert WRITER["producer"]() == pins["producer"]
    with tempfile.TemporaryDirectory() as directory:
        assert verify(Path(directory)) == {key: data for key, data in pins.items() if key != "producer"}


if __name__ == "__main__":
    main()
