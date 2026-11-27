"""Compare recursive Arrow Events with pinned positional PyArrow IPC observations."""

import json
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = Path(__file__).with_name("fixtures.json")
STREAM = runpy.run_path(str(ROOT / "scripts/arrow-recursive-stream-oracle/check.py"))
ROWS, SCHEMA = STREAM["ROWS"], STREAM["SCHEMA"]
metadata, read_record = (STREAM[key] for key in ("metadata", "read_record"))
require, fingerprint, bytes_term = (STREAM[key] for key in ("require", "fingerprint", "bytes_term"))

LEAN = """\
module

meta import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Defs

open Silmaril Silmaril.Relational
open Silmaril.Formats.Arrow.RecursiveSchema (Field)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream (Error)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events

private meta def agrees (events : EventStream)
    (expected : List (Option String × Field))
    (batches : List Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Observation)
    (ending : Silmaril.Formats.Arrow.Events.Termination Error) : Bool :=
  match events with
  | .error _ => false
  | .ok ⟨source, trace⟩ =>
    declarations source == expected && trace.batches.map eraseBatch == batches &&
    decide (trace.termination = ending)

private meta def selection (source : Signature) (positions : List Nat) : Scan.Projection source :=
  Scan.Projection.ofArray ((positions.filterMap fun index =>
    if valid : index < source.width then some ⟨index, valid⟩ else none).toArray)

private meta def projects (input : KBytes) (positions : List Nat) :=
  readProjected {} input (fun source => selection source positions)

private meta def composed (input : KBytes) (first second : List Nat) :=
  readProjected {} input (fun source =>
    let projection := selection source first
    projection.comp (selection projection.schema second))

private meta def failsAtOpen (input : KBytes) (wanted : Error) : Bool :=
  match read {} input, projects input [] with
  | .error original, .error afterProject => original == wanted && afterProject == wanted
  | _, _ => false
"""


def produce(pa):
    fixtures = STREAM["produce"](pa)
    kind = pa.list_(pa.field("element", pa.int64()))
    schema = pa.schema([pa.field("", kind, nullable=False)])
    values = pa.array([[-2**63, None], [], [2**63 - 1]], type=kind)
    batch = pa.record_batch([values], schema=schema)
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema) as writer:
        writer.write_batch(batch)
    fixtures["empty_name"] = sink.getvalue().to_pybytes()
    return fixtures


def controls(fixtures):
    genuine = fixtures["empty_name"]
    data, _ = metadata(genuine)
    fields, count = SCHEMA["root_vector"](data)
    require(count == 1, "expected one top-level field")
    root = SCHEMA["target"](data, fields)
    child, _ = SCHEMA["vector"](data, root, 5)
    child = SCHEMA["target"](data, child)
    vtable = root - struct.unpack_from("<i", data, root)[0]
    require(vtable != child - struct.unpack_from("<i", data, child)[0], "shared Field vtable")
    require(SCHEMA["slot"](data, root, 0) is not None, "producer omitted the explicit empty name")
    absent = bytearray(genuine)
    struct.pack_into("<H", absent, 8 + vtable + 4, 0)
    changed, _ = metadata(absent)
    require(SCHEMA["slot"](changed, root, 0) is None and
            SCHEMA["slot"](changed, child, 0) == SCHEMA["slot"](data, child, 0),
            "expected exactly the original top-level name reference to be absent")

    source_edits = STREAM["controls"](fixtures)
    return {"absent_name": bytes(absent),
            "late_null_count": source_edits["late_null_count"],
            "legacy_at_eos": source_edits["legacy_at_eos"]}


def lean_declaration(pa, field, absent=False):
    name = "none" if absent else f"(some {json.dumps(field.name, ensure_ascii=False)})"
    term = SCHEMA["field_term"](SCHEMA["pyarrow_field"](pa, field))
    if absent:
        require(term.startswith('.node (some "") '), "expected an explicit empty producer name")
        term = term.replace('.node (some "") ', ".node none ", 1)
    return f"({name}, {term})"


def observations(pa, data, positions=None, *, limit=None, absent=False):
    reader = pa.ipc.open_stream(data)
    fields = list(reader.schema)
    positions = list(range(len(fields))) if positions is None else positions
    require(all(0 <= i < len(fields) for i in positions), "projection out of bounds")
    labels = ROWS["lean_list"](lean_declaration(pa, fields[i], absent and i == 0) for i in positions)
    _, cursor = metadata(data)
    batches = []
    for batch in reader:
        if limit is not None and len(batches) == limit:
            break
        record = read_record(data, cursor)
        ROWS["SEMANTICS"]["positional"](pa, record, batch)
        values = [batch.column(i).to_pylist() for i in positions]
        row_count = record.rows
        require(batch.num_rows == row_count, "original row count differs")
        rows = ROWS["lean_list"](
            ROWS["lean_list"](ROWS["lean_cell"](pa, fields[i].type, col[row])
                              for i, col in zip(positions, values, strict=True))
            for row in range(row_count)
        )
        batches.append(f"⟨{row_count}, {rows}⟩")
        cursor = record.end
    return labels, ROWS["lean_list"](batches), len(batches), cursor


def guard(call, expected, ending=".eos"):
    return f"#guard agrees ({call}) {expected[0]} {expected[1]} ({ending})"


def checks(pa, fixtures, edits):
    for label, data in fixtures.items():
        if label == "legacy":
            yield f"#guard failsAtOpen {bytes_term(data)} (.schema (.envelope (.unsupported .legacyFraming)))"
            continue
        expected = observations(pa, data)
        require(data[expected[3]:] == STREAM["EOS"], "expected exact original EOS")
        yield guard(f"read {{}} {bytes_term(data)}", expected)
        print(f"{label}: {expected[2]} positional Events batches")

    data = fixtures["four_level"]
    repeated = [3, 1, 1, 0]
    for indices in (repeated, [], [0, 1, 2, 3]):
        yield guard(f"projects {bytes_term(data)} {indices}", observations(pa, data, indices))
    yield guard(f"composed {bytes_term(data)} {repeated} [2, 3, 1]", observations(pa, data, [1, 0, 1]))

    genuine_name = fixtures["empty_name"]
    absent = edits["absent_name"]
    yield guard(f"read {{}} {bytes_term(absent)}", observations(pa, genuine_name, absent=True))
    yield guard(f"projects {bytes_term(absent)} [0, 0]",
                observations(pa, genuine_name, [0, 0], absent=True))

    good = fixtures["two_populated"]
    late = edits["late_null_count"]
    for indices in (None, [2, 2], []):
        expected = observations(pa, good, indices, limit=1)
        fault = f".readError (.failed 1 {expected[3]} (.rows (.source (.nullCount 0 0 1))))"
        call = f"read {{}} {bytes_term(late)}" if indices is None else f"projects {bytes_term(late)} {indices}"
        yield guard(call, expected, fault)

    expected = observations(pa, good, [])
    fault = f".readError (.failed 2 {expected[3]} (.envelope (.unsupported .legacyFraming)))"
    yield guard(f"projects {bytes_term(edits['legacy_at_eos'])} []", expected, fault)


def main():
    import pyarrow as pa

    pins = json.loads(MANIFEST.read_text(encoding="utf-8"))
    require(platform.python_implementation() == "CPython" and
            platform.python_version() == pins["producer"]["cpython"], "CPython pin differs")
    require(pa.__version__ == pins["producer"]["pyarrow"], "PyArrow pin differs")
    fixtures = produce(pa)
    edits = controls(fixtures)
    require({name: fingerprint(data) for name, data in fixtures.items()} == pins["genuine_ipc"],
            "genuine IPC pins differ")
    require({name: fingerprint(data) for name, data in edits.items()} == pins["labeled_edits"],
            "labeled edit pins differ")
    with tempfile.TemporaryDirectory() as directory:
        driver = Path(directory) / "Check.lean"
        driver.write_text("\n".join([LEAN, *checks(pa, fixtures, edits)]), encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        str(driver)], cwd=ROOT, check=True)
    print(f"Checked {len(fixtures)} genuine IPC pins, {len(edits)} labeled edits, and 18 Events comparisons")


if __name__ == "__main__":
    main()
