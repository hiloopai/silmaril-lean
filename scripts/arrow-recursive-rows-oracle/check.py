"""Compare recursive logical rows against genuine pinned PyArrow IPC."""

import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = Path(__file__).with_name("fixtures.json")
SEMANTICS = runpy.run_path(str(ROOT / "scripts/arrow-recursive-semantics-oracle/check.py"))
BATCH = SEMANTICS["BATCH"]
metadata, read_record = (BATCH[key] for key in ("metadata", "read_record"))
require, fingerprint, bytes_term = (BATCH[key] for key in ("require", "fingerprint", "bytes_term"))

LEAN = """\
module

meta import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Defs

open Silmaril
open Silmaril.Formats.Arrow.RecursiveSchema.Batch (readFrame)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows

private meta def follows (input : KBytes) (expectedFirst : Observation)
    (expectedSecond : Except Error Observation) : Bool :=
  match readFirst {} input with
  | .error _ => false
  | .ok (first, observed) =>
    observed == expectedFirst &&
    match readFrame {} first.schema input first.batch.next with
    | .error _ => false
    | .ok second =>
      match decode second, expectedSecond with
      | .ok actual, .ok wanted => actual == wanted
      | .error actual, .error wanted => actual == wanted
      | _, _ => false

private meta def sees (input : KBytes) (wanted : Observation) : Bool :=
  match readFirst {} input with
  | .error _ => false
  | .ok (_, actual) => actual == wanted

private meta def refuses (input : KBytes) (wanted : Error) : Bool :=
  match readFirst {} input with
  | .error cause => cause == wanted
  | .ok _ => false
"""


def produce(pa):
    genuine = SEMANTICS["produce"](pa)
    batch = pa.ipc.open_stream(genuine["hidden"]).read_next_batch()
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, batch.schema) as stream:
        stream.write_batch(batch)
        stream.write_batch(batch)
    genuine["two_populated"] = sink.getvalue().to_pybytes()
    return genuine


def controls(genuine):
    earlier, padding = SEMANTICS["controls"](genuine["hidden"], genuine["four_level"])
    stream = genuine["two_populated"]
    _, start = metadata(stream)
    first = read_record(stream, start)
    second = read_record(stream, first.end)
    require(second.nodes[0] == (4, 1), "expected a later parent bitmap with one null")
    corrupt = BATCH["edit_record"](stream, second, second.node_start + 8, "q", 0)
    require(corrupt[:first.end] == stream[:first.end], "late edit touched the earlier batch")
    return earlier, padding, corrupt


def lean_list(items):
    return "[" + ", ".join(items) + "]"


def lean_cell(pa, kind, value):
    if value is None:
        return "none"
    if pa.types.is_struct(kind):
        fields = (lean_cell(pa, field.type, value[field.name]) for field in kind)
        return f"(some (.struct {lean_list(fields)}))"
    if pa.types.is_list(kind):
        children = (lean_cell(pa, kind.value_type, child) for child in value)
        return f"(some (.list {lean_list(children)}))"
    require(kind in (pa.int32(), pa.int64()), "unexpected signed type")
    return f"(some (.int{kind.bit_width} ({value})))"


def observe(pa, batch, record):
    # The producer has duplicate top-level names, so use PyArrow's positional
    # arrays and to_pylist instead of converting the row to a name-keyed dict.
    kinds = list(batch.schema.types)
    columns = [batch.column(i).to_pylist() for i in range(batch.num_columns)]
    require(batch.num_rows == record.rows and all(len(col) == record.rows for col in columns),
            "original row count and PyArrow differ")
    rows = ([col[i] for col in columns] for i in range(record.rows))
    encoded = lean_list(lean_list(lean_cell(pa, kind, value)
                                  for kind, value in zip(kinds, row, strict=True)) for row in rows)
    return f"⟨{record.rows}, {encoded}⟩"


def compare(pa, data):
    _, start = metadata(data)
    result = []
    for batch in pa.ipc.open_stream(data):
        record = read_record(data, start)
        SEMANTICS["positional"](pa, record, batch)  # Includes independent original-byte checks.
        result.append(observe(pa, batch, record))
        start = record.end
    return result


def checks(pa, genuine, edits, padding, late):
    for label, data in genuine.items():
        frames = compare(pa, data)
        require(len(frames) in (1, 2), "unexpected number of fixture batches")
        if label == "empty_schema":
            require(frames == ["⟨2, [[], []]⟩"], "expected two rows at width zero")
        yield f"#guard sees {bytes_term(data)} {frames[0]}"
        if len(frames) == 2:
            yield f"#guard follows {bytes_term(data)} {frames[0]} (.ok {frames[1]})"
        if label == "two_populated":
            yield f"#guard follows {bytes_term(late)} {frames[0]} (.error (.source (.nullCount 0 0 1)))"
        print(f"{label}: compared {len(frames)} positional logical batch(es)")
    hidden, = compare(pa, genuine["hidden"])
    require(compare(pa, padding) == [hidden], "bitmap padding changed PyArrow rows")
    yield f"#guard sees {bytes_term(padding)} {hidden}"
    for data, error in edits.values():
        yield f"#guard refuses {bytes_term(data)} (.source ({error}))"


def main():
    import pyarrow as pa

    pins = json.loads(MANIFEST.read_text(encoding="utf-8"))
    require(platform.python_implementation() == "CPython" and
            platform.python_version() == pins["producer"]["cpython"], "CPython pin differs")
    require(pa.__version__ == pins["producer"]["pyarrow"], "PyArrow pin differs")
    genuine = produce(pa)
    edits, padding, late = controls(genuine)
    require({name: fingerprint(data) for name, data in genuine.items()} == pins["genuine_ipc"],
            "genuine IPC pins differ")
    actual = {name: fingerprint(data) for name, (data, _) in edits.items()}
    actual["bitmap_padding"] = fingerprint(padding)
    actual["late_null_count"] = fingerprint(late)
    require(actual == pins["labeled_edits"], "labeled edit pins differ")
    with tempfile.TemporaryDirectory() as directory:
        driver = Path(directory) / "Check.lean"
        driver.write_text("\n".join([LEAN, *checks(pa, genuine, edits, padding, late)]), encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        str(driver)], cwd=ROOT, check=True)
    print(f"Checked {len(genuine)} genuine IPC pins, {len(actual)} labeled edits, and {len(edits) + 1} typed refusals")


if __name__ == "__main__":
    main()
