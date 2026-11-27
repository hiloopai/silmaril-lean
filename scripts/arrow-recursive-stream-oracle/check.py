"""Compare native recursive V5 stream traces with pinned PyArrow IPC."""

import json
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = Path(__file__).with_name("fixtures.json")
ROWS = runpy.run_path(str(ROOT / "scripts/arrow-recursive-rows-oracle/check.py"))
BATCH = ROWS["BATCH"]
SCHEMA = BATCH["SCHEMA_ORACLE"]
metadata, read_record = (BATCH[key] for key in ("metadata", "read_record"))
require, fingerprint, bytes_term = (BATCH[key] for key in ("require", "fingerprint", "bytes_term"))
EOS = struct.pack("<II", 0xffffffff, 0)

LEAN = """\
module

meta import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Defs

open Silmaril
open Silmaril.Formats.Arrow.RecursiveSchema (Schema)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream

private meta def sees (limits : Silmaril.Formats.Arrow.RecursiveSchema.Batch.Limits)
    (input : KBytes) (wanted : Trace) : Bool :=
  match readTrace limits input with
  | .error _ => false
  | .ok trace =>
    trace == wanted &&
    match wanted.terminal, read limits input with
    | .eos .., .ok checked => checked == trace
    | .failed ordinal offset cause, .error failure => failure == .failed ordinal offset cause
    | _, _ => false

private meta def openFails (limits : Silmaril.Formats.Arrow.RecursiveSchema.Batch.Limits)
    (input : KBytes) (wanted : Silmaril.Formats.Arrow.RecursiveSchema.Error) : Bool :=
  match readTrace limits input, read limits input with
  | .error original, .error wrapped => original == wanted && wrapped == .schema wanted
  | _, _ => false
"""


def produce(pa):
    fixtures = ROWS["produce"](pa)
    schema = pa.ipc.open_stream(fixtures["four_level"]).schema
    fixtures["schema_only"] = SCHEMA["stream"](pa, schema)

    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, pa.schema([])) as stream:
        for rows in (2, 0, 1):
            records = pa.array([{}] * rows, type=pa.struct([]))
            stream.write_batch(pa.RecordBatch.from_struct_array(records))
    fixtures["zero_width_multi"] = sink.getvalue().to_pybytes()
    fixtures["legacy"] = SCHEMA["fixtures"](pa)[0]["legacy"]
    return fixtures


def controls(fixtures):
    _, _, late_null_count = ROWS["controls"](fixtures)
    stream = fixtures["two_populated"]
    _, start = metadata(stream)
    first = read_record(stream, start)
    second = read_record(stream, first.end)
    require(second.end + 8 == len(stream) and stream[second.end:] == EOS, "expected exact producer EOS")
    bad_node = BATCH["edit_record"](stream, second, second.node_start, "q", 5)
    odd_length = bytearray(stream)
    struct.pack_into("<I", odd_length, second.start + 4, len(second.metadata) + 1)
    return {
        "late_null_count": late_null_count,
        "late_node_length": bad_node,
        "late_truncated_body": stream[:second.end - 1],
        "late_unaligned_metadata": bytes(odd_length),
        "missing_eos": stream[:-8],
        "trailing_byte": stream + b"\0",
        "legacy_at_eos": stream[:-8] + struct.pack("<II", 8, 0),
        "eos_without_schema": stream[-8:],
    }


def observe(pa, raw):
    arrow = pa.ipc.open_stream(raw)
    schema = SCHEMA["fields_term"]([SCHEMA["pyarrow_field"](pa, field) for field in arrow.schema])
    _, cursor = metadata(raw)
    schema_end = cursor
    records, terms = [], []
    for ordinal, batch in enumerate(arrow):
        record = read_record(raw, cursor)
        ROWS["SEMANTICS"]["positional"](pa, record, batch)
        values = ROWS["observe"](pa, batch, record)
        terms.append(f"⟨{ordinal}, {cursor}, {len(record.metadata)}, {len(record.body)}, {values}⟩")
        records.append(record)
        cursor = record.end
    require(raw[cursor:] == EOS, "expected the original exact modern EOS")
    return schema, schema_end, records, terms, cursor


def trace(data, observation, completed, terminal, limits="{}"):
    schema, schema_end, _, terms, _ = observation
    batches = ROWS["lean_list"](terms[:completed])
    return f"#guard sees {limits} {bytes_term(data)} ⟨⟨{schema}⟩, {schema_end}, {batches}, {terminal}⟩"


def refused(data, observation, complete, cursor, cause, limits="{}"):
    return trace(data, observation, complete, f".failed {complete} {cursor} ({cause})", limits)


def open_fails(data, cause, limits="{}"):
    return f"#guard openFails {limits} {bytes_term(data)} ({cause})"


def limit(setting):
    return "{ schema := { ipc := { " + setting + " } } }"


def checks(pa, fixtures, edits):
    observations = {}
    for label, data in fixtures.items():
        if label == "legacy":
            yield open_fails(data, ".envelope (.unsupported .legacyFraming)")
            continue
        observed = observe(pa, data)
        observations[label] = observed
        records, end = observed[2], observed[4]
        yield trace(data, observed, len(records), f".eos {len(records)} {end}")
        print(f"{label}: row counts {[record.rows for record in records]}, exact EOS at {end}")

    yield open_fails(edits["eos_without_schema"], ".expectedSchema")
    populated = observations["two_populated"]
    first, second = populated[2]
    for label, cause in {
        "late_null_count": ".rows (.source (.nullCount 0 0 1))",
        "late_node_length": ".batch (.nodeLength 0 4 5)",
        "late_truncated_body": ".batch (.body (.malformed .truncated))",
        "late_unaligned_metadata": ".envelope (.malformed .metadataLength)",
    }.items():
        require(edits[label][:first.end] == fixtures["two_populated"][:first.end], "late edit changed prefix")
        yield refused(edits[label], populated, 1, second.start, cause)
    for label, cause in {
        "missing_eos": ".envelope (.malformed .truncated)",
        "trailing_byte": ".trailingBytes",
        "legacy_at_eos": ".envelope (.unsupported .legacyFraming)",
    }.items():
        yield refused(edits[label], populated, 2, second.end, cause)

    schema_only = observations["schema_only"]
    yield trace(fixtures["schema_only"], schema_only, 0, f".eos 0 {schema_only[4]}", limit("batches := 0"))
    data = fixtures["four_level"]
    nested = observations["four_level"]
    positive, empty = nested[2]
    yield trace(data, nested, 2, f".eos 2 {empty.end}", limit("batches := 2"))
    yield refused(data, nested, 0, positive.start, ".batchLimit", limit("batches := 0"))
    yield refused(data, nested, 1, empty.start, ".batchLimit", limit("batches := 1"))
    yield refused(edits["late_unaligned_metadata"], populated, 1, second.start,
                  ".envelope (.malformed .metadataLength)", limit("batches := 1"))
    yield refused(data, nested, 0, positive.start, ".batch (.metadata (.limit .rows))", limit("rows := 3"))
    yield refused(data, nested, 0, positive.start, ".batch (.body (.limit .bodyBytes))",
                  limit(f"bodyBytes := {len(positive.body) - 1}"))
    yield refused(data, nested, 0, positive.start, ".batch (.slots 0)", "{ slots := 0 }")
    schema_bytes, _ = metadata(data)
    fields_first, _ = SCHEMA["root_vector"](schema_bytes)
    yield open_fails(data, f".fields {SCHEMA['target'](schema_bytes, fields_first)}", limit("fields := 0"))

    zero = observations["zero_width_multi"]
    require([record.rows for record in zero[2]] == [2, 0, 1], "width-zero sequence lost")
    schema_size = zero[1] - 8
    require(len(zero[2][0].metadata) > schema_size, "expected larger record metadata than schema")
    yield refused(fixtures["zero_width_multi"], zero, 0, zero[1], ".envelope (.limit .metadataBytes)",
                  limit(f"metadataBytes := {schema_size}"))


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
    print(f"Checked {len(fixtures)} genuine IPC pins, {len(edits)} labeled edits, and 17 typed refusals")


if __name__ == "__main__":
    main()
