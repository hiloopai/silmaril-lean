"""Check native Lean recursive streams against PyArrow and original byte cursors."""

import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MANIFEST = HERE / "fixtures.json"
BATCH_WRITER = runpy.run_path(str(ROOT / "scripts/arrow-recursive-batch-writer-oracle/check.py"))
require, fingerprint, read_record, raw_schema, eos, columns, check_record = (
    BATCH_WRITER[key] for key in
    ("require", "fingerprint", "read_record", "raw_schema", "eos", "columns", "check_record")
)


def produce(pa):
    previous = BATCH_WRITER["produce"](pa)
    sources = {name: previous[name] for name in
               ("four_level", "hidden", "zero_width_multi", "schema_only")}
    # Repeated root and Struct child names, an explicit empty batch,
    # and distinct nonempty batches with exact fixed-width buffers.
    repeated = pa.ipc.open_stream(previous["repeated"]).read_next_batch()
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, repeated.schema) as writer:
        for start, length in ((0, 7), (0, 0), (7, 3)):
            arrays = [pa.concat_arrays([column.slice(start, length)]) for column in repeated.columns]
            writer.write_batch(pa.RecordBatch.from_arrays(arrays, schema=repeated.schema))
    sources["repeated_multi"] = sink.getvalue().to_pybytes()
    return sources


def compare(pa, sources):
    pins = {}
    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        for label, data in sources.items():
            (scratch / f"{label}.arrow").write_bytes(data)
        subprocess.run(["lake", "env", "lean", "--run", str(HERE / "Emit.lean"), directory, *sources],
                       cwd=ROOT, check=True)
        for label, source in sources.items():
            data = (scratch / f"{label}.lean.arrow").read_bytes()
            expected, actual = pa.ipc.open_stream(source), pa.ipc.open_stream(data)
            fields, schema_end = raw_schema(data)
            require(fields == raw_schema(source)[0] and actual.schema.equals(expected.schema),
                    f"{label}: positional schema changed")
            cursor = schema_end
            records = []
            for old, new in zip(expected, actual, strict=True):
                record = read_record(data, cursor)
                require(old.num_rows == new.num_rows == record.rows, f"{label}: row count changed")
                values = columns(pa, old)
                require(columns(pa, new) == values, f"{label}: logical rows changed")
                check_record(pa, expected.schema, record, values)
                records.append({"start": cursor, "metadata": len(record.metadata),
                                "body": len(record.body), "rows": record.rows, "end": record.end})
                cursor = record.end
            require(data[cursor:] == eos, f"{label}: expected exactly one final modern EOS")
            pins[label] = {**fingerprint(data), "schema_end": schema_end, "records": records, "eos": cursor}
            print(f"{label}: rows {[record['rows'] for record in records]}, "
                  f"frame ends {[record['end'] for record in records]}, EOS at {cursor}")
    return pins


def main():
    import pyarrow as pa

    pins = json.loads(MANIFEST.read_text(encoding="utf-8"))
    require(platform.python_implementation() == "CPython" and
            platform.python_version() == pins["producer"]["cpython"], "CPython pin differs")
    require(pa.__version__ == pins["producer"]["pyarrow"], "PyArrow pin differs")
    sources = produce(pa)
    require({label: fingerprint(data) for label, data in sources.items()} == pins["genuine_ipc"],
            "genuine input pins differ")
    require(compare(pa, sources) == pins["lean_ipc"], "Lean output pins or raw cursors differ")


if __name__ == "__main__":
    main()
