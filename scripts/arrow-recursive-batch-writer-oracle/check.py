"""Compare actual Lean recursive RecordBatch frames with PyArrow and raw IPC."""

import json
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MANIFEST = HERE / "fixtures.json"
SCHEMA_WRITER = runpy.run_path(str(ROOT / "scripts/arrow-recursive-schema-writer-oracle/check.py"))
STREAM = SCHEMA_WRITER["STREAM"]
read_record, require, fingerprint, eos = (
    STREAM[key] for key in ("read_record", "require", "fingerprint", "EOS")
)
raw_schema = SCHEMA_WRITER["raw_schema"]
HIDDEN = object()


def produce(pa):
    predecessors = STREAM["produce"](pa)
    sources = {name: predecessors[name] for name in
               ("four_level", "hidden", "zero_width_multi", "schema_only")}

    # A second bitmap byte and repeated positional names at both levels.
    pair = pa.struct([pa.field("same", pa.int32()), pa.field("same", pa.int64(), nullable=False)])
    left = pa.array([None, -(2**31), 2**31 - 1, -4, 5, -6, 7, 8, None, 10], type=pa.int32())
    right = pa.array([-(2**63), -(2**41), 2**63 - 1, 4, -5, 2**50, 7, -8, 9, -10], type=pa.int64())
    inner = pa.StructArray.from_arrays([left, right], fields=list(pair),
                                      mask=pa.array([False, True] + [False] * 7 + [True]))
    schema = pa.schema([pa.field("repeat", pair), pa.field("repeat", pa.int32())])
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema) as writer:
        writer.write_batch(pa.RecordBatch.from_arrays([inner, left], schema=schema))
    sources["repeated"] = sink.getvalue().to_pybytes()
    return sources


def logical(pa, array, slot):
    scalar = array[slot]
    if not scalar.is_valid:
        return None
    if pa.types.is_struct(array.type):
        return tuple(logical(pa, array.field(index), slot) for index in range(array.type.num_fields))
    if pa.types.is_list(array.type):
        return [logical(pa, scalar.values, index) for index in range(len(scalar.values))]
    return scalar.as_py()


def columns(pa, batch):
    return [[logical(pa, batch.column(index), slot) for slot in range(batch.num_rows)]
            for index in range(batch.num_columns)]


def check_record(pa, schema, record, logical_columns):
    nodes, buffers = [], []
    body = bytearray()

    def add(raw):
        buffers.append((len(body), len(raw)))
        body.extend(raw)
        body.extend(b"\0" * (-len(raw) % 8))

    def walk(field, values):
        require(field.nullable or all(value is not None for value in values), "visible required null")
        nodes.append((len(values), sum(value is None for value in values)))
        bitmap = bytearray((len(values) + 7) // 8)
        for index, value in enumerate(values):
            bitmap[index // 8] |= int(value is not None) << (index % 8)
        add(bitmap)
        kind = field.type
        if pa.types.is_struct(kind):
            for index, child in enumerate(kind):
                walk(child, [HIDDEN if value is None or value is HIDDEN else value[index]
                             for value in values])
        elif pa.types.is_list(kind):
            offsets, children = [0], []
            for value in values:
                if value is not None and value is not HIDDEN:
                    children.extend(value)
                offsets.append(len(children))
            add(b"".join(struct.pack("<i", offset) for offset in offsets))
            walk(kind.value_field, children)
        else:
            require(kind in (pa.int32(), pa.int64()), "unexpected type")
            code = "<i" if kind.bit_width == 32 else "<q"
            add(b"".join(struct.pack(code, 0 if value is None or value is HIDDEN else value)
                         for value in values))

    for declaration, values in zip(schema, logical_columns, strict=True):
        walk(declaration, values)
    require(record.nodes == nodes, "raw preorder node vector differs")
    require(record.buffers == buffers, "raw preorder buffer vector differs")
    require(record.body == body, "raw validity, words, List windows or zero padding differ")


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
            expected, reader = pa.ipc.open_stream(source), pa.ipc.open_stream(data)
            fields, cursor = raw_schema(data)
            require(fields == raw_schema(source)[0] and reader.schema.equals(expected.schema),
                    f"{label}: schema changed")
            counts = []
            for old, new in zip(expected, reader, strict=True):
                record = read_record(data, cursor)
                require(old.num_rows == new.num_rows == record.rows, f"{label}: row count changed")
                values = columns(pa, old)
                require(columns(pa, new) == values, f"{label}: positional logical rows changed")
                check_record(pa, expected.schema, record, values)
                counts.append(record.rows)
                cursor = record.end
            require(data[cursor:] == eos, f"{label}: the last emitted frame did not end at EOS")
            pins[label] = fingerprint(data)
            print(f"{label}: schemas, logical rows and canonical original bytes agree for batches {counts}")
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
    require(compare(pa, sources) == pins["lean_ipc"], "native Lean output pins differ")


if __name__ == "__main__":
    main()
