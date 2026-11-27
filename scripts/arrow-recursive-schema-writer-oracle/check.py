"""Read emitted Lean IPC schemas with pinned PyArrow and a raw FlatBuffers observer."""

import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "fixtures.json"
EVENTS = runpy.run_path(str(ROOT / "scripts/arrow-recursive-events-oracle/check.py"))
SCHEMA = EVENTS["SCHEMA"]
STREAM = EVENTS["STREAM"]
require, fingerprint = EVENTS["require"], EVENTS["fingerprint"]


def produce(pa):
    earlier = EVENTS["produce"](pa)
    repeated = pa.schema([pa.field("同じ", pa.struct([
        pa.field("葉", pa.int64(), nullable=False),
        pa.field("葉", pa.list_(pa.field("", pa.int32())), nullable=True),
    ]), nullable=False)])
    fixtures = {
        "four_level": earlier["schema_only"],
        "empty_name": earlier["empty_name"],
        "zero_width": SCHEMA["stream"](pa, pa.schema([])),
        "repeated_children": SCHEMA["stream"](pa, repeated),
    }
    # The producer API requires an actual string. This control changes one
    # optional name reference and preserves the producer's other metadata.
    try:
        pa.field(None, pa.int64())
    except TypeError:
        pass
    else:
        raise SystemExit("pinned PyArrow unexpectedly admits an absent field name")
    edits = {"absent_name": EVENTS["controls"](earlier)["absent_name"]}
    return fixtures, edits


def raw_fields(data, start, count):
    scalar, target, slot, vector = (SCHEMA[key] for key in ("scalar", "target", "slot", "vector"))
    require(start + 4 * count <= len(data), "field vector exceeds the original metadata")
    fields = []
    for word in range(start, start + 4 * count, 4):
        field = target(data, word)
        require(word + 4 <= field < len(data) and field % 4 == 0, "invalid original Field offset")
        name_slot = slot(data, field, 0)
        name = None
        if name_slot is not None:
            name_pos = target(data, name_slot)
            length = scalar(data, name_pos, "I")
            name = data[name_pos + 4:name_pos + 4 + length].decode("utf-8")
            require(data[name_pos + 4 + length] == 0, "name lacks its terminator")
        nullable = SCHEMA["read_scalar"](data, field, 1, "B")
        tag = SCHEMA["read_scalar"](data, field, 2, "B")
        require(nullable in (0, 1), "invalid original nullable flag")
        kind = target(data, slot(data, field, 3))
        width = None
        if tag == 2:
            width = SCHEMA["read_scalar"](data, kind, 0, "I")
            require(width in (32, 64) and SCHEMA["read_scalar"](data, kind, 1, "B") == 1,
                    "expected original signed INT32 or INT64")
        else:
            require(tag in (12, 13), "unexpected original union tag")
            vtable = kind - scalar(data, kind, "i")
            require(scalar(data, vtable, "H") == 4, "expected empty List or Struct type table")
        first, length = vector(data, field, 5)
        require((length == 0 if tag == 2 else length == 1 if tag == 12 else True),
                "incorrect original child vector cardinality")
        fields.append((name, bool(nullable), tag, width, raw_fields(data, first, length)))
    return fields


def raw_schema(ipc):
    data, end = SCHEMA["metadata"](ipc)
    return raw_fields(data, *SCHEMA["root_vector"](data)), end


def normalize_for_pyarrow(fields):
    return [("" if name is None else name, nullable, tag, width, normalize_for_pyarrow(children))
            for name, nullable, tag, width, children in fields]


def compare(pa, fixtures, edits):
    all_inputs = {**fixtures, **edits}
    outputs = {}
    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        for label, data in all_inputs.items():
            (scratch / f"{label}.arrow").write_bytes(data)
        subprocess.run(["lake", "env", "lean", "--run", str(HERE / "Emit.lean"), directory],
                       cwd=ROOT, check=True)
        for label, source in all_inputs.items():
            data = (scratch / f"{label}.lean.arrow").read_bytes()
            expected, _ = raw_schema(source)
            observed, eos = raw_schema(data)
            require(data[eos:] == STREAM["EOS"], f"{label}: emitted IPC lacks exact schema-only EOS")
            require(observed == expected, f"{label}: original raw field tree changed")
            pyarrow = pa.ipc.open_stream(data)
            require(list(pyarrow) == [], f"{label}: emitted stream contains a batch")
            named = [SCHEMA["pyarrow_field"](pa, field) for field in pyarrow.schema]
            require(named == normalize_for_pyarrow(expected), f"{label}: PyArrow's positional schema differs")
            if label in fixtures:
                require(pyarrow.schema.equals(pa.ipc.open_stream(source).schema),
                        f"{label}: PyArrow schema did not round trip")
            else:
                require(expected[0][0] is None and named[0][0] == "",
                        "expected raw absent name and PyArrow's empty string observation")
            outputs[label] = fingerprint(data)
            print(f"{label}: exact recursive metadata and EOS at byte {eos}")
    return outputs


def main():
    import pyarrow as pa

    pins = json.loads(MANIFEST.read_text(encoding="utf-8"))
    require(platform.python_implementation() == "CPython" and
            platform.python_version() == pins["producer"]["cpython"], "CPython pin differs")
    require(pa.__version__ == pins["producer"]["pyarrow"], "PyArrow pin differs")
    fixtures, edits = produce(pa)
    require({name: fingerprint(data) for name, data in fixtures.items()} == pins["genuine_ipc"],
            "genuine IPC pins differ")
    require({name: fingerprint(data) for name, data in edits.items()} == pins["labeled_edits"],
            "labeled edit pins differ")
    require(compare(pa, fixtures, edits) == pins["lean_ipc"], "Lean IPC pins differ")
    print("PyArrow and raw vector inspection agreed on five actual Lean schema-only streams")


if __name__ == "__main__":
    main()
