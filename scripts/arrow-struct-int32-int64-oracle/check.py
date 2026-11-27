"""Check the signed-wide STRUCT against independent IPC and legacy byte pins."""

from hashlib import sha256
import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile

import pyarrow as pa

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEGACY_DIR = HERE.parent / "arrow-struct-int32-oracle"
LEGACY = runpy.run_path(str(LEGACY_DIR / "check.py"))
produce, inspect_wire, check_pyarrow, edit = (LEGACY[name] for name in (
    "produce", "inspect_wire", "check_pyarrow", "edit"))
MIN, MAX = -(2**63), 2**63 - 1
POINT = pa.field("point", pa.struct([
    pa.field("signed", pa.int32(), nullable=False), pa.field("wide", pa.int64()),
]))
REQUIRED = pa.field("点", pa.struct([pa.field("同", pa.int32()),
                                   pa.field("同", pa.int64(), nullable=False)]))
POINT_ROWS = [
    [(False, 11, -37), (True, -(2**31), MIN), (True, 0, None), (False, None, MAX),
     (True, 2**31 - 1, MAX)],
    [],
    [(True, -1, 4398046511104), (True, 7, -4398046511105)],
]
REQUIRED_ROWS = [[(False, 17, None), (True, None, 2147483648), (True, -17, -2147483649), (False, -1, MIN)], []]
CASES = {"nested_point_shape": (POINT, POINT_ROWS), "required_wide": (REQUIRED, REQUIRED_ROWS),
         "schema_only": (POINT, [])}


def fixtures():
    inputs = {name: produce(field, rows) for name, (field, rows) in CASES.items()}
    for name, typ in (("unsigned", pa.uint64()), ("float", pa.float64()), ("timestamp", pa.timestamp("ns"))):
        inputs[name] = produce(POINT.with_type(pa.struct([POINT.type[0], POINT.type[1].with_type(typ)])), [])
    inputs["swapped"] = produce(POINT.with_type(pa.struct([POINT.type[1], POINT.type[0]])), [])
    inputs["required_visible"] = produce(REQUIRED, [[(True, 1, None)]])
    source = inputs["nested_point_shape"]
    first, _, _ = inspect_wire(source, POINT, POINT_ROWS, canonical=False)
    nodes, buffers, _, _, _ = first
    inputs["edited_short_wide"] = edit(source, buffers + 4 * 16 + 8, "<q", 8 * len(POINT_ROWS[0]) - 1)
    inputs["edited_wide_null_count"] = edit(source, nodes + 2 * 16 + 8, "<q", 0)
    inputs["edited_trailing"] = source + b"\0"
    return inputs


def hashes(inputs):
    return {name: sha256(wire).hexdigest() for name, wire in inputs.items()}


def stage(directory, inputs):
    directory.mkdir(exist_ok=True)
    for name, wire in inputs.items():
        (directory / f"{name}.arrow").write_bytes(wire)


def execute(driver, directory):
    subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                    str(driver), str(directory)], cwd=ROOT, check=True)


def main():
    assert platform.python_version() == "3.13.5" and pa.__version__ == "26.0.1"
    pins = json.loads((HERE / "fixtures.json").read_text())
    inputs = fixtures()
    assert hashes(inputs) == pins["inputs"]
    legacy = LEGACY["fixtures"]()
    assert hashes(legacy) == json.loads((LEGACY_DIR / "fixtures.json").read_text())
    with tempfile.TemporaryDirectory(prefix="arrow-struct-int32-int64-") as output:
        directory = Path(output)
        legacy_dir = directory / "legacy"
        stage(directory, inputs)
        stage(legacy_dir, legacy)
        execute(HERE / "Emit.lean", directory)
        for name, (field, rows) in CASES.items():
            check_pyarrow(inputs[name], field, rows)
            inspect_wire(inputs[name], field, rows, canonical=False)
            emitted = (directory / f"{name}.lean.arrow").read_bytes()
            check_pyarrow(emitted, field, rows)
            inspect_wire(emitted, field, rows, canonical=True)
        execute(LEGACY_DIR / "Emit.lean", legacy_dir)
        original = {name: (legacy_dir / f"{name}.lean.arrow").read_bytes() for name in LEGACY["CASES"]}
        assert hashes(original) == pins["legacy_outputs"]
    print("PyArrow verified three actual signed-wide IPCs, and all three two-INT32 IPCs are byte-identical")


if __name__ == "__main__":
    main()
