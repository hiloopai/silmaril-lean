"""Independently inspect native Lean NestedPoint writes and returned STRUCT IPC."""

from hashlib import sha256
from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile

import pyarrow as pa

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
STRUCT = runpy.run_path(str(HERE.parent / "arrow-struct-int32-int64-oracle/check.py"))
NESTED = runpy.run_path(str(HERE.parent / "parquet-nested-point-ipc-oracle/check.py"))
produce, check_ipc, inspect_ipc = (STRUCT[name] for name in ("produce", "check_pyarrow", "inspect_wire"))
inspect_parquet = NESTED["inspect"]
FIELD = pa.field("座標", pa.struct([
    pa.field("符号", pa.int32(), nullable=False), pa.field("wide_µ", pa.int64()),
]))
FIRST, _, LAST = STRUCT["POINT_ROWS"]
CASES = {"native": [FIRST, [], [], LAST], "schema_only": [], "framed_empty": [[]]}


def fixture_inputs():
    files = {name: produce(FIELD, batches) for name, batches in CASES.items()}
    left, right = FIELD.type
    fields = {
        "left_nullable": FIELD.with_type(pa.struct([left.with_nullable(True), right])),
        "right_required": FIELD.with_type(pa.struct([left, right.with_nullable(False)])),
        "duplicate": FIELD.with_type(pa.struct([left.with_name("wide"), right.with_name("wide")])),
        "empty_name": FIELD.with_name(""),
        "narrow": FIELD.with_type(pa.struct([left, right.with_type(pa.int32())])),
        "required_null": FIELD,
    }
    for name, field in fields.items():
        batches = [[(True, 1, 2)]] if name != "required_null" else [[(True, None, 2)]]
        files[name] = produce(field, batches)
    eos = b"\xff\xff\xff\xff\0\0\0\0"
    assert files["native"].endswith(eos) and files["right_required"].endswith(eos)
    files["edited_late"] = files["native"] + b"\0"
    files["edited_right_required"] = files["right_required"] + b"\0"
    return files


def inspect_singletons(wire, groups):
    physical = inspect_parquet(wire, groups, FIELD)
    for pair in physical:
        for (leaf,) in pair:
            _, payload, extent, levels = leaf
            assert extent == 2 * len(levels)
            assert wire[payload + 4:payload + 4 + extent] == b"".join(bytes((2, level)) for level in levels)


def main():
    assert platform.python_version() == "3.13.5" and pa.__version__ == "26.0.1"
    assert version("thrift") == "0.25.0"
    inputs = fixture_inputs()
    assert {name: sha256(data).hexdigest() for name, data in inputs.items()} == json.loads(
        (HERE / "fixtures.json").read_text())
    with tempfile.TemporaryDirectory(prefix="parquet-nested-point-from-ipc-") as output:
        directory = Path(output)
        for name, wire in inputs.items():
            (directory / f"{name}.arrow").write_bytes(wire)
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                        str(HERE / "Emit.lean"), output], cwd=ROOT, check=True)
        for name, batches in CASES.items():
            check_ipc(inputs[name], FIELD, batches)
            inspect_ipc(inputs[name], FIELD, batches, canonical=False)
            rows = [[(left, right) if present else None for present, left, right in batch] for batch in batches]
            inspect_singletons((directory / f"{name}.parquet").read_bytes(), rows)
            restored = (directory / f"{name}.returned.arrow").read_bytes()
            check_ipc(restored, FIELD, batches)
            inspect_ipc(restored, FIELD, batches, canonical=True)
    print("Thrift and PyArrow verified three Lean Parquet files and three returned native IPC streams")


if __name__ == "__main__":
    main()
