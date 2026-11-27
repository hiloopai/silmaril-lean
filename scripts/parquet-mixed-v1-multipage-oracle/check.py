"""Verify mixed PLAIN V1 page cuts, order, and wire offsets independently."""

import argparse
from hashlib import sha256
from importlib.metadata import version
import os
from pathlib import Path
from runpy import run_path
import subprocess

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LONG = b"\x80" + b"*" * 23 + b"\x00\xff"
GROUPS = [
    [[-2**31, None, 0, -7, 2**31 - 1], [None, b"", b"\xff\x00\x80", None, LONG]],
    [[], []],
    [[None, 6, -5], [LONG, None, b""]],
]
PINS = {
    "int-first": "e10ab4c45c6b52fd92a081ade11b8ac57a92e75595dad1951031de8b658947ae",
    "byte-first-recut": "b998b61d5013aed6305e4073b879866a48a749566aa872b660ed344950cb7d56",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert version("thrift") == "0.25.0"
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Write.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    thrift = run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
    oracle = run_path(str(ROOT / "scripts/parquet-mixed-v1-writer-oracle/check.py"))
    for name, order, first_cuts in (
        ("int-first", (1, 6), [[2, 3], [1, 1, 3]]),
        ("byte-first-recut", (6, 1), [[1, 4], [2, 1, 2]]),
    ):
        fields = [("count", True), ("opaque", True)]
        groups = GROUPS
        cuts = [first_cuts, [[0], [0]], [[3], [1, 2]]]
        if order == (6, 1):
            fields = fields[::-1]
            groups = [group[::-1] for group in groups]
            cuts = [group[::-1] for group in cuts]
        wire = (out / f"{name}.parquet").read_bytes()
        oracle["check_wire_groups"](thrift, wire, fields, groups, order, cuts)
        oracle["check_arrow_groups"](wire, fields, groups, order)
        digest = sha256(wire).hexdigest()
        print(f"{digest}  {name}.parquet")
        assert digest == PINS[name], f"{name}: fixture hash changed"
    print("PyArrow and Thrift checked both field orders, distinct page counts and exact chunk extents.")


if __name__ == "__main__":
    main()
