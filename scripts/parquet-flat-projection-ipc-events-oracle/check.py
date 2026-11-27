"""Compare projected native IPC events on pinned five-leaf Parquet fixtures."""

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
ORIGINAL = [3, 0, 1, 2]
REPEATED = [2, 1, 2, 3, 0]
PINS = {
    "wide.parquet": "4a63a28bda9dda61a334eca989d152cc96bc4c405f7b940f42bac3d819a84c6a",
    "empty-middle.parquet": "d1a64588b88f9c84497283218e25b1c8a0a1f7cf353980323433a996d3e65c3c",
    "schema-only.parquet": "3fbbf7d60350faec15ac0303ab71a2b0ea9245714b27dacc3b0ca43f29ced089",
    "empty-middle-repeat.arrows": "83c218cd640ee633b048b6dd7cc845d7d33bbc04e8bfdbb6bff6b5137227359a",
    "empty-middle-wide.arrows": "1a7b8642ae37d12e52284ec80e88517355eec7ce7bd9be10fc12a6dfedcd6c9a",
    "empty-middle-zero-width.arrows": "1036161839bbf5b7ae22301b475e2ee570ba1ed02c7f1c43167b1a3419c3cba4",
    "schema-only-repeat.arrows": "1e1d791362c6bbed0641a9b2f89bcebf23c8e8acf854dba23c79f47aae911b04",
    "schema-only-wide.arrows": "0e046b48109a437501e2826b28d7136acfaef91180ce34cca312e313606b39aa",
    "wide-repeat.arrows": "aa0229383abf72f7e38b87500a2a0f8b91fa729f1069a0900208570133e905b1",
    "wide-wide.arrows": "81beac932bab1dab6e314cbcd01217962363932dc4b86d86f2296c761820a742",
}


def compare_projection(wide, direct, positions):
    with pa.ipc.open_stream(wide) as original, pa.ipc.open_stream(direct) as projected:
        assert projected.schema.equals(pa.schema([original.schema[i] for i in positions]))
        for left, right in zip(original, projected, strict=True):
            assert left.num_rows == right.num_rows
            assert [left.column(i).to_pylist() for i in positions] == [
                column.to_pylist() for column in right.columns
            ]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert version("thrift") == "0.25.0"
    oracle = run_path(str(ROOT / "scripts/parquet-flat-projection-oracle/check.py"))
    oracle["produce_fixtures"](out)
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    for name in ("wide", "empty-middle", "schema-only"):
        source = out / f"{name}.parquet"
        original = (out / f"{name}-wide.arrows").read_bytes()
        oracle["check_ipc"](source, original, ORIGINAL)
        projections = [("repeat", REPEATED)]
        if name == "empty-middle":
            projections.append(("zero-width", []))
        for suffix, positions in projections:
            projected = (out / f"{name}-{suffix}.arrows").read_bytes()
            oracle["check_ipc"](source, projected, [ORIGINAL[i] for i in positions])
            compare_projection(original, projected, positions)
    for name, expected in PINS.items():
        digest = sha256((out / name).read_bytes()).hexdigest()
        print(f"{digest}  {name}")
        assert digest == expected, f"{name}: fixture hash changed"
    print("PyArrow checked seven emitted streams through EOS and four positional comparisons.")


if __name__ == "__main__":
    main()
