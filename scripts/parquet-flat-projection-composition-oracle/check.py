"""Check positional composition on the pinned five-leaf Parquet producer."""

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
PINS = {
    "wide.parquet": "4a63a28bda9dda61a334eca989d152cc96bc4c405f7b940f42bac3d819a84c6a",
    "wide-late.parquet": "1555bbf83c8d720d87e26b7d8926bd4684dffd83b6b4a8062c8a6c9b1737925a",
    "empty-middle.parquet": "d1a64588b88f9c84497283218e25b1c8a0a1f7cf353980323433a996d3e65c3c",
    "schema-only.parquet": "3fbbf7d60350faec15ac0303ab71a2b0ea9245714b27dacc3b0ca43f29ced089",
    "wide-repeat.arrows": "194641640800560e033808d6b1110bd6037187ac5b1c3c36f4a15320d77aafc6",
    "framed-repeat.arrows": "2f37652678f4cffacac55194d04c457d8e00f9ad4d885fb89c06ab7c7f6a14e2",
    "framed-empty.arrows": "1036161839bbf5b7ae22301b475e2ee570ba1ed02c7f1c43167b1a3419c3cba4",
    "schema-only-repeat.arrows": "27063a29702a4a29bb620c9e1564b8e150c8e792cb5c84bd090aed30d4b6c55f",
    "wide-late-drop.arrows": "194641640800560e033808d6b1110bd6037187ac5b1c3c36f4a15320d77aafc6",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert version("thrift") == "0.25.0"
    oracle = run_path(str(ROOT / "scripts/parquet-flat-projection-oracle/check.py"))
    header = oracle["produce_fixtures"](out)
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), str(out), str(header)],
        cwd=ROOT, check=True,
    )
    cases = [
        ("wide-repeat", "wide", [1, 0, 1]),
        ("framed-repeat", "empty-middle", [1, 0, 1]),
        ("framed-empty", "empty-middle", []),
        ("schema-only-repeat", "schema-only", [1, 0, 1]),
        ("wide-late-drop", "wide-late", [1, 0, 1]),
    ]
    for result, source, ordinals in cases:
        oracle["check_ipc"](out / f"{source}.parquet", (out / f"{result}.arrows").read_bytes(), ordinals)
    for name in ("wide.parquet", "wide-late.parquet", "empty-middle.parquet", "schema-only.parquet",
                 *(name + ".arrows" for name, _, _ in cases)):
        digest = sha256((out / name).read_bytes()).hexdigest()
        print(f"{digest}  {name}")
        assert digest == PINS[name], f"{name}: fixture hash changed"
    print("PyArrow verified the composed ordinal lists and exact group rows through IPC EOS.")


if __name__ == "__main__":
    main()
