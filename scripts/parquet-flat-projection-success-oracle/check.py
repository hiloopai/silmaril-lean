"""Compare composed source reads with independent PyArrow group observations."""

import argparse
from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
from runpy import run_path
import subprocess

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PINS = {
    "wide.parquet": "4a63a28bda9dda61a334eca989d152cc96bc4c405f7b940f42bac3d819a84c6a",
    "empty-middle.parquet": "d1a64588b88f9c84497283218e25b1c8a0a1f7cf353980323433a996d3e65c3c",
    "schema-only.parquet": "3fbbf7d60350faec15ac0303ab71a2b0ea9245714b27dacc3b0ca43f29ced089",
    "observations.json": "7f4bb57812c8f261fe10fcfa14178fc7b4d0b3498fb39c80ee943274451b68c5",
}


def observe(path, ordinals):
    with pq.ParquetFile(path) as source:
        schema = source.schema_arrow
        selected = [schema[index] for index in ordinals]
        fields = [
            {"name": field.name, "nullable": field.nullable, "kind": str(field.type)}
            for field in selected
        ]
        groups = []
        for index in range(source.num_row_groups):
            names = list(dict.fromkeys(field.name for field in selected))
            group = source.read_row_group(index, columns=names, use_threads=False)
            values = []
            for field in selected:
                slots = group[field.name].to_pylist()
                values.append([
                    list(slot) if slot is not None else None for slot in slots
                ] if field.type == pa.binary() else slots)
            assert group.num_rows == source.metadata.row_group(index).num_rows
            groups.append({"rows": group.num_rows, "values": values})
    return {"fields": fields, "groups": groups}


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
    cases = [
        ("wide", [1, 0, 1]),
        ("wide", [1, 0, 1, 3, 1]),
        ("empty-middle", []),
        ("empty-middle", [1, 0, 1]),
        ("schema-only", [1, 0, 1]),
    ]
    actual = json.loads((out / "observations.json").read_text(encoding="utf-8"))
    expected = [observe(out / f"{name}.parquet", ordinals) for name, ordinals in cases]
    assert actual == expected
    assert [group["rows"] for group in actual[2]["groups"]] == [12, 0, 6]
    for name in ("wide.parquet", "empty-middle.parquet", "schema-only.parquet", "observations.json"):
        digest = sha256((out / name).read_bytes()).hexdigest()
        print(f"{digest}  {name}")
        assert digest == PINS[name], f"{name}: fixture hash changed"
    print("PyArrow verified the exact projected schema, nullable slots and original group rows.")


if __name__ == "__main__":
    main()
