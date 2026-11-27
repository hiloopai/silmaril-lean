"""Compare the actual checked Parquet, BinaryView, and typed hex CSV path."""

import argparse
import csv
from hashlib import sha256
import json
import os
from pathlib import Path
from runpy import run_path
import subprocess
import sys

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CASES = [
    ("selected.parquet", "optional-v2", "blob", True, [4, 4]),
    ("plain-byte-array-v1.parquet", "required-v1", "key", False, [12, 12, 12]),
    ("schema-only.parquet", "schema-only", "blob", True, []),
    ("framed-zero-row-group.parquet", "empty-batch", "blob", True, [0]),
]


def checked_rows(path, name, nullable, counts):
    with pq.ParquetFile(path) as source:
        assert source.schema_arrow.field(name) == pa.field(name, pa.binary(), nullable=nullable)
        groups = []
        for i in range(source.num_row_groups):
            group = source.read_row_group(i, columns=[name])
            group.validate(full=True)
            groups.append(group.column(0).to_pylist())
        assert [len(group) for group in groups] == counts
    return groups


def tokens(name, rows):
    return [[name]] + [["N" if value is None else "T" + value.hex().upper()] for value in rows]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    producer = out / "source"
    producer.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert sys.version_info[:2] == (3, 13)
    subprocess.run(
        [sys.executable, str(ROOT / "scripts/parquet-byte-array-to-ipc-oracle/check.py"), "--out", str(producer)],
        cwd=ROOT, check=True,
    )
    read_ipc = run_path(str(ROOT / "scripts/typed-csv-opaque-ipc-oracle/check.py"))["read_ipc"]
    expected = {}
    for file, stem, name, nullable, counts in CASES:
        groups = checked_rows(producer / file, name, nullable, counts)
        field = pa.field(name, pa.binary_view(), nullable=nullable)
        assert read_ipc(producer / f"{stem}.arrows", field) == groups
        values = [value for group in groups for value in group]
        expected[stem] = (field, values, tokens(name, values))
        with (producer / f"{stem}.csv").open("w", encoding="utf-8", newline="") as stream:
            csv.writer(stream, lineterminator="\r\n").writerows(expected[stem][2])
    _, opaque, _ = expected["optional-v2"]
    assert None in opaque and b"" in opaque
    assert any(b"\x00" in value and b"\xff" in value for value in opaque if value)

    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
         "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    for stem, (field, values, expected_csv) in expected.items():
        with (out / f"{stem}.csv").open(encoding="utf-8", newline="") as stream:
            assert list(csv.reader(stream, strict=True)) == expected_csv
        assert read_ipc(out / f"{stem}.arrows", field) == [values]
    assert (out / "schema-only.arrows").read_bytes() == (out / "empty-batch.arrows").read_bytes()

    pins = json.loads((HERE / "sha256.json").read_text(encoding="utf-8"))
    assert set(pins) == {
        f"{prefix}{stem}.{suffix}"
        for stem in expected for prefix in ("", "source/") for suffix in ("arrows", "csv")
    }
    for name, digest in pins.items():
        actual = sha256((out / name).read_bytes()).hexdigest()
        assert actual == digest, f"{name}: fixture hash changed"
        print(f"{actual}  {name}")
    print("PyArrow and CPython verified all four files, both IPC stages, and ordered nullable hex CSV.")


if __name__ == "__main__":
    main()
