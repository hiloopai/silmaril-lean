"""Check original PyArrow BinaryView IPC against actual Lean Parquet files."""

import argparse
from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
from runpy import run_path
import subprocess
import sys

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ALL_OCTETS = bytes(range(256))
CASES = {
    "optional": (pa.field("octets, café", pa.binary_view()),
                 [[None, b""], [], [b"\x00\xff\x80", ALL_OCTETS, b"a\x00z"]]),
    "required": (pa.field("raw", pa.binary_view(), nullable=False), [[b"", b"\xff\x00\x80"], [ALL_OCTETS]]),
    "schema-only": (pa.field("empty", pa.binary_view()), []),
    "explicit-empty": (pa.field("empty", pa.binary_view(), nullable=False), [[]]),
}
CONTROLS = ("trailing", "missing-eos", "required-null", "text")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    fixtures = out / "source"
    fixtures.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert sys.version_info[:2] == (3, 13) and version("thrift") == "0.25.0"

    producer = run_path(str(ROOT / "scripts/typed-csv-opaque-ipc-oracle/check.py"))
    source_rows = {}
    for stem, (field, batches) in CASES.items():
        path = fixtures / f"{stem}.arrows"
        producer["write_ipc"](path, field, batches)
        observed = producer["read_ipc"](path, field)
        assert observed == batches
        source_rows[stem] = [value for batch in observed for value in batch]
    source = (fixtures / "optional.arrows").read_bytes()
    (fixtures / "trailing.arrows").write_bytes(source + b"\x00")
    (fixtures / "missing-eos.arrows").write_bytes(source[:-8])
    producer["write_ipc"](fixtures / "required-null.arrows", CASES["required"][0], [[b""], [None]])
    producer["write_ipc"](fixtures / "text.arrows", pa.field("text", pa.string_view()), [["é"]])

    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
         "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    thrift = run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
    native = run_path(str(ROOT / "scripts/parquet-plain-byte-array-file-writer-oracle/check.py"))
    for stem, (field, _) in CASES.items():
        wire = (out / f"{stem}.parquet").read_bytes()
        native["check_wire"](thrift, wire, field.name, field.nullable, source_rows[stem])
        native["check_pyarrow"](wire, field.name, field.nullable, source_rows[stem])

    pins = json.loads((HERE / "sha256.json").read_text(encoding="utf-8"))
    assert set(pins) == {f"source/{stem}.arrows" for stem in (*CASES, *CONTROLS)} | {
        f"{stem}.parquet" for stem in CASES
    }
    for name, digest in pins.items():
        actual = sha256((out / name).read_bytes()).hexdigest()
        assert digest == actual, f"{name}: fixture hash changed"
        print(f"{actual}  {name}")
    print("PyArrow and Thrift verified exact schema, framing and source-ordered opaque slots in four native files.")


if __name__ == "__main__":
    main()
