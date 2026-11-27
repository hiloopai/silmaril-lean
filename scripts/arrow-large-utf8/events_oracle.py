#!/usr/bin/env python3
"""Check pinned PyArrow LargeUtf8 inputs and modern Lean event output."""
import argparse
import hashlib
from pathlib import Path
import runpy
import subprocess
import sys

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
INPUT_HASHES = {
    "modern": "05ea324892d22c35a55893f8b2081e4687b34869374a36cf6ee2bd48dc4b66a5",
    "legacy": "0d959e375bc54c26b785ec1f06b3e13b6995516bc52a4cc41b995a07f440797f",
    "modern_schema_only": "1c936412eda21fca8be362b33d59078a9aaee6783f5f094a54cfb2c470ca55c1",
    "legacy_schema_only": "ea0a21dc7e65af0b7f9200581072e3523d67004d34d11d3126bac25b1a3c33f6",
}
BATCH_OUTPUT_HASH = "0070a73868c010940136d686816fa0de1c10cbeed86d7333d9ae645f32d03807"
SCHEMA_OUTPUT_HASH = "6534d41bf7498269f60e737dc08579b512d16bb06a5603cff0147fbdb2ba6932"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    if (sys.byteorder != "little" or pa.__version__ != "26.0.1"
            or pa.cpp_build_info.version != "26.0.1"):
        raise SystemExit("oracle requires little-endian PyArrow 26.0.1")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    scripts = ROOT / "scripts/arrow-large-utf8"
    producer = scripts / "stream_fixture.py"
    subprocess.run([sys.executable, str(producer)], cwd=ROOT, check=True)
    expected = runpy.run_path(str(producer))["EXPECTED"]
    verify = runpy.run_path(str(scripts / "stream_writer_oracle.py"))["verify"]
    subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", "--run",
         str(scripts / "TranscodeEvents.lean"), str(output)],
        cwd=ROOT, check=True,
    )
    for case, expected_input_hash in INPUT_HASHES.items():
        schema_only = case.endswith("_schema_only")
        values = [] if schema_only else expected
        source = (output / f"{case}.source.arrows").read_bytes()
        input_hash = hashlib.sha256(source).hexdigest()
        assert input_hash == expected_input_hash, (case, input_hash)
        with pa.ipc.open_stream(source) as reader:
            assert reader.schema.equals(pa.schema([pa.field("payload", pa.large_string())]))
            records = list(reader)
        assert [record.column(0).to_pylist() for record in records] == values

        wire = (output / f"{case}.arrows").read_bytes()
        ranges, eos = verify(wire, "payload", True, values)
        output_hash = hashlib.sha256(wire).hexdigest()
        assert output_hash == (SCHEMA_OUTPUT_HASH if schema_only else BATCH_OUTPUT_HASH), (case, output_hash)
        print(f"{case}: input {input_hash}, output {output_hash}, records {ranges}, EOS {eos}")


if __name__ == "__main__":
    main()
