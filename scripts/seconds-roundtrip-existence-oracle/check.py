"""Measure the independent native seconds sink and test exact and one-byte/row tighter caps."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile

import pyarrow as pa

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
INVERSE = runpy.run_path(str(HERE.parent / "parquet-millis-to-arrow-seconds-oracle/check.py"))
SECONDS = INVERSE["SECONDS"]


def measure(wire, rows):
    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert len(messages) == len(rows) + 1
    max_rows = max(map(len, rows), default=0)
    first_rows = next((i for i, group in enumerate(rows) if len(group) == max_rows), 0)
    sizes = [0 if message.body is None else message.body.size for message in messages[1:]]
    assert sizes == [8 * (len(group) + (len(group) + 63) // 64) for group in rows]
    max_body = max(sizes, default=0)
    first_body = next((i for i, size in enumerate(sizes) if size == max_body), 0)
    metadata_sizes = [message.metadata.size for message in messages]
    max_metadata = max(metadata_sizes)
    first_metadata_frame = metadata_sizes.index(max_metadata)
    return [len(rows), max_rows, max_body, max_metadata, sum(map(len, rows)),
            first_rows, first_body, first_metadata_frame]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    pins = json.loads((HERE.parent / "parquet-millis-to-arrow-seconds-oracle/fixtures.json").read_text())
    with tempfile.TemporaryDirectory(prefix="seconds-roundtrip-existence-") as temporary:
        directory = Path(temporary)
        lean = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                "-DwarningAsError=true", "--run", str(HERE / "Emit.lean")]
        for name, (zone, nullable, rows) in SECONDS["POSITIVE"].items():
            original = SECONDS["ARROW"]["timestamp_stream"]("s", zone, rows, nullable)
            assert sha256(original).hexdigest() == pins["original_seconds"][name]
            (directory / (name + ".input.arrows")).write_bytes(original)
        subprocess.run([*lean, "probe", str(directory)], cwd=ROOT, check=True)
        controls = 0
        for name, (zone, nullable, rows) in SECONDS["POSITIVE"].items():
            native = (directory / (name + ".probe.arrows")).read_bytes()
            INVERSE["verify_ipc"](native, zone, nullable, rows)
            caps = measure(native, rows)
            (directory / (name + ".caps")).write_text(" ".join(map(str, caps)))
            controls += 2 + int(caps[0] > 0) + int(caps[1] > 0) + int(caps[2] > 0) + 2 * int(caps[4] > 0)
            print(f"{name} independently measured batches/rows/body/metadata/total caps: {caps[:5]}")
        subprocess.run([*lean, "exercise", str(directory)], cwd=ROOT, check=True)
        for name, (zone, nullable, rows) in SECONDS["POSITIVE"].items():
            middle = (directory / (name + ".parquet")).read_bytes()
            assert sha256(middle).hexdigest() == pins["lean_parquet"][name]
            output = (directory / (name + ".result.arrows")).read_bytes()
            assert output == (directory / (name + ".probe.arrows")).read_bytes()
            INVERSE["verify_ipc"](output, zone, nullable, rows)
        print(f"Four independent tight sink witnesses and {controls} one-unit refusal controls passed")


if __name__ == "__main__":
    main()
