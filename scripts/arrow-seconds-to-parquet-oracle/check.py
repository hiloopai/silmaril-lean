"""Verify real Arrow seconds inputs and actual Lean Parquet millisecond output."""

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
import pyarrow.parquet as pq

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WRITER = runpy.run_path(str(HERE.parent / "arrow-timestamp-to-parquet-oracle/check.py"))
ARROW = WRITER["ARROW"]

# Derive both bounds in signed arithmetic, including the negative ceiling.
LOW, HIGH = -((-WRITER["MIN"]) // 1000), WRITER["MAX"] // 1000
assert (LOW, HIGH) == (-9223372036854775, 9223372036854775)
POSITIVE = {
    "utc_optional": ("UTC", True, [[LOW, None, 0, -1], [], [], [HIGH, 1, None]]),
    "local_required": (None, False, [[HIGH, 0], [], [LOW, -1001]]),
    "all_empty": (None, True, [[], []]),
    "schema_only": ("UTC", False, []),
}


def fixtures():
    stream = ARROW["timestamp_stream"]
    cases = {name: stream("s", zone, groups, nullable)
             for name, (zone, nullable, groups) in POSITIVE.items()}
    cases["positive_overflow"] = stream("s", "UTC", [[-1], [], [None, 0, HIGH + 1, LOW - 1]])
    cases["negative_overflow"] = stream("s", None, [[], [None, LOW - 1, HIGH + 1]])
    cases["wrong_unit"] = stream("ms", None, [[0]])
    cases["named_timezone"] = stream("s", "Asia/Kathmandu", [[-1], []])
    cases["offset_timezone"] = stream("s", "+00:00", [[0]])
    cases["present_empty_timezone"] = ARROW["explicit_empty_timezone"](cases["named_timezone"])

    # An earlier overflow never masks an error from the original record walk.
    malformed = stream("s", "UTC", [[HIGH + 1], [], [None, 0], [-1]])
    cases["truncated_body"] = malformed[:-9]
    cases["missing_eos"] = malformed[:-8]
    cases["trailing_bytes"] = malformed + b"x"
    # Metadata admission also follows the original reader's exact EOS.
    cases["timezone_missing_eos"] = cases["named_timezone"][:-8]
    return cases


def verify(source, output, zone, nullable, original):
    reader = pa.ipc.open_stream(source)
    assert reader.schema.field(0).equals(pa.field("time", pa.timestamp("s", zone), nullable=nullable))
    assert [batch.column(0).cast(pa.int64()).to_pylist() for batch in reader] == original
    expected = [[None if value is None else value * 1000 for value in group] for group in original]
    # The shared checker parses Thrift annotation and every original PLAIN word.
    # The expected millis stream here is an independent Python integer calculation.
    milliseconds = ARROW["timestamp_stream"]("ms", zone, expected, nullable)
    WRITER["verify"](milliseconds, output)
    parquet = pq.ParquetFile(pa.BufferReader(output))
    actual = [parquet.read_row_group(index).column(0).cast(pa.int64()).to_pylist()
              for index in range(parquet.metadata.num_row_groups)]
    assert all(value % 1000 == 0 for group in actual for value in group if value is not None)
    assert [[None if value is None else value // 1000 for value in group] for group in actual] == original


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    cases = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in cases.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="arrow-seconds-to-parquet-") as temporary:
        directory = Path(temporary)
        for name, source in cases.items():
            (directory / (name + ".arrows")).write_bytes(source)
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(directory)],
                       cwd=ROOT, check=True)
        assert {file.stem for file in directory.glob("*.parquet")} == set(POSITIVE)
        for name, (zone, nullable, groups) in POSITIVE.items():
            verify(cases[name], (directory / (name + ".parquet")).read_bytes(), zone, nullable, groups)


if __name__ == "__main__":
    main()
