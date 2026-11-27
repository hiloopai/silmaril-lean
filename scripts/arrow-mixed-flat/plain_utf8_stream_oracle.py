#!/usr/bin/env python3
"""Compare independent PyArrow 26.0.1 and Lean plain Utf8 streams."""
import argparse
import hashlib
from pathlib import Path
import runpy
import struct
import subprocess
import sys

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
EOS = b"\xff\xff\xff\xff\0\0\0\0"
PINS = {
    "plain_mixed": (
        "4ddf36d9f5e21fc70a2f9bc9469eff2de21a1b22361881d83fb58e39f0961b2c",
        [(312, 424, 216), (960, 384, 16), (1368, 424, 128)], 1928,
    ),
    "plain_schema_only": (
        "66b9f352e5dd234285ff0f385c46b9b5176a169b9896b99e2113d8411cd632ba",
        [], 312,
    ),
    "plain_empty": (
        "6286893bfbb2b9ae24064c273bccb1e4faab099d1d60f32dac26fbee198b662a",
        [(312, 384, 16)], 720,
    ),
}


def fixture_cases():
    file_oracle = runpy.run_path(str(ROOT / "scripts/arrow-mixed-flat/file_writer_oracle.py"))
    cases = file_oracle["fixture_cases"]()
    return {name: cases[name] for name in ("plain_mixed", "plain_schema_only", "plain_empty")}


def produce(schema, batches):
    sink = pa.BufferOutputStream()
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5,
                                     use_legacy_format=False, compression=None)
    with pa.ipc.new_stream(sink, schema, options=options) as writer:
        for batch in batches:
            writer.write_batch(batch)
    return sink.getvalue().to_pybytes()


def verify(wire, schema, expected):
    with pa.ipc.open_stream(wire) as reader:
        assert reader.schema.equals(schema, check_metadata=True)
        observed = list(reader)
    assert [batch.num_rows for batch in observed] == [batch.num_rows for batch in expected]
    for reference, actual in zip(expected, observed, strict=True):
        actual.validate(full=True)
        assert actual.equals(reference, check_metadata=True)

    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(expected)
    offset = 0
    ranges = []
    for message in messages:
        size = message.metadata.size
        body = message.body.size if message.body is not None else 0
        assert struct.unpack_from("<II", wire, offset) == (0xFFFFFFFF, size)
        if message.type == "record batch":
            ranges.append((offset, size, body))
        offset += 8 + size + body
    assert wire[offset:] == EOS
    return ranges, offset


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    if sys.byteorder != "little" or pa.__version__ != "26.0.1" or pa.cpp_build_info.version != "26.0.1":
        raise SystemExit("fixture requires little-endian PyArrow 26.0.1")
    args.output.mkdir(parents=True, exist_ok=True)
    cases = fixture_cases()
    for name, (schema, batches) in cases.items():
        wire = produce(schema, batches)
        ranges, eos = verify(wire, schema, batches)
        digest = hashlib.sha256(wire).hexdigest()
        assert (digest, ranges, eos) == PINS[name]
        (args.output / f"pyarrow-{name}.arrows").write_bytes(wire)
        print(f"PyArrow {name} {digest} ranges {ranges} EOS {eos}", flush=True)
    subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", "--run",
         str(ROOT / "scripts/arrow-mixed-flat/PlainUtf8StreamOracle.lean"), str(args.output.resolve())],
        cwd=ROOT, check=True,
    )
    for name, (schema, batches) in cases.items():
        wire = (args.output / f"lean-{name}.arrows").read_bytes()
        ranges, eos = verify(wire, schema, batches)
        print(f"Lean {name} {hashlib.sha256(wire).hexdigest()} ranges {ranges} EOS {eos}")


if __name__ == "__main__":
    main()
