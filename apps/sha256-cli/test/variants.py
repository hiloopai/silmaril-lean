#!/usr/bin/env python3
"""Runtime evidence and mutation controls for retained O3 SHA driver variants.

Requires Linux x86-64. Native runs do not establish a Lean machine theorem.
Producer-chunked pipes do not claim an observed kernel read/write schedule.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import platform
import random
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("sha_variants", HERE.parent / "build_variants.py")
variants = importlib.util.module_from_spec(spec)
spec.loader.exec_module(variants)


def expected(data):
    return variants.sha(data).encode("ascii") + b"\n"


def run(binary, data, **kwargs):
    result = subprocess.run([str(binary)], input=data, capture_output=True, timeout=10, **kwargs)
    return result.returncode == 0 and result.stdout == expected(data) and result.stderr == b""


def check(directory):
    started = time.perf_counter()
    data, manifest = variants.verify(directory)
    results = {}
    with tempfile.TemporaryDirectory(prefix="sha256-runtime-") as tmp:
        tmp = Path(tmp)
        binary = tmp / "sha256"
        binary.write_bytes(data)
        binary.chmod(0o755)
        rng = random.Random(3029)
        corpus = {"empty": b"", "abc": b"abc"}
        for size in [1, 55, 56, 57, 63, 64, 65, 119, 120, 127, 128, 129, 1000, 1048576]:
            corpus[f"length-{size}"] = rng.randbytes(size)
        for name, message in corpus.items():
            results[name] = run(binary, message)
        # Delays make short reads likely, but no syscall trace is asserted here.
        message = corpus["length-129"]
        process = subprocess.Popen([str(binary)], stdin=subprocess.PIPE,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        for offset in range(0, len(message), 7):
            process.stdin.write(message[offset:offset + 7])
            process.stdin.flush()
            time.sleep(0.001)
        process.stdin.close()
        output = process.stdout.read()
        stderr = process.stderr.read()
        results["producer-chunked-pipe"] = (process.wait(timeout=10) == 0
                                               and output == expected(message) and stderr == b"")
        process.stdout.close()
        process.stderr.close()

        # A refused read must exit 1 before output; a refused write also exits 1.
        refused_read = subprocess.run([str(binary)], preexec_fn=lambda: os.close(0),
                                      capture_output=True, timeout=10)
        results["read-ebadf"] = (refused_read.returncode == 1 and refused_read.stdout == b""
                                  and refused_read.stderr == b"")
        with open("/dev/full", "wb") as full:
            refused_write = subprocess.run([str(binary)], input=b"abc", stdout=full,
                                           stderr=subprocess.PIPE, timeout=10)
        results["write-enospc"] = refused_write.returncode == 1 and refused_write.stderr == b""

        # Corrupt the actual ELF's hex lookup table, then require a wrong digest.
        table = b"0123456789abcdef"
        if data.count(table) != 1:
            raise ValueError("expected exactly one retained hex lookup table")
        mutant = tmp / "wrong-hex"
        mutant.write_bytes(data.replace(table, b"g123456789abcdef"))
        mutant.chmod(0o755)
        observed = subprocess.run([str(mutant)], input=b"", capture_output=True, timeout=10)
        results["wrong-hex-runtime-rejected"] = (observed.returncode == 0
                                                  and len(observed.stdout) == 65
                                                  and observed.stdout != expected(b""))

        # Retained-byte and claimed-source corruption must both fail validation.
        copied = tmp / "manifest-mutation"
        shutil.copytree(directory, copied)
        (copied / "sha256.elf.hex").write_text(mutant.read_bytes().hex())
        try:
            variants.verify(copied)
        except ValueError:
            results["artifact-hash-mutation-rejected"] = True
        else:
            results["artifact-hash-mutation-rejected"] = False
        (copied / "sha256.elf.hex").write_bytes((directory / "sha256.elf.hex").read_bytes())
        corrupt = json.loads((copied / "manifest.json").read_text())
        corrupt["sources"]["src/sha256.c"] = "0" * 64
        variants.write_json(copied / "manifest.json", corrupt)
        try:
            variants.verify(copied)
        except ValueError:
            results["source-hash-mutation-rejected"] = True
        else:
            results["source-hash-mutation-rejected"] = False
        for field, name in [("producer", "build_variants.py"),
                            ("model_snapshot", "Silmaril/Process/CLI/Sha256.lean")]:
            corrupt = json.loads((directory / "manifest.json").read_text())
            entries = corrupt[field]["files"] if field == "model_snapshot" else corrupt[field]
            entries[name] = "0" * 64
            variants.write_json(copied / "manifest.json", corrupt)
            try:
                variants.verify(copied)
            except ValueError:
                results[field + "-hash-mutation-rejected"] = True
            else:
                results[field + "-hash-mutation-rejected"] = False

    return {"variant": manifest["variant"], "artifact_sha256": variants.sha(data),
            "host": {"system": platform.system(), "machine": platform.machine()},
            "test_script_sha256": variants.file_sha(Path(__file__)),
            "evidence_stage": "native runtime examples and rejecting mutation controls; no formal binary correctness",
            "short_transfer_scope": "producer-chunked input only; arbitrary short-transfer syscall schedules remain a proof obligation",
            "results": results, "seconds": time.perf_counter() - started,
            "passed": all(results.values())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise SystemExit("runtime controls require Linux x86_64; artifact verification is portable")
    result = check(args.directory)
    if args.output:
        variants.write_json(args.output, result)
    print(json.dumps(result, indent=2, sort_keys=True))
    raise SystemExit(0 if result["passed"] else 1)


if __name__ == "__main__":
    main()
