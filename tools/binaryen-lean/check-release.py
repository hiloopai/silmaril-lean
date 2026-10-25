#!/usr/bin/env python3
"""Build the scoped toolkit and proof roots, then run native release checks."""

import argparse
import concurrent.futures
import hashlib
import json
import shutil
import subprocess
import sys
import time
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true",
                        help="first build the included library, executables and proof roots with --wfail")
    parser.add_argument("--bin-dir", type=Path, default=Path(".lake/build/bin"))
    parser.add_argument("--reference-bin-dir", type=Path,
                        help="optionally check extension codecs and merge against Binaryen version_133")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    root = Path(__file__).resolve().parents[2]
    suite_dir = Path(__file__).resolve().parent
    binaries = ["wasm-opt", "wasm-as", "wasm-dis", "wasm-merge", "wasm-shell",
                "wasm-ctor-eval", "wasm-metadce", "wasm-shell-lean"]
    manifest = json.loads((suite_dir / "release-manifest.json").read_text())
    proof_roots = sorted({proof["module"] for tool in
                          [*manifest["tools"], *manifest["cli_compatibility"]["executables"]]
                          for proof in tool.get("proof_roots", [])})
    subprocess.run([sys.executable, str(suite_dir / "check-release-manifest.py")],
                   cwd=root, check=True)
    node = shutil.which("node")
    if not node:
        parser.error("Node.js 24 or later is required for the independent execution checks")
    node_version = subprocess.run([node, "--version"], capture_output=True, text=True, check=True)
    if int(node_version.stdout.strip().removeprefix("v").split(".")[0]) < 24:
        parser.error("Node.js 24 or later is required for the GC and memory64 reference checks")

    if args.build:
        subprocess.run(["lake", "build", "--wfail", "Silmaril", *binaries, *proof_roots],
                       cwd=root, check=True)
    bin_dir = args.bin_dir.resolve()
    for binary in binaries:
        if not (bin_dir / binary).is_file():
            parser.error(f"missing {bin_dir / binary}; build first or pass --build")

    def binary(name):
        return str(bin_dir / name)

    suites = []

    def add(name, script, *arguments):
        suites.append((name, [sys.executable, str(suite_dir / script), *arguments]))

    add("seven-tool-demo", "test-release-demo.py", "--bin-dir", str(bin_dir))
    add("command-lines", "test-compat-tools.py", "--bin-dir", str(bin_dir))
    add("selected-passes", "test-selected-opt.py", binary("wasm-opt"))
    add("inlining", "test-selected-inlining.py", binary("wasm-opt"))
    add("extended-core", "test-selected-extended-inputs.py", binary("wasm-opt"))
    add("compact-imports", "test-compact-imports.py", "--", binary("wasm-opt"))
    add("canonical-encodings", "test-canonical-encodings.py", binary("wasm-opt"))
    add("zero-grow-refinement", "test-zero-grow-success.py", binary("wasm-opt"))
    add("mode-policies", "test-mode-cleanup.py", binary("wasm-opt"))
    add("trap-insertion", "test-trap-grow-cleanup.py", binary("wasm-opt"))
    add("constructor", "test-ctor-fallback.py", binary("wasm-ctor-eval"))
    add("graph-metadce", "test-metadce-fallback.py", binary("wasm-metadce"))
    add("shell-execution", "test-shell.py", binary("wasm-shell-lean"))
    for name in ["tools", "memory", "globals", "data"]:
        add("text-" + name, "test-text-" + name + ".py",
            "--as-driver", binary("wasm-as"), "--dis-driver", binary("wasm-dis"))
    add("text-numerics", "test-text-numerics.py",
        "--as-command", binary("wasm-as"), "--dis-command", binary("wasm-dis"))
    if args.reference_bin_dir:
        reference = args.reference_bin_dir.resolve()
        for command in ["wasm-as", "wasm-opt"]:
            if not (reference / command).is_file():
                parser.error(f"missing reference executable {reference / command}")
        for name, script in [("atomic-codec", "test-atomic-disassembly.py"),
                             ("memory-proposal-codec", "test-binaryen-memory-disassembly.py"),
                             ("legacy-exception-codec", "test-legacy-eh-disassembly.py")]:
            add(name, script, "--dis-command", binary("wasm-dis"),
                "--reference-as", str(reference / "wasm-as"),
                "--reference-opt", str(reference / "wasm-opt"))
        add("merge-sources-policies", "test-merge-supported.py",
            "--driver", binary("wasm-merge"), "--reference-as", str(reference / "wasm-as"),
            "--reference-opt", str(reference / "wasm-opt"))
        add("merge-function-subtyping", "test-merge-subtyping.py",
            "--driver", binary("wasm-merge"), "--reference-as", str(reference / "wasm-as"),
            "--reference-opt", str(reference / "wasm-opt"))

    def run(suite):
        name, command = suite
        start = time.monotonic()
        try:
            result = subprocess.run(command, cwd=root, capture_output=True,
                                    text=True, timeout=900)
            record = {"name": name, "command": command, "exit_code": result.returncode,
                      "stdout": result.stdout, "stderr": result.stderr}
        except subprocess.TimeoutExpired:
            record = {"name": name, "command": command, "exit_code": None,
                      "stdout": "", "stderr": "release suite exceeded 900 seconds"}
        record["elapsed_seconds"] = time.monotonic() - start
        return record

    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for record in pool.map(run, suites):
            results.append(record)
            passed = record["exit_code"] == 0
            print(("PASS " if passed else "FAIL ") + record["name"], flush=True)
            if not passed:
                print(record["stdout"] + record["stderr"], flush=True)
    revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root,
                              capture_output=True, text=True, check=False)
    report = {"schema_version": 1,
              "scope": "native scoped-tool regressions; not full Binaryen parity or kernel replay",
              "revision": revision.stdout.strip() if revision.returncode == 0 else None,
              "tracked_source_changes": subprocess.run(
                  ["git", "status", "--porcelain", "--untracked-files=no"], cwd=root,
                  capture_output=True, text=True, check=False).stdout.splitlines(),
              "build_and_proof_check_requested": args.build,
              "node_version": node_version.stdout.strip(),
              "proof_roots": proof_roots,
              "binary_sha256": {name: hashlib.sha256((bin_dir / name).read_bytes()).hexdigest()
                                for name in binaries},
              "suite_sha256": {Path(command[1]).name:
                               hashlib.sha256(Path(command[1]).read_bytes()).hexdigest()
                               for _, command in suites},
              "results": results}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    passed = sum(record["exit_code"] == 0 for record in results)
    print(f"{passed}/{len(results)} release suites passed; full CI/replay is separate")
    return 0 if passed == len(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
