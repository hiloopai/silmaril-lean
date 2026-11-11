#!/usr/bin/env python3
"""Golden command-line suites of wasm-tools; pass the binary under test.

python3 -I tools/wasm-tools/test-cli.py [--suite NAME]... [--jobs N] [--verbose] [BINARY]

BINARY defaults to .lake/build/bin/wasm-tools. Each suite is a file
tools/wasm-tools/tests/golden/NAME.json: fixtures, a comparison mode and a list of
command lines with the outcome the pinned upstream wasm-tools 1.262.0 gave for them
(exit status, stdout, the files the command wrote, stderr as far as the mode compares it);
a case may name a fixture as its stdin (else stdin is empty).
The outcomes were recorded by tools/wasm-tools/tests/golden-capture.sh; this script
needs no upstream binary. A case marked "known" is reported but does not fail the run.

Exit status 0 when every case outside "known" agrees, 1 otherwise.
"""

import base64
import concurrent.futures
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
GOLDEN = HERE / "tests" / "golden"
FIXTURES = HERE / "tests" / "fixtures"
TIMEOUT = 60


def environment():
    """The environment of every run: the caller's, without terminal width or colour hints."""
    env = {k: v for k, v in os.environ.items()
           if k not in ("COLUMNS", "LINES", "CLICOLOR", "CLICOLOR_FORCE", "NO_COLOR", "TERM")}
    env["LANG"] = env["LC_ALL"] = "C.UTF-8"
    return env


def blob(data):
    """A JSON value for bytes: the text when it is UTF-8, else base64."""
    try:
        return {"text": data.decode("utf-8")}
    except UnicodeDecodeError:
        return {"base64": base64.b64encode(data).decode("ascii")}


def stderr_view(mode, status, data):
    """The part of stderr a suite compares."""
    if mode == "exact":
        return blob(data)
    if mode == "exact-unless-1":
        return blob(data[:6]) if status == 1 else blob(data)
    if mode == "error-word":
        return {"text": "error:" if data.startswith(b"error:") else ""}
    if mode == "empty-or-not":
        return {"text": "nonempty" if data else ""}
    raise ValueError(f"unknown stderr mode {mode}")


def setup(suite, directory):
    """Copy the suite's fixtures into a fresh working directory; return their digests."""
    for name, source in suite.get("fixtures", {}).items():
        target = directory / name
        if isinstance(source, dict) and "text" in source:
            target.write_text(source["text"])
        else:
            shutil.copyfile(FIXTURES / source, target)
    for name in suite.get("dirs", []):
        (directory / name).mkdir()
    return snapshot(directory)


def snapshot(directory):
    out = {}
    for path in sorted(directory.rglob("*")):
        if path.is_file():
            out[str(path.relative_to(directory))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return out


def run(binary, suite, args, stdin=None):
    """Run one command line in a fresh directory (stdin: the named fixture, else empty):
    its observable outcome."""
    with tempfile.TemporaryDirectory(prefix="wasm-tools-cli-") as tmp:
        directory = Path(tmp)
        before = setup(suite, directory)
        data = (FIXTURES / stdin).read_bytes() if stdin else b""
        result = subprocess.run([str(binary), *args], cwd=directory, env=environment(),
                                input=data, capture_output=True,
                                timeout=TIMEOUT, check=False)
        after = snapshot(directory)
        written = {name: digest for name, digest in after.items() if before.get(name) != digest}
        removed = sorted(name for name in before if name not in after)
        mode = suite.get("stderr", "exact")
        return {"status": result.returncode, "stdout": blob(result.stdout),
                "stderr": stderr_view(mode, result.returncode, result.stderr),
                "files": written, "removed": removed}


FIELDS = ("status", "stdout", "stderr", "files", "removed")


def differences(expected, got):
    return [field for field in FIELDS if expected.get(field) != got.get(field)]


def show(value):
    text = json.dumps(value, ensure_ascii=False)
    return text if len(text) <= 160 else text[:157] + "..."


def main(argv):
    suites, verbose, binary, jobs = [], False, None, min(8, os.cpu_count() or 1)
    i = 0
    while i < len(argv):
        if argv[i] == "--suite":
            suites.append(argv[i + 1]); i += 2
        elif argv[i] == "--jobs":
            jobs = int(argv[i + 1]); i += 2
        elif argv[i] == "--verbose":
            verbose = True; i += 1
        elif argv[i].startswith("-"):
            print(__doc__, file=sys.stderr); return 2
        else:
            binary = argv[i]; i += 1
    binary = Path(binary or ".lake/build/bin/wasm-tools").resolve()
    if not os.access(binary, os.X_OK):
        print(f"SKIP: {binary} not built (lean_exe wasm-tools)")
        return 0
    names = suites or sorted(p.stem for p in GOLDEN.glob("*.json"))
    total_fail = 0
    for name in names:
        suite = json.loads((GOLDEN / f"{name}.json").read_text())
        same = known = fail = 0
        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
            outcomes = list(pool.map(lambda c: run(binary, suite, c["args"], c.get("stdin")),
                                     suite["cases"]))
        for case, got in zip(suite["cases"], outcomes):
            diff = differences(case["expect"], got)
            label = " ".join(case["args"]) or "(no arguments)"
            if not diff:
                same += 1
            elif "known" in case:
                known += 1
                print(f"known: {name}: {label}: {case['known']}")
            else:
                fail += 1
                print(f"DIFF: {name}: {label}: {', '.join(diff)}")
                if verbose:
                    for field in diff:
                        print(f"  want {field} {show(case['expect'].get(field))}")
                        print(f"  got  {field} {show(got.get(field))}")
        total_fail += fail
        print(f"{name}: {same} same, {known} known, {fail} differ (of {len(suite['cases'])})")
    return 1 if total_fail else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
