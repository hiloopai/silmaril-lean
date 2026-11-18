#!/usr/bin/env bash
# Verify the Alethe fixtures tests/alethe/cvc5-1.4.2 against their receipt (docs/projects/formal-rows.md,
# "Alethe"): every file's SHA-256. With CVC5=<path to the cvc5 1.4.2 executable>, also check the
# executable's hash and regenerate every proof with the receipt's exact arguments, failing if any
# differs. The executable comes from the official release archive named in receipt.json; this
# script never downloads it.
#   scripts/alethe/check-fixtures.sh
#   CVC5=/path/to/cvc5-Linux-x86_64-static/bin/cvc5 scripts/alethe/check-fixtures.sh
set -euo pipefail
cd "$(dirname "$0")/../../tests/alethe/cvc5-1.4.2"
python3 -I - "${CVC5:-}" <<'PY'
import hashlib, json, os, resource, subprocess, sys
receipt = json.load(open("receipt.json"))
sha = lambda path: hashlib.sha256(open(path, "rb").read()).hexdigest()
bad = [f for f, h in receipt["files"].items() if sha(f) != h]
if bad:
    sys.exit(f"error: hash mismatch: {bad}")
print(f"alethe fixtures: {len(receipt['files'])} files match receipt.json")
cvc5 = sys.argv[1]
if not cvc5:
    sys.exit(0)
if sha(cvc5) != receipt["executable"]["sha256"]:
    sys.exit("error: CVC5 is not the executable named in receipt.json")
def limits():
    resource.setrlimit(resource.RLIMIT_CPU, (5, 5))
    resource.setrlimit(resource.RLIMIT_AS, (268435456, 268435456))
for run in receipt["runs"]:
    out = subprocess.run([cvc5, *run["args"]], capture_output=True, preexec_fn=limits, check=True).stdout
    if out != open(run["output"], "rb").read():
        sys.exit(f"error: {run['output']} differs from a fresh run")
print(f"alethe fixtures: {len(receipt['runs'])} proofs regenerate identically")
PY
