#!/usr/bin/env python3
"""Record the upstream outcomes of the golden command-line suites.

python3 -I tools/wasm-tools/tests/golden-capture.py UPSTREAM [SUITE]...

Runs every case of tools/wasm-tools/tests/golden/SUITE.json (all suites by default) with
UPSTREAM, the pinned wasm-tools 1.262.0 (golden-capture.sh checks its SHA-256 and passes it),
exactly as tools/wasm-tools/test-cli.py runs the binary under test, and writes the outcome
into each case's "expect". Everything else in the file (fixtures, modes, "known" notes) is
kept. Review the diff of golden/ before committing it.
"""

import importlib.util
import json
import sys

sys.dont_write_bytecode = True
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("test_cli", HERE.parent / "test-cli.py")
test_cli = importlib.util.module_from_spec(spec)
spec.loader.exec_module(test_cli)


def main(argv):
    if not argv:
        print(__doc__, file=sys.stderr)
        return 2
    upstream = Path(argv[0]).resolve()
    names = argv[1:] or sorted(p.stem for p in test_cli.GOLDEN.glob("*.json"))
    for name in names:
        path = test_cli.GOLDEN / f"{name}.json"
        suite = json.loads(path.read_text())
        for case in suite["cases"]:
            case["expect"] = test_cli.run(upstream, suite, case["args"], case.get("stdin"))
        path.write_text(json.dumps(suite, indent=1, ensure_ascii=False) + "\n")
        print(f"{name}: {len(suite['cases'])} cases recorded")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
