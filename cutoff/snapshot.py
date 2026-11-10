"""Record size, mtime and sha256 of every file in the root package's Lake build tree."""

import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(".lake/build")


def main() -> None:
    out = {}
    for path in sorted(ROOT.rglob("*")):
        if path.is_file() and not path.is_symlink():
            stat = path.stat()
            out[str(path)] = [stat.st_size, stat.st_mtime_ns, hashlib.sha256(path.read_bytes()).hexdigest()]
    Path(sys.argv[1]).write_text(json.dumps(out))


if __name__ == "__main__":
    main()
