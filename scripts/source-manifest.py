#!/usr/bin/env python3
"""Write an optional local hash and size inventory of tracked working-tree files."""

import hashlib
import json
import subprocess
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    manifest_path = root / "SOURCE-MANIFEST.json"
    names = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached"],
        cwd=root).decode().split("\0")
    files = []
    for name in sorted(set(names)):
        path = root / name
        if not name or name == manifest_path.name or not path.is_file():
            continue
        data = path.read_bytes()
        files.append({"path": name, "sha256": hashlib.sha256(data).hexdigest(),
                      "bytes": len(data)})
    manifest = {"schema_version": 1, "files": files}
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Wrote {manifest_path.name}: {len(files)} tracked files")


if __name__ == "__main__":
    main()
