#!/usr/bin/env python3
"""Check or refresh public source hashes (the manifest excludes itself)."""

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--update", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    manifest_path = root / "SOURCE-MANIFEST.json"
    manifest = json.loads(manifest_path.read_text())
    names = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
        cwd=root).decode().split("\0")
    files = []
    external = set()
    for name in sorted(set(names)):
        path = root / name
        if not name or name == manifest_path.name or not path.is_file():
            continue
        data = path.read_bytes()
        files.append({"path": name, "sha256": hashlib.sha256(data).hexdigest(),
                      "bytes": len(data)})
        if path.suffix == ".lean":
            external.update(dep for dep in re.findall(
                r"^(?:(?:public|private) )?import\s+(?:all\s+)?([\w.]+)",
                data.decode(), re.M) if not dep.startswith("Silmaril"))
    expected = dict(manifest, files=files, external_imports=sorted(external),
                    scope="Public Silmaril library, seven Wasm tools, documentation and development tooling")
    if args.update:
        manifest_path.write_text(json.dumps(expected, indent=2) + "\n")
        print(f"Updated hashes for {len(files)} public files")
    elif manifest != expected:
        parser.exit(1, "Source inventory changed; run python3 scripts/source-manifest.py --update\n")
    else:
        print(f"Source hashes pass: {len(files)} public files (manifest excludes itself)")


if __name__ == "__main__":
    main()
