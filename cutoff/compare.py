"""Compare two build-tree snapshots and summarise the rebuild."""

import json
import re
import sys
from pathlib import Path

LIB = ".lake/build/lib/lean/"
BASE = "Silmaril/X86/Machine"
SUFFIXES = (".olean", ".olean.server", ".olean.private", ".ilean", ".ir", ".ir.sig", ".trace", ".hash")


def module_of(path: str) -> tuple[str, str] | None:
    if not path.startswith(LIB):
        return None
    rel = path[len(LIB):]
    for suffix in sorted(SUFFIXES, key=len, reverse=True):
        if rel.endswith(suffix):
            return rel[: -len(suffix)].replace("/", "."), suffix
    return None


def main() -> None:
    before = json.loads(Path(sys.argv[1]).read_text())
    after = json.loads(Path(sys.argv[2]).read_text())
    log = Path(sys.argv[3]).read_text(errors="replace")
    wall = float(Path(sys.argv[4]).read_text())
    touched, changed = set(), set()
    base = {}
    for path, (size, mtime, digest) in after.items():
        old = before.get(path)
        info = module_of(path)
        if info and info[0] == BASE.replace("/", "."):
            base[info[1]] = {
                "before": old[2] if old else None,
                "after": digest,
                "bytes_changed": old is None or old[2] != digest,
                "rewritten": old is None or old[1] != mtime,
            }
        if old is None or old[1] != mtime:
            if info and info[1] == ".olean":
                touched.add(info[0])
            if info and info[1] == ".olean" and (old is None or old[2] != digest):
                changed.add(info[0])
    built = sorted(set(re.findall(r"Built (Silmaril[\w.]*|ProjectSelfTest[\w.]*)\b(?!:)", log)))
    built_jobs = re.findall(r"Built (\S+)", log)
    base_mod = BASE.replace("/", ".")
    print(json.dumps({
        "wall_seconds": wall,
        "modules_olean_rewritten": len(touched),
        "downstream_olean_rewritten": len(touched - {base_mod}),
        "modules_public_olean_bytes_changed": sorted(changed),
        "lake_built_module_lines": len(built),
        "lake_built_jobs_all": len(built_jobs),
        "downstream_built_modules": [m for m in built if m != base_mod][:50],
        "base_artifacts": base,
    }, indent=1))


if __name__ == "__main__":
    main()
