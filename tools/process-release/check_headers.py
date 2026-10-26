#!/usr/bin/env python3
"""Check the process release's public header and proof/raw layout."""
from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
TOPICS = (
    "Model", "Shapes", "Syscalls/Linux", "Syscalls/X86", "X86", "RiscV",
    "Probes", "Musl", "Sha256",
)


def header(path: Path) -> bool:
    return path.name in {"Defs.lean", "Thms.lean"}


def main() -> int:
    errors: list[str] = []
    for topic in TOPICS:
        path = ROOT / "Silmaril" / "Process" / topic
        for name in ("Defs.lean", "Thms.lean"):
            file = path / name
            if not file.exists():
                errors.append(f"missing public header: {file.relative_to(ROOT)}")
    for file in (ROOT / "Silmaril" / "Process").rglob("*.lean"):
        if not header(file):
            continue
        text = file.read_text()
        if re.search(r"^\s*(?:private |protected )?axiom\b", text, re.MULTILINE):
            errors.append(f"axiom in public header: {file.relative_to(ROOT)}")
        if "native_decide" in text:
            errors.append(f"native_decide in public header: {file.relative_to(ROOT)}")
        # A public header can contain a tiny one-line proof, but longer proof
        # blocks belong under Silmaril/Proofs or Silmaril/Raw.
        for match in re.finditer(r"\bby\s*\n((?:[^\n]*\n){4,})", text):
            errors.append(f"long proof block in public header: {file.relative_to(ROOT)}")
            break
    if errors:
        print("process header/layout check: FAILED", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1
    print(f"process header/layout check: {len(TOPICS)} topics have Defs/Thms headers")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
