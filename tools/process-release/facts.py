#!/usr/bin/env python3
"""Generate and verify the small machine-readable process-release facts file."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

FACTS = Path("docs/facts.json")
SOURCE = Path(".process-promotion.json")
FIXTURES = Path("examples/verification-projects/theorem-dev/lps-probes/probes")
DATA = Path("Silmaril/Process/LPS/Probes/Data")
CORPUS = Path("Silmaril/Process/LPS/Problems/X86Probes")


def collect(root: Path) -> dict:
    promotion = json.loads((root / SOURCE).read_text())
    topics = [
        "Model", "Shapes", "Syscalls/Linux", "Syscalls/X86", "X86", "RiscV",
        "Probes", "Musl", "Sha256",
    ]
    return {
        "source_commit": promotion["source_commit"],
        "translated_syscall_arms": 90,
        "probe_fixtures": len(list((root / FIXTURES).glob("*.json"))),
        "probe_lean_data_modules": len(list((root / DATA).glob("*.lean"))),
        "x86_probe_problem_modules": len(list((root / CORPUS).rglob("*.lean"))),
        "public_process_header_topics": topics,
        "verification_commands": [
            "make library",
            "make demo-process demo-sha256",
            "python3 apps/sha256sum-min/build.py --verify-only",
            "python3 -B tools/verification-projects/lps_probes.py check --offline",
            "python3 -B tools/verification-projects/x86_probe_problems.py check",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="fail if docs/facts.json is stale")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    expected = json.dumps(collect(root), indent=2) + "\n"
    path = root / FACTS
    if args.check:
        actual = path.read_text()
        if actual != expected:
            print(f"{FACTS}: stale; regenerate with {Path(__file__).name}")
            return 1
        print(f"{FACTS}: up to date")
        return 0
    path.write_text(expected)
    print(f"wrote {FACTS}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
