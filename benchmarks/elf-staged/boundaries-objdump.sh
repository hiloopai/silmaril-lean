#!/usr/bin/env bash
# Instruction boundaries of a section, from GNU objdump's linear sweep, as `offset length`
# lines (file offsets in hex, lengths in decimal): the tile certificate `elf-staged` checks.
#
#   boundaries-objdump.sh FILE [SECTION]      (default SECTION: .text)
#
# Untrusted tooling: a wrong boundary makes the check fail, never a false theorem.
set -euo pipefail
file=$1; sec=${2:-.text}
objdump -d -w --insn-width=15 -j "$sec" "$file" | python3 -I -c '
import re, subprocess, sys
f, sec = sys.argv[1], sys.argv[2]
addr = off = None
for line in subprocess.run(["readelf", "-SW", f], capture_output=True, text=True).stdout.splitlines():
    m = re.search(r"\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)", line)
    if m and m.group(1) == sec:
        addr, off = int(m.group(2), 16), int(m.group(3), 16)
        break
if addr is None:
    sys.exit(f"no section {sec}")
out = sys.stdout
for line in sys.stdin:
    m = re.match(r"^\s*([0-9a-f]+):\t([0-9a-f ]+)\t", line)
    if m:
        n = len(m.group(2).split())
        if n:
            out.write(f"{int(m.group(1), 16) - addr + off:#x} {n}\n")
' "$file" "$sec"
