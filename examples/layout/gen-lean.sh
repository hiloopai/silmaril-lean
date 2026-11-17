#!/usr/bin/env bash
# Regenerate Silmaril/Data/Layout/Bitfield/Examples/Defs.lean from cases.h and the two measurements.
#   examples/layout/gen-lean.sh [--check]
set -euo pipefail
cd "$(dirname "$0")/../.."
out=Silmaril/Data/Layout/Bitfield/Examples/Defs.lean
tmp=$(mktemp)
python3 -I scripts/layout/gen.py examples/layout/cases.h examples/layout/gcc-x86_64.txt examples/layout/msvc-x64.txt "$tmp"
if [ "${1:-}" = --check ]; then cmp -s "$tmp" "$out" || { echo "gen-lean.sh: $out differs" >&2; exit 1; }; rm -f "$tmp"
else mkdir -p "$(dirname "$out")"; mv "$tmp" "$out"; fi
