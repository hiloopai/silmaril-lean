#!/usr/bin/env bash
# Capture the help texts of the meta subcommands from the pinned wasm-tools 1.262.0
# (COLUMNS unset, stdout not a terminal), then regenerate Silmaril/Wasm/Tools/Meta/Help/Defs.lean.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
# shellcheck source=pins.sh
source "$here/pins.sh"
wt_require_upstream
WT=$WT_UPSTREAM
d=$here/help
run() { env -u COLUMNS "$WT" "$@"; }
run demangle -h > "$d/demangle-h.txt"; run demangle --help > "$d/demangle-help.txt"
run metadata -h > "$d/metadata-h.txt"; run metadata help help > "$d/metadata-help-help.txt"
for s in show add; do run metadata $s -h > "$d/metadata-$s-h.txt"; run metadata $s --help > "$d/metadata-$s-help.txt"; done
run addr2line -h > "$d/addr2line-h.txt"; run addr2line --help > "$d/addr2line-help.txt"
python3 "$here/gen-help.py" "$root"
