#!/usr/bin/env bash
# Re-record the golden command-line suites (tools/wasm-tools/tests/golden/*.json) from the
# pinned wasm-tools 1.262.0, whose SHA-256 is checked first; skips without it.
#
#   tools/wasm-tools/tests/golden-capture.sh [SUITE]...
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
# shellcheck source=pins.sh
source "$here/pins.sh"
wt_require_upstream
exec python3 -I "$here/golden-capture.py" "$WT_UPSTREAM" "$@"
