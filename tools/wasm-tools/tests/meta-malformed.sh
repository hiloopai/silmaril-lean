#!/usr/bin/env bash
# Malformed-binary differential test of `metadata show` and `demangle` (error messages with
# wasmparser's offsets, byte for byte) against the pinned wasm-tools 1.262.0.
#
#   tools/wasm-tools/tests/meta-malformed.sh [--ours BIN] [-n CASES] [--seed S]
#
# Seeds: the WIT packages and the WASI 0.3 components of the vendored corpus (tests/corpus).
# Skips (exit 0) when the pinned binary is absent; exit 1 when any case differs.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
# shellcheck source=pins.sh
source "$here/pins.sh"
WT=$WT_UPSTREAM
OURS=$root/.lake/build/bin/wasm-tools
N=500; SEED=1
while [[ $# -gt 0 ]]; do
  case $1 in
    --ours) OURS=$2; shift 2 ;; -n) N=$2; shift 2 ;; --seed) SEED=$2; shift 2 ;;
    *) echo "usage: $0 [--ours BIN] [-n CASES] [--seed S]" >&2; exit 2 ;;
  esac
done
wt_require_upstream
wt_require_ours "$OURS" wasm-tools
seeds=()
wt_corpus_check
for n in demo wasi-cli-0.2.12 wasi-clocks-0.2.12 wasi-io-0.2.12 wasi-random-0.2.12 cat echo hello; do
  seeds+=("$WT_CORPUS_DIR/$n.wasm")
done
python3 -I "$here/meta-malformed.py" "$WT" "$OURS" "$N" "$SEED" "${seeds[@]}"
