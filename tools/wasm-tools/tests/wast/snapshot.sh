#!/usr/bin/env bash
# `wast --snapshot DIR --assert snapshot-*`: blessing (BLESS=1) and checking, ours against
# ours and against snapshots the pinned wasm-tools 1.262.0 blessed.
#
#   tools/wasm-tools/tests/wast/snapshot.sh [--bin PATH]
#
# Skips the upstream comparisons (not the self-checks) when the pinned binary is absent.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
source "$here/../pins.sh"
bin=$root/.lake/build/bin/wasm-tools
[[ ${1:-} == --bin ]] && bin=$2
wt_require_ours "$bin" wasm-tools
bin=$(cd "$(dirname "$bin")" && pwd)/$(basename "$bin")
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/w/tests"
cd "$tmp/w"
spec=$(wt_spec_core)
[[ -n $spec ]] || { echo "SKIP: the spec testsuite pin is not unpacked (fetch-pins.sh spec)"; exit 0; }
cp "$spec/i32.wast" tests/i32.wast
printf '(module (func (export "f") (result i32) (i32.const 1)))\n(module binary "\\00asm" "\\01\\00\\00\\00")\n' > tests/small.wast
pass=0 fail=0
check() { # name expected-rc command...
  local name=$1 want=$2; shift 2
  "$@" >/dev/null 2>"$tmp/err"; local rc=$?
  if [[ $rc == "$want" ]]; then pass=$((pass + 1)); echo "PASS $name (rc=$rc)"
  else fail=$((fail + 1)); echo "FAIL $name (rc=$rc, want $want)"; head -12 "$tmp/err" | sed 's/^/    /'; fi
}
A=(-a snapshot-print,snapshot-json --ignore-error-messages)
check "bless ours" 0 env BLESS=1 "$bin" wast "${A[@]}" --snapshot snap tests/small.wast
check "snapshot files written" 0 test -f snap/small.wast.json -a -f snap/small.wast/0.print
check "check ours against ours" 0 env -u BLESS "$bin" wast "${A[@]}" --snapshot snap tests/small.wast
echo '(module)' >> snap/small.wast/0.print
check "a changed print snapshot fails" 1 env -u BLESS "$bin" wast "${A[@]}" --snapshot snap tests/small.wast
check "no --snapshot directory fails" 1 env -u BLESS "$bin" wast "${A[@]}" tests/small.wast
check "missing snapshot fails" 1 env -u BLESS "$bin" wast "${A[@]}" --snapshot nothing tests/small.wast
if [[ -x $WT_UPSTREAM ]]; then
  for f in small i32; do
    check "upstream blesses $f json" 0 env BLESS=1 "$WT_UPSTREAM" wast -a snapshot-json --ignore-error-messages --snapshot up tests/$f.wast
    check "ours matches upstream's $f json snapshot" 0 env -u BLESS "$bin" wast -a snapshot-json --ignore-error-messages --snapshot up tests/$f.wast
  done
  check "upstream blesses small print" 0 env BLESS=1 "$WT_UPSTREAM" wast -a snapshot-print --ignore-error-messages --snapshot up tests/small.wast
  # the merged binary prints in wasmprinter's format: the print snapshot matches
  check "ours matches upstream's print snapshot" 0 env -u BLESS "$bin" wast -a snapshot-print --ignore-error-messages --snapshot up tests/small.wast
else
  echo "skip: pinned wasm-tools not installed; upstream snapshot comparisons skipped"
fi
echo "SUMMARY snapshot pass=$pass fail=$fail"
((fail == 0))
