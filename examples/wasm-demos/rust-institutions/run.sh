#!/usr/bin/env bash
# Build every demo crate for wasm32, then ask wasm-verify the questions in expected.txt and
# compare each verdict with the expected one. Prints each JSON report.
# Usage: ./run.sh [path/to/wasm-verify]
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
verify=${1:-$root/.lake/build/bin/wasm-verify}
[ -x "$verify" ] || { echo "build it first: (cd $root && lake build wasm-verify)" >&2; exit 2; }
cd "$here"
cargo build --quiet --release --target wasm32-unknown-unknown -p adder -p door -p door-buggy -p leaf-door-opens -p leaf-overflow
fail=0
while read -r crate prop imp exp want; do
  case "$crate" in ''|\#*) continue ;; esac
  wasm=target/wasm32-unknown-unknown/release/$crate.wasm
  if [ "$exp" = - ]; then args=("$prop" "$imp"); else args=("$prop" "$imp" "$exp"); fi
  out=$("$verify" "$wasm" "${args[@]}")
  got=$(sed -E 's/^\{"verdict":"([a-z]+)".*/\1/' <<<"$out")
  mark=ok; [ "$got" = "$want" ] || { mark=MISMATCH; fail=1; }
  printf '%-8s %-10s %-18s %-11s %-11s -> %-8s [%s]\n  %s\n' \
    "$mark" "$crate" "$prop" "$imp" "$exp" "$got" "want $want" "$out"
done < expected.txt

# The Lean quotation of the binaries must match this build.
cargo build --quiet -p wasm2lean
rel=target/wasm32-unknown-unknown/release
lean=$root/Silmaril/Wasm/Examples/RustInst/Defs.lean
target/debug/wasm2lean lean "$rel/RustInst.Defs.lean" Silmaril.Wasm.Examples.RustInst \
  adder=$rel/adder.wasm door=$rel/door.wasm doorBuggy=$rel/door_buggy.wasm \
  leafDoorOpens=$rel/leaf_door_opens.wasm leafOverflow=$rel/leaf_overflow.wasm
if [ "${REGEN:-0}" = 1 ]; then
  cp "$rel/RustInst.Defs.lean" "$lean"; echo "wrote $lean"
elif cmp -s "$rel/RustInst.Defs.lean" "$lean"; then
  echo "ok       $lean matches this build"
else
  echo "MISMATCH $lean differs from this build (REGEN=1 ./run.sh to rewrite it)"; fail=1
fi
exit $fail
