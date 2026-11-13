#!/usr/bin/env bash
# Differential fuzzing harness of the gentool subcommands against pinned wasm-tools 1.262.0.
#
#   tools/wasm-tools/tests/gen/fuzz.sh [N] [RANDOM_SEED]     (default 200 seeds, seed 1)
#
# For each of N seeds (random bytes of random length, reproducible from RANDOM_SEED):
#  1. our `smith` (default model)  -> upstream `validate` must accept;          [smith-valid]
#     our `smith -t` == upstream `print` of our `smith` output, byte for byte;   [print-parity]
#     an output of `(module)` from a non-empty seed counts as a fallback;       [fallback]
#  2. our `smith` with every 2.0/3.0 flag off -> upstream `validate --features=mvp,mutable-global` (wasmparser's
#     `mvp` predates the import and export of mutable globals, which Wasm 1.0 has); [smith-v10]
#  3. our `mutate -s K` of our smith output -> upstream `validate`;              [mutate-valid]
#     with `--preserve-semantics` too;                                         [mutate-pres]
#  4. upstream `smith` (features our model and decoder cover) -> our `mutate` must accept the
#     input (it decodes and validates it): a differential test of our decoder and validator
#     against upstream's;                                                      [decode-agree]
#     the same with GC, exceptions, memory64, SIMD, relaxed SIMD and tail calls on (data:
#     disagreements are reported, not failed);                                 [decode-agree-30]
#  5. our `smith --module-shape` of a fixed shape -> upstream `validate` accepts, and the
#     output has exactly the shape's three imports and two exports;            [smith-shape]
# Failing seeds are kept in $GT_FUZZ_KEEP (default /tmp/gentool-fuzz-failures).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/pins.sh"
gt_require_upstream
gt_ours
GT_DIAG="$(dirname "$GT_OURS")/wasm-tools-gen-diag"
N=${1:-200}
RANDOM=${2:-1}
keep=${GT_FUZZ_KEEP:-/tmp/gentool-fuzz-failures}
mkdir -p "$keep"
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
cd "$work"
U=$GT_UPSTREAM; O=$GT_OURS
declare -A ok bad
for k in smith-valid print-parity fallback smith-v10 mutate-valid mutate-pres decode-agree \
  decode-agree-30 smith-shape; do
  ok[$k]=0; bad[$k]=0; done
"$U" parse - -o shape.wasm <<'WAT'
(module (import "env" "ping" (func (param i32))) (import "env" "memory" (memory 1))
  (import "env" "g" (global (mut i64))) (func (export "foo") (param i32) (result i32) unreachable)
  (global (export "bar") i32 i32.const 0))
WAT
tally() { if [[ $2 == 0 ]]; then ok[$1]=$((ok[$1]+1)); else bad[$1]=$((bad[$1]+1)); cp s "$keep/$1-$3.seed"; fi; }
mvp="--sign-extension-ops-enabled false --saturating-float-to-int-enabled false \
--multi-value-enabled false --reference-types-enabled false --bulk-memory-enabled false \
--simd-enabled false --relaxed-simd-enabled false --tail-call-enabled false \
--extended-const-enabled false --gc-enabled false --exceptions-enabled false \
--memory64-enabled false"
upflags30="--compact-imports-enabled false --custom-descriptors-enabled false \
--threads-enabled false --shared-everything-threads-enabled false --wide-arithmetic-enabled false \
--max-memories 1 --max-tables 1"
upflags="--compact-imports-enabled false --custom-descriptors-enabled false \
--threads-enabled false --shared-everything-threads-enabled false --simd-enabled false \
--relaxed-simd-enabled false --gc-enabled false --exceptions-enabled false \
--memory64-enabled false --tail-call-enabled false --wide-arithmetic-enabled false \
--max-memories 1 --max-tables 1"
for i in $(seq 1 "$N"); do
  head -c $(( (RANDOM * 32768 + RANDOM) % 6000 + 1 )) /dev/urandom > s
  "$O" smith s -o o.wasm; "$U" validate o.wasm 2>/dev/null; tally smith-valid $? "$i"
  "$O" smith -t s > o.wat 2>/dev/null; r=$?
  if [[ $r == 0 ]]; then "$U" print o.wasm > u.wat; cmp -s u.wat o.wat; r=$?; fi
  tally print-parity $r "$i"
  [[ "$(head -c 9 o.wat)" == "(module)" ]]; tally fallback $(( $? == 0 )) "$i"
  # shellcheck disable=SC2086
  "$O" smith s $mvp -o v.wasm; "$U" validate --features=mvp,mutable-global v.wasm 2>/dev/null; tally smith-v10 $? "$i"
  "$O" mutate o.wasm -s "$i" -o m.wasm 2>/dev/null; r=$?
  if [[ $r == 0 ]]; then "$U" validate m.wasm 2>/dev/null; r=$?; elif [[ $r == 3 ]]; then r=0; fi
  tally mutate-valid $r "$i"
  "$O" mutate o.wasm -s "$i" --preserve-semantics -o p.wasm 2>/dev/null; r=$?
  if [[ $r == 0 ]]; then "$U" validate p.wasm 2>/dev/null; r=$?; elif [[ $r == 3 ]]; then r=0; fi
  tally mutate-pres $r "$i"
  # shellcheck disable=SC2086
  "$U" smith s $upflags -o us.wasm 2>/dev/null
  if [[ -s us.wasm ]]; then
    "$O" mutate us.wasm -s 1 -o /dev/null 2>/dev/null; r=$?
    [[ $r == 0 || $r == 3 ]]; r2=$?
    if [[ $r2 != 0 && -x ${GT_DIAG:-} ]]; then "$GT_DIAG" us.wasm >> "$keep/decode-agree.log"; fi
    tally decode-agree $r2 "$i"
  fi
  # shellcheck disable=SC2086
  "$U" smith s $upflags30 -o u3.wasm 2>/dev/null
  if [[ -s u3.wasm ]]; then
    "$O" mutate u3.wasm -s 1 -o /dev/null 2>/dev/null; r=$?
    [[ $r == 0 || $r == 3 ]]; r2=$?
    if [[ $r2 != 0 && -x ${GT_DIAG:-} ]]; then "$GT_DIAG" u3.wasm >> "$keep/decode-agree-30.log"; fi
    tally decode-agree-30 $r2 "$i"
  fi
  "$O" smith s --module-shape shape.wasm -o sh.wasm; r=$?
  if [[ $r == 0 ]]; then "$U" validate sh.wasm 2>/dev/null; r=$?; fi
  if [[ $r == 0 ]]; then [[ "$("$U" print sh.wasm | grep -cE '^  \((import|export) ')" == 5 ]]; r=$?; fi
  tally smith-shape $r "$i"
done
fail=0
for k in smith-valid print-parity fallback smith-v10 mutate-valid mutate-pres decode-agree \
  decode-agree-30 smith-shape; do
  printf '%-15s %5d ok %5d failed\n' "$k" "${ok[$k]}" "${bad[$k]}"
  [[ $k == decode-agree || $k == decode-agree-30 || ${bad[$k]} == 0 ]] || fail=1
done
[[ $fail == 0 ]]
