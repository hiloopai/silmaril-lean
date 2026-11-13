#!/usr/bin/env bash
# Differential test of our `wit-smith` against pinned wasm-tools 1.262.0.
#
#   tools/wasm-tools/tests/gen/wit-smith.sh [N] [RANDOM_SEED]     (default 200 seeds, seed 1)
#
# For each of N random seeds and each flag set (default; --async --futures --streams
# --error-context; --fixed-length-lists --world-include; --arbitrary-config):
#   our `wit-smith` -> upstream `validate --features all` accepts it (as upstream wit-smith
#                      checks its own output);                            [valid]
#                   -> upstream `component wit` decodes it as a package;   [wit]
#                   -> our `wit-smith -t` is upstream `print`'s text?      [print-same] (counted)
#                   -> the fallback was not used (our -v message);         [no-fallback] (counted)
# Upstream's own `wit-smith` on the same seed is run for the speed comparison only (outputs
# differ by design). Failing seeds are kept in $GT_FUZZ_KEEP (default /tmp/gentool-fuzz-failures).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/pins.sh"
gt_require_upstream
gt_ours
N=${1:-200}
RANDOM=${2:-1}
keep=${GT_FUZZ_KEEP:-/tmp/gentool-fuzz-failures}
mkdir -p "$keep"
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
cd "$work"
U=$GT_UPSTREAM; O=$GT_OURS
flagsets=("" "--async --futures --streams --error-context" "--fixed-length-lists --world-include" "--arbitrary-config")
fail=0
for fs in "${flagsets[@]}"; do
  valid=0; wit=0; same=0; nofb=0; bad=0
  for i in $(seq 1 "$N"); do
    head -c $(( (RANDOM * 32768 + RANDOM) % 4000 + 1 )) /dev/urandom > s
    # shellcheck disable=SC2086
    "$O" wit-smith s $fs -v -o o.wasm 2>o.err
    if [[ $? != 0 ]]; then bad=$((bad+1)); cp s "$keep/wit-smith-run-$i.seed"; continue; fi
    if grep -q "wrote the fallback" o.err; then cat o.err >> "$keep/wit-smith-fallback.log"; else nofb=$((nofb+1)); fi
    if "$U" validate --features all o.wasm 2>/dev/null; then valid=$((valid+1)); else cp s "$keep/wit-smith-valid-$i.seed"; fi
    if "$U" component wit o.wasm >/dev/null 2>&1; then wit=$((wit+1)); else cp s "$keep/wit-smith-wit-$i.seed"; fi
    # shellcheck disable=SC2086
    "$O" wit-smith s $fs -t > o.wat 2>/dev/null; "$U" print o.wasm > u.wat 2>/dev/null
    cmp -s o.wat u.wat && same=$((same+1))
  done
  printf 'flags [%s]: runs %d ok (%d failed), upstream-valid %d, component-wit %d, no-fallback %d, -t equal to upstream print %d\n' \
    "${fs:-default}" $((N - bad)) "$bad" "$valid" "$wit" "$nofb" "$same"
  [[ $bad == 0 && $valid == $((N - bad)) && $wit == $((N - bad)) ]] || fail=1
done
[[ $fail == 0 ]]
