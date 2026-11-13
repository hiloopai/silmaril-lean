#!/usr/bin/env bash
# The typed rules of `validate` on small hand-written components: our Lean binary against the
# pinned upstream wasm-tools 1.262.0 (exit status only; the message text is not compared).
#
#   tools/wasm-tools/tests/compval/typed.sh
#
# Each `typed/*.wat` (accessor rules in instance and component type declarations, GC
# lowerings) is turned into a binary by upstream `parse` and validated by both tools with
# `--features all`. Cases named `*-gap.wat` are known disagreements (listed under Known
# limitations in docs/projects/wasm-components.md) and are reported, not counted as failures. Exit 1 on
# an unexpected disagreement, 77 when a pinned tool or the binary is absent.

set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
# shellcheck source=../../../wasm-jco/tests/pins.sh
source "$root/tools/wasm-jco/tests/pins.sh"
wt=$WASM_TOOLS
ours=${WASM_TOOLS_LEAN:-$root/.lake/build/bin/wasm-tools-cv}
if [[ ! -x $wt || $(sha256sum "$wt" | cut -d' ' -f1) != "$WASM_TOOLS_SHA256" ]]; then
  echo "compval/typed: SKIP: pinned wasm-tools $WASM_TOOLS_VERSION not found at $wt" >&2
  exit 77
fi
[[ -x $ours ]] || { echo "compval/typed: SKIP: $ours missing" >&2; exit 77; }
d=$(mktemp -d /tmp/compval-typed.XXXXXX)
trap 'rm -rf "$d"' EXIT
pass=0 fail=0 gap=0
for f in "$here"/typed/*.wat; do
  n=$(basename "$f" .wat)
  if ! "$wt" parse "$f" -o "$d/$n.wasm" 2>/dev/null; then
    echo "FAIL $n: upstream parse failed"; fail=$((fail + 1)); continue
  fi
  "$wt" validate --features all "$d/$n.wasm" >/dev/null 2>&1; u=$?
  "$ours" validate --features all "$d/$n.wasm" >/dev/null 2>&1; o=$?
  [[ $u -ne 0 ]] && u=1; [[ $o -ne 0 ]] && o=1
  if [[ $u == "$o" ]]; then echo "ok   $n (exit $u)"; pass=$((pass + 1))
  elif [[ $n == *-gap ]]; then echo "gap  $n (upstream $u, ours $o)"; gap=$((gap + 1))
  else echo "FAIL $n (upstream $u, ours $o)"; fail=$((fail + 1)); fi
done
echo "compval/typed: $pass agree, $gap known gaps, $fail failed"
[[ $fail -eq 0 ]]
