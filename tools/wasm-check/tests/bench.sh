#!/usr/bin/env bash
# Regression test and benchmark of the front end (docs/projects/wasm-binaryen-tooling.md).
#
#   tools/wasm-check/tests/bench.sh [--certs] [--mor] [--regen]
#
# 1. Checks the pinned inputs (tests/inputs/*.wasm) against tests/inputs/SHA256SUMS.
# 2. Runs `wasm-check bench` (the cases of tests.wasm.auto.FrontBench(X), built into the
#    tool) and compares every verdict with tests/expected.tsv; prints wall time and peak memory.
#    Then runs `wasm-check bench --vc` (the VC library's contracts against their
#    demonstration modules and mutants, `Silmaril.Wasm.Auto2.VCLib3.vcBench`, expected verdicts
#    built in) and fails on any unexpected verdict.
# 3. Runs `wasm-check refines` on every pinned module pair (decoding the binaries) and
#    compares the verdict with tests/expected.tsv.
# 4. With --certs: writes the Lean certificate of every refuted pair and checks it with
#    `lake env lean` (kernel replay on the verified interpreter), with time and peak memory.
#    Pairs listed in tests/nocert.txt are not checked. The list used to hold the modules with a
#    memory (a one-page memory did not instantiate in the kernel: stopped at 44 GB after 6 min);
#    `Silmaril.Wasm.Auto2.Kernel` (closed-form data segments, validation-free instances) checks them,
#    and the list is empty.
#    With --mor, each certificate is checked by `lake build --scratch` (a fresh
#    scratch module with a new content hash, so no cache restores it; removed afterwards) instead
#    of `lake env lean`.
#
# --regen rewrites tests/inputs from the tool (then review and commit the diff).
#
# The tool is the lake target `wasm-check` (the build command is $WT_BUILD_HINT of
# tools/wasm-tools/tests/pins.sh); when it is absent the test is skipped (exit 0) with a
# message, so CI without the executable is unaffected.
# Exit status: 0 when every verdict is the expected one (or skipped), 1 otherwise.

set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
# shellcheck source=../../wasm-tools/tests/pins.sh
source "$root/tools/wasm-tools/tests/pins.sh"
bin=${SIL_WASM_CHECK:-$root/.lake/build/bin/wasm-check}
certs=0
regen=0
mor=0
for a in "$@"; do
  case $a in
    --certs) certs=1 ;;
    --regen) regen=1 ;;
    --mor) mor=1 ;;
    *) echo "usage: $0 [--certs] [--mor] [--regen]" >&2; exit 2 ;;
  esac
done

wt_require_ours "$bin" wasm-check

timer=()
if [[ -x /usr/bin/time ]]; then timer=(/usr/bin/time -f '%e s, %M KiB'); fi

if (( regen )); then
  "$bin" bench --out "$here/inputs" >/dev/null || true
  (cd "$here/inputs" && sha256sum ./*.wasm | sed 's# \./# #' > SHA256SUMS)
  echo "regenerated $here/inputs"
fi

echo "== pinned inputs"
(cd "$here/inputs" && sha256sum --quiet -c SHA256SUMS)
echo "ok"

fail=0
expected() { awk -F'\t' -v c="$1" '$1 == c { print $2 }' "$here/expected.tsv"; }

echo "== bench (built-in cases)"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
"${timer[@]}" "$bin" bench 2> "$out/bench.time" > "$out/bench.tsv" || true
cat "$out/bench.tsv"
echo "time, peak memory: $(tail -1 "$out/bench.time")"
while IFS=$'\t' read -r name verdict _ _ _; do
  [[ $name == case ]] && continue
  want=$(expected "$name")
  if [[ $verdict != "$want" ]]; then
    echo "FAIL bench $name: $verdict, expected $want"; fail=1
  fi
done < "$out/bench.tsv"

echo "== bench --vc (the VC library's contracts: memory, callees, globals, arithmetic)"
"$bin" bench --vc > "$out/vc-bench.tsv" || true
cat "$out/vc-bench.tsv"
nvc=0
while IFS=$'\t' read -r name verdict want _ ok; do
  [[ $name == vc-case ]] && continue
  nvc=$((nvc + 1))
  if [[ $ok != true ]]; then echo "FAIL bench --vc $name: $verdict, expected $want"; fail=1; fi
done < "$out/vc-bench.tsv"
echo "$nvc vc cases"

echo "== refines on the pinned binaries"
for spec in "$here"/inputs/*.spec.wasm; do
  name=$(basename "$spec" .spec.wasm)
  impl=$here/inputs/$name.impl.wasm
  json=$("$bin" refines "$impl" "$spec" 0 --lean "$out/$name.lean")
  verdict=$(sed -E 's/.*"report":\{"verdict":("[a-z]+").*/\1/' <<< "$json")
  want=$(expected "$name")
  echo -e "$name\t$verdict"
  if [[ $verdict != "$want" ]]; then
    echo "FAIL refines $name: $verdict, expected $want"; fail=1
  fi
  if (( certs )) && grep -qx "$name" "$here/nocert.txt"; then
    echo "  certificate not checked (memory; tests/nocert.txt)"
  elif (( certs )) && [[ -f $out/$name.lean ]]; then
    if (( mor )); then
      checker=(lake build --scratch "$out/$name.lean")
    else
      checker=(lake env lean "$out/$name.lean")
    fi
    rc=0
    (cd "$root" && "${timer[@]}" "${checker[@]}" > "$out/$name.log" 2> "$out/$name.time") || rc=$?
    if (( rc == 0 )); then
      echo -e "  certificate checked: $(tail -1 "$out/$name.time")"
    else
      cat "$out/$name.log" "$out/$name.time"; echo "FAIL certificate $name"; fail=1
    fi
  fi
done

if (( fail )); then echo "FAILED"; exit 1; fi
echo "all verdicts as expected"
