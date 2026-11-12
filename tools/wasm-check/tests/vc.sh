#!/usr/bin/env bash
# Regression test of `wasm-check vc` (docs/projects/wasm-binaryen-tooling.md): each
# pinned binary of tests/inputs (and, for paths with a directory, of tests/, e.g.
# tests/vc-inputs) against a contract of the VC library (`Silmaril.Wasm.Auto2.VCLib3.entriesM3`), with
# the expected number of conditions, of conditions that are not accepted (normalised,
# renamed; `null` when a callee is missing or not accepted, or the types differ), and the
# verdict (tests/vc-expected.tsv). An input `FILE#K` checks function export `K` (default `0`).
#
#   tools/wasm-check/tests/vc.sh [--certs-dir DIR] [--regen]
#
# tests/vc-inputs holds the binaries of the library's demonstration modules (memory, callees),
# written by `wasm-check vc-emit` and pinned by tests/vc-inputs/SHA256SUMS; --regen rewrites
# them (then review and commit the diff).
#
# With --certs-dir DIR, writes the certificate of every `proved` line to DIR (check them as
# modules with `lake build`, never with a bare `lean`). Skips (exit 0) when the tool is
# absent (build it with `lake build wasm-check`).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
bin=${SIL_WASM_CHECK:-$root/.lake/build/bin/wasm-check}
certs=
regen=0
while (( $# )); do
  case $1 in
    --certs-dir) certs=$2; mkdir -p "$certs"; shift 2 ;;
    --regen) regen=1; shift ;;
    *) echo "usage: $0 [--certs-dir DIR] [--regen]" >&2; exit 2 ;;
  esac
done
if [[ ! -x $bin ]]; then
  echo "SKIP: $bin not found (build it with lake build wasm-check)"
  exit 0
fi
if (( regen )); then
  "$bin" vc-emit "$here/vc-inputs" >/dev/null
  (cd "$here/vc-inputs" && sha256sum ./*.wasm | sed 's# \./# #' > SHA256SUMS)
  echo "regenerated $here/vc-inputs"
fi
(cd "$here/vc-inputs" && sha256sum --quiet -c SHA256SUMS)
fail=0
n=0
while IFS=$'\t' read -r input contract conds missing verdict; do
  [[ $input == input ]] && continue
  n=$((n + 1))
  exp=0
  if [[ $input == *'#'* ]]; then exp=${input##*#}; input=${input%#*}; fi
  args=()
  if [[ -n $certs && $verdict == proved ]]; then
    base=${input##*/}
    args=(--lean "$certs/${base%.wasm}_${exp}_$contract.lean")
  fi
  path=$here/inputs/$input
  [[ $input == */* ]] && path=$here/$input
  json=$("$bin" vc "$path" "$exp" "$contract" "${args[@]}")
  got=$(sed -E 's/.*"conditions":([0-9]+),"missing":([0-9a-z]+),"verdict":"([a-z]+)".*/\1\t\2\t\3/' <<< "$json")
  want=$(printf '%s\t%s\t%s' "$conds" "$missing" "$verdict")
  echo -e "$input#$exp\t$contract\t$got"
  if [[ $got != "$want" ]]; then echo "FAIL $input $contract: $got, expected $want"; fail=1; fi
done < "$here/vc-expected.tsv"
if (( fail )); then echo "FAILED"; exit 1; fi
echo "all $n vc verdicts as expected"
