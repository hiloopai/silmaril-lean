#!/usr/bin/env bash
# Performance of the component subcommands (`validate`, `validate --features all`, `print`,
# `parse` of the printed text) of our Lean binary against the pinned upstream wasm-tools 1.262.0.
#
#   tools/wasm-tools/tests/compval/bench.sh [--runs N] [--max-ratio R] [FILE.wasm...]
#
# Each command runs N times (default 3) per input; the best wall time of each tool is reported
# (seconds), with the ratio ours/upstream. Default inputs: the WIT packages of
# tests/wat/fixtures (4-30 KB) and the WASI 0.3 Rust components of examples/wasip3-rust/dist
# (42 KB - 3.1 MB). As a regression test, `--max-ratio R` exits 1 when some command of ours is
# slower than R times upstream plus 0.5 s (the start-up cost of a Lean binary). Exit 77 when a
# pinned tool or the binary is absent.

set -euo pipefail
root=$(cd "$(dirname "$0")/../../../.." && pwd)
runs=3
max=
files=()
while [[ $# -gt 0 ]]; do
  case $1 in
    --runs) runs=$2; shift 2 ;;
    --max-ratio) max=$2; shift 2 ;;
    -h|--help) sed -n '2,13p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) files+=("$1"); shift ;;
  esac
done
# shellcheck source=../../../wasm-jco/tests/pins.sh
source "$root/tools/wasm-jco/tests/pins.sh"
wt=$WASM_TOOLS
ours=${WASM_TOOLS_LEAN:-$root/.lake/build/bin/wasm-tools-cv}
if [[ ! -x $wt || $(sha256sum "$wt" | cut -d' ' -f1) != "$WASM_TOOLS_SHA256" ]]; then
  echo "compval/bench: SKIP: pinned wasm-tools $WASM_TOOLS_VERSION not found at $wt" >&2
  exit 77
fi
[[ -x $ours ]] || { echo "compval/bench: SKIP: $ours missing" >&2; exit 77; }
if [[ ${#files[@]} -eq 0 ]]; then
  files=("$root"/tests/wat/fixtures/*.wasm "$root"/examples/wasip3-rust/dist/*.wasm)
fi
tmp=$(mktemp -d /tmp/compval-bench.XXXXXX)
trap 'rm -rf "$tmp"' EXIT

best() {
  local b=999999 t s e
  for ((i = 0; i < runs; i++)); do
    s=$(date +%s.%N)
    "$@" >/dev/null 2>&1 || true
    e=$(date +%s.%N)
    t=$(echo "$e - $s" | bc)
    b=$(echo "if ($t < $b) $t else $b" | bc)
  done
  printf '%.3f' "$b"
}

fail=0
printf 'bytes\tfile\tcommand\tours_s\tupstream_s\tratio\n'
for f in "${files[@]}"; do
  sz=$(stat -c %s "$f")
  "$wt" print "$f" -o "$tmp/up.wat" 2>/dev/null || true
  "$ours" print "$f" -o "$tmp/ours.wat" 2>/dev/null || true
  for cmd in validate validate-all print parse; do
    case $cmd in
      validate) a=(validate "$f"); u=(validate "$f") ;;
      validate-all) a=(validate --features all "$f"); u=(validate --features all "$f") ;;
      print) a=(print "$f" -o "$tmp/o.wat"); u=(print "$f" -o "$tmp/u.wat") ;;
      parse) a=(parse "$tmp/ours.wat" -o "$tmp/o.wasm"); u=(parse "$tmp/up.wat" -o "$tmp/u.wasm") ;;
    esac
    o=$(best "$ours" "${a[@]}")
    w=$(best "$wt" "${u[@]}")
    r=$(echo "scale=1; $o / ($w + 0.001)" | bc)
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$sz" "${f#"$root"/}" "$cmd" "$o" "$w" "$r"
    if [[ -n $max ]] && (( $(echo "$o > $max * $w + 0.5" | bc) )); then fail=1; fi
  done
done
exit $fail
