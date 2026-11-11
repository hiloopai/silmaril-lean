#!/usr/bin/env bash
# Performance of validate, objdump and strip against wasm-tools 1.262.0.
#
#   tools/wasm-tools/tests/bench.sh [--runs N] [--check]
#
# Inputs, from KB to MB: tests/corpus/pf-example.wasm (a tiny module), the fetched WASI adapter
# wasi_snapshot_preview1.command.wasm (51 KB module, pins.sh), the core modules nested in
# tests/corpus/cat.wasm (44 KB) and, when $WT_CAT_DEBUG is set (pins.sh), cat-debug.wasm (3.1 MB,
# with DWARF), and the components cat.wasm (48 KB) and cat-debug.wasm (3.1 MB). Inputs that are
# absent are skipped. Prints the median
# wall time of N runs (default 5) per tool, subcommand and input.
#
# --check: a regression test; fails when one of our times exceeds 2x its entry in
# tools/wasm-tools/tests/bench-baseline.tsv plus 0.1 s. Skips (status 0) without the pinned
# wasm-tools or our binary.

set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
# shellcheck source=pins.sh
source "$here/pins.sh"
wt_require_upstream
ours=${WASM_TOOLS_OURS:-$repo/.lake/build/bin/wasm-tools}
wt_require_ours "$ours" wasm-tools

runs=5
check=0
while [[ $# -gt 0 ]]; do
  case $1 in
    --runs) runs=$2; shift 2 ;;
    --check) check=1; shift ;;
    *) echo "usage: $0 [--runs N] [--check]" >&2; exit 2 ;;
  esac
done

tmp=$(mktemp -d /tmp/wasm-tools-bench.XXXXXX)
trap 'rm -rf "$tmp"' EXIT

# The first nested core module of a component, by the range objdump prints.
extract() {
  local comp=$1 dst=$2 out line start stop
  out=$("$WT_UPSTREAM" objdump "$comp")
  line=$(grep -m1 '^  module ' <<< "$out")
  start=$(sed 's/^[^|]*| *\(0x[0-9a-f]*\) - *\(0x[0-9a-f]*\) |.*/\1/' <<< "$line")
  stop=$(sed 's/^[^|]*| *\(0x[0-9a-f]*\) - *\(0x[0-9a-f]*\) |.*/\2/' <<< "$line")
  tail -c +"$((start + 1))" "$comp" | head -c "$((stop - start))" > "$dst"
}
wt_corpus_check
extract "$WT_CORPUS_DIR/cat.wasm" "$tmp/cat-core.wasm"
inputs=("tiny-module=$WT_CORPUS_DIR/pf-example.wasm")
[[ -f $WASI_ADAPTER_COMMAND ]] && inputs+=("adapter-module=$(wt_adapters | grep command)")
inputs+=("cat-core=$tmp/cat-core.wasm")
cat_debug=$(wt_cat_debug) || exit 1
if [[ -n $cat_debug ]]; then
  extract "$cat_debug" "$tmp/cat-debug-core.wasm"
  inputs+=("cat-debug-core=$tmp/cat-debug-core.wasm")
fi
inputs+=("cat-component=$WT_CORPUS_DIR/cat.wasm")
[[ -n $cat_debug ]] && inputs+=("cat-debug-component=$cat_debug")

# Median wall time (seconds) of $runs runs of a command.
median() {
  local -a ts=()
  local i s e
  for ((i = 0; i < runs; i++)); do
    s=$(date +%s.%N)
    "$@" > /dev/null 2>&1 || true
    e=$(date +%s.%N)
    ts+=("$(echo "$e - $s" | bc -l)")
  done
  printf '%s\n' "${ts[@]}" | sort -g | awk '{ a[NR] = $1 } END { printf "%.3f", a[int((NR + 1) / 2)] }'
}

printf 'input\tbytes\tsubcommand\tupstream_s\tours_s\n'
fail=0
for entry in "${inputs[@]}"; do
  name=${entry%%=*}
  f=${entry#*=}
  size=$(stat -c %s "$f")
  cmds=("objdump" "strip -o $tmp/out.wasm")
  cmds=("validate" "${cmds[@]}" "dump")
  for c in "${cmds[@]}"; do
    # shellcheck disable=SC2086
    up=$(median "$WT_UPSTREAM" $c "$f")
    # shellcheck disable=SC2086
    us=$(median "$ours" $c "$f")
    sub=${c%% *}
    printf '%s\t%s\t%s\t%s\t%s\n' "$name" "$size" "$sub" "$up" "$us"
    if [[ $check -eq 1 ]]; then
      base=$(awk -F'\t' -v n="$name" -v s="$sub" '$1 == n && $2 == s { print $3 }' \
        "$here/bench-baseline.tsv")
      if [[ -n $base ]] && (( $(echo "$us > 2 * $base + 0.1" | bc -l) )); then
        echo "REGRESSION: $name $sub: ${us}s > 2 x ${base}s + 0.1s" >&2
        fail=1
      fi
    fi
  done
done
exit $fail
