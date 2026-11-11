#!/usr/bin/env bash
# Performance of `wasm-tools print` and `parse` (cli track) against wasm-tools 1.262.0.
#
#   tools/wasm-tools/tests/pp-bench.sh [--bin PATH] [--runs N] [--large] [--check]
#
# Inputs, KB to MB: the fetched WASI adapter wasi_snapshot_preview1.command.wasm (51 KB,
# pins.sh; skipped when absent) and, from the 1.262.0 source archive,
# crates/wasmparser/benches/{bz2,pulldown-cmark}.wasm (188 KB, 2 MB); with --large also
# spidermonkey.wasm (5.4 MB). For each: `print X.wasm` and `parse X.wat` (X.wat: upstream's
# printed text), median wall time of N runs (default 3), and whether the outputs are
# byte-identical with upstream's.
#
# --check: a regression test; fails when an output differs or one of our times exceeds 2x its
# entry in pp-bench-baseline.tsv plus 0.5 s. Skips (status 0) without the pinned wasm-tools,
# the source archive or our binary.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
source "$here/pins.sh"
bin="$repo/.lake/build/bin/wasm-tools"; runs=3; large=0; check=0
while [[ $# -gt 0 ]]; do
  case $1 in
    --bin) bin=$2; shift 2;; --runs) runs=$2; shift 2;; --large) large=1; shift;;
    --check) check=1; shift;;
    *) echo "usage: $0 [--bin PATH] [--runs N] [--large] [--check]"; exit 2;;
  esac
done
wt_require_upstream; wt_require_src
wt_require_ours "$bin" wasm-tools
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
B="$WT_SRC_DIR/crates/wasmparser/benches"
inputs=()
[[ -f $WASI_ADAPTER_COMMAND ]] && inputs+=("adapter:$(wt_adapters | grep command)")
inputs+=("bz2:$B/bz2.wasm" "pulldown-cmark:$B/pulldown-cmark.wasm")
[[ $large == 1 ]] && inputs+=("spidermonkey:$B/spidermonkey.wasm")

median() { sort -n | awk '{a[NR]=$1} END {print a[int((NR+1)/2)]}'; }
timeit() { # cmd... -> seconds (median of $runs)
  for _ in $(seq "$runs"); do
    local s e; s=$(date +%s.%N); "$@" >/dev/null 2>&1; e=$(date +%s.%N)
    echo "$e - $s" | bc
  done | median
}
fail=0
printf '%-16s %-6s %9s %9s %s\n' input cmd ours_s up_s identical
for entry in "${inputs[@]}"; do
  name=${entry%%:*}; f=${entry#*:}
  [[ -f $f ]] || { echo "missing $f"; continue; }
  "$WT_UPSTREAM" print "$f" -o "$tmp/$name.u.wat"
  "$bin" print "$f" -o "$tmp/$name.o.wat"
  cmp -s "$tmp/$name.u.wat" "$tmp/$name.o.wat" && pid=yes || pid=no
  "$WT_UPSTREAM" parse "$tmp/$name.u.wat" -o "$tmp/$name.u.wasm"
  "$bin" parse "$tmp/$name.u.wat" -o "$tmp/$name.o.wasm"
  cmp -s "$tmp/$name.u.wasm" "$tmp/$name.o.wasm" && qid=yes || qid=no
  for cmd in print parse; do
    if [[ $cmd == print ]]; then a=("$f"); id=$pid; else a=("$tmp/$name.u.wat" -o /dev/null); id=$qid; fi
    o=$(timeit "$bin" $cmd "${a[@]}"); u=$(timeit "$WT_UPSTREAM" $cmd "${a[@]}")
    printf '%-16s %-6s %9.2f %9.2f %s\n' "$name" "$cmd" "$o" "$u" "$id"
    if [[ $check == 1 ]]; then
      [[ $id == yes ]] || { echo "FAIL: $name $cmd output differs"; fail=1; }
      base=$(awk -v n="$name" -v c="$cmd" '$1==n && $2==c {print $3}' "$here/pp-bench-baseline.tsv")
      if [[ -n $base ]] && (( $(echo "$o > 2 * $base + 0.5" | bc) )); then
        echo "FAIL: $name $cmd took $o s (baseline $base s)"; fail=1
      fi
    fi
  done
done
[[ $check == 1 && $fail == 0 ]] && echo "pp-bench: check passed"
exit $fail
