#!/usr/bin/env bash
# Check of the byte lexer of `wasm-wit parse` (Perf.WatReadB, proved equal to Sexp.read on
# ASCII text): for every component given (default: the components of tools/wac/tests/fixtures
# built by the wac tests, or COMP.wasm files under BENCH_WORK), `wasm-wit print` it, then parse
# the WAT and variants of it (a non-ASCII line comment, which sends the text to the List Char
# lexer; nested block comments; CRLF line ends; a trailing comment without a newline) with
#   wasm-perf parse-wat bytes|fast   (WatReadB.parseWatB, WatRead.parseWatF)
#   wasm-perf parse-wat spec         (Wit.Tool.parseWat; texts under 2 MB only: it recurses per
#                                      character)
# and require the same bytes from each, equal to the component's.
#
#   tools/wasm-perf/tests/wat-bytes.sh [COMP.wasm ...]
#
# Skips (exit 0) when wasm-wit or wasm-perf is not built.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
BIN=${SIL_BIN:-$root/.lake/build/bin}
for x in wasm-wit wasm-perf; do
  [[ -x $BIN/$x ]] || { echo "skip: $BIN/$x not built"; exit 0; }
done
comps=("$@")
if [[ ${#comps[@]} -eq 0 ]]; then
  if [[ -n ${BENCH_WORK:-} ]]; then
    mapfile -t comps < <(find "$BENCH_WORK" -name comp.wasm | sort)
  fi
fi
if [[ ${#comps[@]} -eq 0 ]]; then echo "skip: no components given (args or BENCH_WORK)"; exit 0; fi
work=$(mktemp -d /tmp/wasm-wat-bytes-XXXXXX)
pass=0 fail=0
for c in "${comps[@]}"; do
  n=$(basename "$(dirname "$c")")/$(basename "$c")
  if ! "$BIN/wasm-wit" print "$c" -o "$work/a.wat" > /dev/null 2>&1; then
    echo "  skip  $n (wasm-wit print refuses it)"; continue
  fi
  want=$(cksum < "$c" | cut -d' ' -f1)
  cp "$work/a.wat" "$work/v0.wat"
  { printf ';; caf\xc3\xa9 \xe2\x9c\x93\n'; cat "$work/a.wat"; } > "$work/v1.wat"
  { printf '(; outer (; inner ;) still ;)\n'; cat "$work/a.wat"; } > "$work/v2.wat"
  sed 's/$/\r/' "$work/a.wat" > "$work/v3.wat"
  { cat "$work/a.wat"; printf ';; trailing'; } > "$work/v4.wat"
  for v in v0 v1 v2 v3 v4; do
    ok=1
    modes="bytes fast"
    (( $(stat -c %s "$work/$v.wat") < 2000000 )) && modes="$modes spec"
    for m in $modes; do
      out=$("$BIN/wasm-perf" parse-wat "$m" "$work/$v.wat" 2>&1)
      "$BIN/wasm-wit" parse "$work/$v.wat" -o "$work/out.wasm" > /dev/null 2>&1 || ok=0
      got=$(cksum < "$work/out.wasm" | cut -d' ' -f1)
      [[ $got == "$want" ]] || ok=0
      echo "$out" | grep -q "^$(stat -c %s "$c") bytes" || ok=0
    done
    if (( ok )); then pass=$((pass + 1)); else fail=$((fail + 1)); echo "  FAIL  $n $v"; fi
  done
done
rm -rf "$work"
echo "wat-bytes: $pass passed, $fail failed"
(( fail == 0 ))
