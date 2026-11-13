#!/usr/bin/env bash
# `wasm-tools wit-smith` (genapi track) against pinned wasm-tools 1.262.0.
#
#   tools/wasm-tools/tests/gen/wit-smith.sh [N] [RANDOM_SEED]     (default 100 seeds, seed 1)
#
# For each of N seeds (random bytes of random length, reproducible from RANDOM_SEED) and each
# flag set (none; --async; --futures --streams; --error-context; --fixed-length-lists):
#  1. our `wit-smith` output -> upstream `validate` (with the component-model features the
#     flags need) must accept;                                                   [valid]
#  2. upstream `component wit` must decode it as a WIT package;                   [wit]
#  3. our `wit-smith -t` -> upstream `parse` -> the same bytes as our binary;     [text]
#  4. upstream `wit-smith` on the same seed -> our `component wit` decodes it     [ours-read]
#     (an informal comparison: the generators differ by design).
# CLI: `-h`/`--help` identical; a missing input file: same status and message.  [cli]
# Failing seeds are kept in $GT_FUZZ_KEEP (default /tmp/wit-smith-failures).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/pins.sh"
gt_require_upstream
gt_ours
N=${1:-100}
RANDOM=${2:-1}
keep=${GT_FUZZ_KEEP:-/tmp/wit-smith-failures}
mkdir -p "$keep"
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
cd "$work"
U=$GT_UPSTREAM; O=$GT_OURS
declare -A ok bad
for k in valid wit text ours-read cli; do ok[$k]=0; bad[$k]=0; done
tally() { if [[ $2 == 0 ]]; then ok[$1]=$((ok[$1]+1)); else bad[$1]=$((bad[$1]+1)); cp s "$keep/$1-$3.seed" 2>/dev/null; fi; }
# flags : upstream validate features
sets=("|" "--async|cm-async" "--futures --streams|cm-async" "--error-context|cm-async,cm-error-context" "--fixed-length-lists|cm-fixed-length-lists")
# cli
for a in -h --help; do
  "$O" wit-smith $a > o.txt 2>&1; ro=$?; "$U" wit-smith $a > u.txt 2>&1; ru=$?
  cmp -s o.txt u.txt && [[ $ro == "$ru" ]]; tally cli $? "help$a"
done
"$O" wit-smith /nonexistent/seed > o.txt 2>&1; ro=$?; "$U" wit-smith /nonexistent/seed > u.txt 2>&1; ru=$?
cmp -s o.txt u.txt && [[ $ro == "$ru" ]]; tally cli $? missing
for i in $(seq 1 "$N"); do
  head -c $((RANDOM % 2000)) /dev/urandom > s
  for st in "${sets[@]}"; do
    fl=${st%%|*}; feat=${st#*|}
    tag="$i-${fl// /}"
    if ! "$O" wit-smith $fl s -o o.wasm 2>err; then tally valid 1 "$tag"; continue; fi
    if [[ -n $feat ]]; then "$U" validate --features "$feat" o.wasm 2>err; else "$U" validate o.wasm 2>err; fi
    tally valid $? "$tag"
    "$U" component wit o.wasm > /dev/null 2>err; tally wit $? "$tag"
    if "$O" wit-smith $fl -t s > o.wat 2>err && "$U" parse o.wat -o p.wasm 2>err; then
      cmp -s o.wasm p.wasm; tally text $? "$tag"
    else tally text 1 "$tag"; fi
    if "$U" wit-smith $fl s -o u.wasm 2>/dev/null; then
      "$O" component wit u.wasm > /dev/null 2>err; tally ours-read $? "$tag"
    fi
  done
done
fail=0
for k in valid wit text ours-read cli; do
  printf '%-10s %4d ok %4d failed\n' "$k" "${ok[$k]}" "${bad[$k]}"
done
(( bad[valid] + bad[wit] + bad[cli] == 0 )) || fail=1
exit $fail
