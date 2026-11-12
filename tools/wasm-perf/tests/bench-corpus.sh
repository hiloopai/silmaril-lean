#!/usr/bin/env bash
# Benchmark of wasm-jco and wasm-wac on the real-producer corpora, against the native tools,
# and the regression check of its targets (targets-corpus.tsv).
#
#   tools/wasm-perf/tests/bench-corpus.sh [--runs N] [--no-check] [--only jco|wac]
#
# jco: the Rust corpus of tools/wasm-jco/tests/corpus (core modules written by the pinned Rust
#   1.99.1 + wit-bindgen 0.62.0: std crates with several component-type sections, a no_std
#   crate, resources, async exports with streams, and the 3.4 MB debug build of `kitchen`),
#   built by corpus/build.sh (or SIL_CORPUS, a directory of NAME.core.wasm). Per module:
#     jco-new       wasm-jco new NAME.core.wasm        | wasm-tools component new
#     jco-validate  wasm-jco validate (wasm-tools' component) | wasm-tools validate --features all
#   each the minimum CPU time of N runs (default 3) and the maximum RSS; wasm-jco's output must
#   validate with wasm-tools.
# wac: the wac corpus suites, run as they are with every wasm-wac and wac invocation timed (a
#   wrapper in SIL_WAC / WAC records GNU time's user+system CPU and RSS):
#     tools/wac/tests/corpus.sh  the documents of wac v0.12.0's own tests and examples
#     tools/wac/tests/rust.sh    a Rust wasm32-wasip2 program, release and debug, composed and plugged
#   reported per suite and tool: invocations, total and maximum CPU, maximum RSS; the suite must
#   pass (exit 0).
# The check: each line of targets-corpus.tsv (case, input or `*`, max CPU s, max RSS MB) bounds
# the Lean tool; `wac-corpus`/`wac-rust` rows bound the maximum per invocation, `…-total` rows
# the total CPU (RSS column unused). Skips (exit 0) when a pinned tool or an executable is absent.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$root/tools/wasm-jco/tests/pins.sh"
BIN=${SIL_BIN:-$root/.lake/build/bin}

runs=3 check=1 only=
while [[ $# -gt 0 ]]; do
  case $1 in
    --runs) runs=$2; shift ;;
    --no-check) check=0 ;;
    --only) only=$2; shift ;;
    *) sed -n '5,6p' "$0" | sed 's/^# \{0,1\}//' >&2; exit 2 ;;
  esac
  shift
done

for x in wasm-jco wasm-wac; do
  if [[ ! -x $BIN/$x ]]; then echo "skip: $BIN/$x not built (lake build wasm-jco wasm-wac)"; exit 0; fi
done
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0
have_tool wac "$WAC" "$WAC_SHA256" || exit 0
[[ -x /usr/bin/time ]] || { echo "skip: GNU time (/usr/bin/time) is absent"; exit 0; }

work=${BENCH_WORK:-$(mktemp -d /tmp/wasm-perf-corpus-XXXXXX)}
mkdir -p "$work"
results=$work/results.tsv
: > "$results"
echo "work: $work"
echo "machine: $(grep -m1 'model name' /proc/cpuinfo | sed 's/.*: //'), $(nproc) threads, $(free -g | awk '/Mem:/{print $2}') GB; load $(cut -d' ' -f1-3 /proc/loadavg)"

# `measure CMD…`: min CPU seconds over $runs runs and max RSS (MB); prints "secs rss rc".
measure() {
  local best="" rss=0 rc=0 i
  for ((i = 0; i < runs; i++)); do
    /usr/bin/time -o "$work/time.txt" -f '%U %S %M' "$@" > /dev/null 2> "$work/stderr.txt"
    rc=$?
    read -r u s m < <(tail -1 "$work/time.txt")
    local t; t=$(awk -v u="$u" -v s="$s" 'BEGIN{printf "%.2f", u+s}')
    if [[ -z $best ]] || awk -v a="$t" -v b="$best" 'BEGIN{exit !(a<b)}'; then best=$t; fi
    (( m > rss )) && rss=$m
  done
  echo "$best $((rss / 1024)) $rc"
}

# `row CASE INPUT SIZE MORIA-CMD… -- NATIVE-CMD…`
row() {
  local case=$1 input=$2 size=$3; shift 3
  local mcmd=() ncmd=()
  while [[ $1 != -- ]]; do mcmd+=("$1"); shift; done; shift
  ncmd=("$@")
  read -r ms mr mrc <<< "$(measure "${mcmd[@]}")"
  read -r ns nr nrc <<< "$(measure "${ncmd[@]}")"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$case" "$input" "$size" "$ms" "$mr" "$mrc" "$ns" "$nr" >> "$results"
  printf '  %-13s %-14s %9s B  lean %6ss %5s MB rc=%s   native %6ss %5s MB\n' "$case" "$input" "$size" "$ms" "$mr" "$mrc" "$ns" "$nr"
}

ok=0 bad=0
verify() { if "$@" > /dev/null 2>&1; then ok=$((ok + 1)); else bad=$((bad + 1)); echo "  FAIL  check: $*"; fi; }

# --- jco: the Rust corpus ------------------------------------------------------------------------
if [[ -z $only || $only == jco ]]; then
  corpus=${SIL_CORPUS:-}
  if [[ -z $corpus ]]; then
    corpus=$work/jco-core
    "$root/tools/wasm-jco/tests/corpus/build.sh" "$corpus" > "$work/jco-build.log" 2>&1 ||
      { echo "error: the jco corpus did not build ($work/jco-build.log)"; exit 1; }
  fi
  shopt -s nullglob
  mods=("$corpus"/*.core.wasm)
  if [[ ${#mods[@]} -eq 0 ]]; then
    echo "note: no jco corpus ($(tail -1 "$work/jco-build.log" 2>/dev/null)); jco cases skipped"
  else
    echo "jco corpus (min CPU s of $runs runs, max RSS):"
    for m in "${mods[@]}"; do
      n=$(basename "$m" .core.wasm)
      d=$work/jco/$n
      mkdir -p "$d"
      size=$(stat -c %s "$m")
      row jco-new "$n" "$size" "$BIN/wasm-jco" new "$m" -o "$d/mj.wasm" -- "$WASM_TOOLS" component new "$m" -o "$d/wt.wasm"
      verify "$WASM_TOOLS" validate --features all "$d/mj.wasm"
      csize=$(stat -c %s "$d/wt.wasm")
      row jco-validate "$n" "$csize" "$BIN/wasm-jco" validate "$d/wt.wasm" -- "$WASM_TOOLS" validate --features all "$d/wt.wasm"
    done
  fi
fi

# --- wac: the corpus suites, every invocation timed ----------------------------------------------
# `wrapper NAME REAL LOG`: an executable that runs REAL under GNU time, appending "cpu rss" to LOG.
wrapper() {
  cat > "$work/$1" <<EOF
#!/usr/bin/env bash
/usr/bin/time -a -o '$3' -f '%U %S %M' '$2' "\$@"
EOF
  chmod +x "$work/$1"
}
# `suite NAME SCRIPT`: run SCRIPT with timed wasm-wac and wac; record the summary rows.
suite() {
  local name=$1 script=$2 mlog=$work/$1.lean.times wlog=$work/$1.wac.times
  : > "$mlog"; : > "$wlog"
  wrapper "$name-wasm-wac" "$BIN/wasm-wac" "$mlog"
  wrapper "$name-wac" "$WAC" "$wlog"
  SIL_WAC=$work/$name-wasm-wac WAC=$work/$name-wac bash "$script" > "$work/$name.log" 2>&1
  local rc=$?
  if grep -q '^SKIP' "$work/$name.log"; then echo "  $name: $(grep -m1 '^SKIP' "$work/$name.log")"; return; fi
  if (( rc == 0 )); then ok=$((ok + 1)); else bad=$((bad + 1)); echo "  FAIL  $script exited $rc ($work/$name.log)"; fi
  # summary: count, total CPU, max CPU, max RSS (MB)
  # (GNU time also writes "Command exited with non-zero status N" lines: skipped)
  summ() { awk '/^[0-9.]+ [0-9.]+ [0-9]+$/{c++; t=$1+$2; s+=t; if (t>m) m=t; if ($3+0>r) r=$3+0} END{printf "%d %.2f %.2f %d", c, s, m, r/1024}' "$1"; }
  read -r mc ms mm mr <<< "$(summ "$mlog")"
  read -r wc ws wm wr <<< "$(summ "$wlog")"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "wac-$name" "*" "$mc" "$mm" "$mr" "$rc" "$wm" "$wr" >> "$results"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "wac-$name-total" "*" "$mc" "$ms" 0 "$rc" "$ws" 0 >> "$results"
  printf '  %-12s wasm-wac: %4d runs, total %6ss, max %5ss, max %4s MB   wac: %4d runs, total %6ss, max %5ss, max %4s MB  (suite: %s)\n' \
    "$name" "$mc" "$ms" "$mm" "$mr" "$wc" "$ws" "$wm" "$wr" "$(tail -1 "$work/$name.log")"
}
if [[ -z $only || $only == wac ]]; then
  echo "wac corpus suites (every invocation timed once):"
  suite corpus "$root/tools/wac/tests/corpus.sh"
  suite rust "$root/tools/wac/tests/rust.sh"
fi

echo "output checks: $ok passed, $bad failed"
fail=$bad
if (( check )); then
  while IFS=$'\t' read -r case input maxs maxmb; do
    [[ -z $case || $case == \#* ]] && continue
    while IFS=$'\t' read -r _ inp _ ms mr mrc _ _; do
      [[ -z $inp ]] && continue
      if [[ $mrc != 0 ]] || awk -v a="$ms" -v b="$maxs" 'BEGIN{exit !(a>b)}' || (( mr > maxmb )); then
        echo "  OVER  $case $inp: ${ms}s ${mr} MB rc=$mrc (target ${maxs}s ${maxmb} MB)"; fail=$((fail + 1))
      fi
    done < <(awk -F'\t' -v c="$case" -v i="$input" '$1==c && (i=="*" || $2==i)' "$results")
  done < "$here/targets-corpus.tsv"
  echo "targets: $([[ $fail == 0 ]] && echo met || echo "$fail over or failed")"
fi
exit $(( fail > 0 ? 1 : 0 ))
