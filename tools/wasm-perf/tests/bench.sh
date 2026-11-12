#!/usr/bin/env bash
# Benchmark of wasm-jco, wasm-wit and wasm-wac against the native tools (pinned wasm-tools and
# wac), on inputs from KB to multi-MB, and the regression check of their targets.
#
#   tools/wasm-perf/tests/bench.sh [--full] [--runs N] [--no-check]
#
# Corpus (built in a work directory with the pinned wasm-tools, nothing downloaded):
#   xfN    the byte transformer of tools/wac/tests (canonical ABI, world test:upper/upper)
#          with filler functions (gen-filler.awk): N = 2, 25, 100, 400 (and 1200 with --full)
#          filler functions of 1000 steps, about 9 KB of code each: 20 KB, 230 KB, 0.9 MB,
#          3.6 MB (10.8 MB) core modules; the components of `wasm-tools component new`
#   callsN a core module of N functions with 20 calls each to pseudo-random functions
#          (gen-calls.awk; N = 5000 and, with --full, 20000: 0.67 MB and 2.8 MB), embedded in an
#          empty world: the validator's function lookups (a list walk per call made silmaril's
#          validator quadratic: 31.6 s on calls20k before Perf.ValidateF)
#   rustR, rustD  a std-only Rust WASI 0.2 command (corpus/hello) built with the pinned Rust
#          1.99.1 (wasm32-wasip2), release (140 KB) and debug (3.7 MB, mostly DWARF); only when
#          the toolchain is installed in ~/.cache/silmaril-tools/rust-1.99.1 (installer:
#          examples/wasip3-rust/toolchain.sh on the wasip3-rust branch: rustup-init 1.29.2,
#          SHA-256 5be191e8c70a5007074254cb74d78dbfdd25cd5a61c27de7b8e5410122ec24f4)
# Cases (Lean tool | native tool):
#   jco-new       wasm-jco new CORE -o OUT            | wasm-tools component new CORE -o OUT
#   jco-validate  wasm-jco validate COMP              | wasm-tools validate COMP
#   wit-print     wasm-wit print COMP -o OUT.wat      | wasm-tools print COMP -o OUT.wat
#                 (lean prints core modules as bytes, wasm-tools as instructions)
#   wit-parse     wasm-wit parse OUT.wat -o OUT.wasm  | wasm-tools parse OUT.wat -o OUT.wasm
#   wac-compose   wasm-wac compose pipeline.wac --deps D --wasm -o OUT | wac compose
#                 (the xfN component as test:upper among the four other fixture packages)
#   wac-plug      wasm-wac plug run.wasm --plug xfN.wasm -o OUT | wac plug
# Each measurement is the minimum over N runs (default 3) of user+system CPU seconds, and the
# maximum resident set size (GNU time). Every lean output is also checked: jco-new output
# validates with wasm-tools; wit-parse gives back the input bytes; wac outputs validate.
#
# The check: targets.tsv (case, input, max CPU seconds, max RSS MB) for the Lean tool; a row
# over its target fails the run (exit 1) unless --no-check. Skips with exit 0 when a pinned
# tool or a Lean executable is absent.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$root/tools/wasm-jco/tests/pins.sh"
BIN=${SIL_BIN:-$root/.lake/build/bin}
RUST_ROOT=$SIL_TOOLS/rust-1.99.1

full=0 runs=3 check=1
while [[ $# -gt 0 ]]; do
  case $1 in
    --full) full=1 ;;
    --runs) runs=$2; shift ;;
    --no-check) check=0 ;;
    *) sed -n '2,4p' "$0" | sed 's/^# \{0,1\}//' >&2; exit 2 ;;
  esac
  shift
done

for x in wasm-jco wasm-wit wasm-wac; do
  if [[ ! -x $BIN/$x ]]; then echo "skip: $BIN/$x not built (lake build wasm-jco wasm-wit wasm-wac)"; exit 0; fi
done
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0
have_tool wac "$WAC" "$WAC_SHA256" || exit 0
[[ -x /usr/bin/time ]] || { echo "skip: GNU time (/usr/bin/time) is absent"; exit 0; }

work=${BENCH_WORK:-$(mktemp -d /tmp/wasm-perf-bench-XXXXXX)}
mkdir -p "$work"
results=$work/results.tsv
: > "$results"
echo "work: $work"
echo "machine: $(grep -m1 'model name' /proc/cpuinfo | sed 's/.*: //'), $(nproc) threads, $(free -g | awk '/Mem:/{print $2}') GB; load $(cut -d' ' -f1-3 /proc/loadavg)"

# `measure LABEL CMD…`: min CPU seconds over $runs runs and max RSS (MB); prints "secs rss rc".
measure() {
  local best="" rss=0 rc=0 i out
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
  local ns=- nr=- nrc=-
  if [[ ${#ncmd[@]} -gt 0 ]]; then read -r ns nr nrc <<< "$(measure "${ncmd[@]}")"; fi
  local ratio=-
  [[ $ns != - ]] && ratio=$(awk -v a="$ms" -v b="$ns" 'BEGIN{ if (b < 0.01) b = 0.01; printf "%.0f", a/b }')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$case" "$input" "$size" "$ms" "$mr" "$mrc" "$ns" "$nr" "$ratio" >> "$results"
  printf '  %-13s %-6s %9s B  lean %6ss %5s MB rc=%s   native %6ss %5s MB   x%s\n' "$case" "$input" "$size" "$ms" "$mr" "$mrc" "$ns" "$nr" "$ratio"
}

ok=0 bad=0
verify() { if "$@" > /dev/null 2>&1; then ok=$((ok + 1)); else bad=$((bad + 1)); echo "  FAIL  check: $*"; fi; }

# The corpus.
fx=$work/fixtures
bash "$root/tools/wac/tests/build-fixtures.sh" "$fx" > /dev/null 2>&1 || { echo "error: build-fixtures.sh failed"; exit 1; }
sizes=(2 25 100 400)
(( full )) && sizes+=(1200)
inputs=()
for n in "${sizes[@]}"; do
  d=$work/xf$n
  mkdir -p "$d/wit/deps/pipe"
  cp "$root/tools/wac/tests/fixtures/pipe.wit" "$d/wit/deps/pipe/"
  printf 'package test:upper;\n\nworld upper {\n  export test:pipe/xf;\n}\n' > "$d/wit/upper.wit"
  awk -v nfun="$n" -v steps=1000 -v step='local.get $c i32.const 97 i32.ge_u local.get $c i32.const 122 i32.le_u i32.and if local.get $c i32.const 32 i32.sub local.set $c end i32.const 1' \
    -f "$here/gen-filler.awk" "$root/tools/wac/tests/fixtures/xf.wat.in" > "$d/core.wat"
  "$WASM_TOOLS" component embed "$d/wit" "$d/core.wat" --world test:upper/upper -o "$d/core.wasm"
  "$WASM_TOOLS" component new "$d/core.wasm" -o "$d/comp.wasm"
  inputs+=("xf$n")
done
csizes=(5000)
(( full )) && csizes+=(20000)
for n in "${csizes[@]}"; do
  d=$work/calls$((n / 1000))k
  mkdir -p "$d/wit"
  printf 'package test:calls;\n\nworld calls {}\n' > "$d/wit/calls.wit"
  awk -v nfun="$n" -v ncalls=20 -f "$here/gen-calls.awk" > "$d/core.wat"
  "$WASM_TOOLS" component embed "$d/wit" "$d/core.wat" --world test:calls/calls -o "$d/core.wasm"
  "$WASM_TOOLS" component new "$d/core.wasm" -o "$d/comp.wasm"
  inputs+=("calls$((n / 1000))k")
done
if [[ -x $RUST_ROOT/cargo/bin/cargo && -d $RUST_ROOT/rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/wasm32-wasip2 ]]; then
  rs=$work/rust
  mkdir -p "$rs"
  cp -r "$here/corpus/hello/." "$rs/"
  for prof in release debug; do
    flag=(); [[ $prof == release ]] && flag=(--release)
    if (cd "$rs" && RUSTUP_HOME=$RUST_ROOT/rustup CARGO_HOME=$RUST_ROOT/cargo PATH=$RUST_ROOT/cargo/bin:$PATH \
          cargo +1.99.1 build --offline --target wasm32-wasip2 "${flag[@]}" > "$work/cargo-$prof.log" 2>&1); then
      t=rust${prof:0:1}; t=${t/rustr/rustR}; t=${t/rustd/rustD}
      mkdir -p "$work/$t"
      cp "$rs/target/wasm32-wasip2/$prof/hello.wasm" "$work/$t/comp.wasm"
      inputs+=("$t")
    else
      echo "note: the Rust example did not build ($prof; $work/cargo-$prof.log)"
    fi
  done
else
  echo "note: Rust 1.99.1 with wasm32-wasip2 not installed at $RUST_ROOT; the rust inputs are skipped"
fi

echo "cases (min CPU s of $runs runs, max RSS):"
for i in "${inputs[@]}"; do
  d=$work/$i
  csize=$(stat -c %s "$d/comp.wasm")
  if [[ -f $d/core.wasm ]]; then
    size=$(stat -c %s "$d/core.wasm")
    row jco-new "$i" "$size" "$BIN/wasm-jco" new "$d/core.wasm" -o "$d/mj.wasm" -- "$WASM_TOOLS" component new "$d/core.wasm" -o "$d/wt.wasm"
    verify "$WASM_TOOLS" validate "$d/mj.wasm"
  fi
  row jco-validate "$i" "$csize" "$BIN/wasm-jco" validate "$d/comp.wasm" -- "$WASM_TOOLS" validate "$d/comp.wasm"
  row wit-print "$i" "$csize" "$BIN/wasm-wit" print "$d/comp.wasm" -o "$d/m.wat" -- "$WASM_TOOLS" print "$d/comp.wasm" -o "$d/w.wat"
  wsize=$(stat -c %s "$d/m.wat")
  row wit-parse "$i" "$wsize" "$BIN/wasm-wit" parse "$d/m.wat" -o "$d/m.wasm" -- "$WASM_TOOLS" parse "$d/m.wat" -o "$d/mw.wasm"
  verify cmp "$d/m.wasm" "$d/comp.wasm"
  if [[ $i == xf* ]]; then
    deps=$d/deps
    rm -rf "$deps"; cp -r "$fx/deps" "$deps"; cp "$d/comp.wasm" "$deps/test/upper.wasm"
    pw=$root/tools/wac/tests/fixtures/pipeline.wac
    row wac-compose "$i" "$csize" "$BIN/wasm-wac" compose "$pw" --deps "$deps" --wasm -o "$d/mc.wasm" -- "$WAC" compose "$pw" --deps-dir "$deps" -o "$d/wc.wasm"
    verify "$WASM_TOOLS" validate "$d/mc.wasm"
    row wac-plug "$i" "$csize" "$BIN/wasm-wac" plug "$deps/test/run.wasm" --plug "$deps/test/upper.wasm" -o "$d/mp.wasm" -- "$WAC" plug "$deps/test/run.wasm" --plug "$deps/test/upper.wasm" -o "$d/wp.wasm"
    verify "$WASM_TOOLS" validate "$d/mp.wasm"
  fi
done

echo "output checks: $ok passed, $bad failed"
fail=$bad
if (( check )); then
  while IFS=$'\t' read -r case input maxs maxmb; do
    [[ -z $case || $case == \#* ]] && continue
    line=$(awk -F'\t' -v c="$case" -v i="$input" '$1==c && $2==i' "$results")
    [[ -z $line ]] && continue
    IFS=$'\t' read -r _ _ _ ms mr mrc _ _ _ <<< "$line"
    if [[ $mrc != 0 ]] || awk -v a="$ms" -v b="$maxs" 'BEGIN{exit !(a>b)}' || (( mr > maxmb )); then
      echo "  OVER  $case $input: ${ms}s ${mr} MB rc=$mrc (target ${maxs}s ${maxmb} MB)"; fail=$((fail + 1))
    fi
  done < "$here/targets.tsv"
  echo "targets: $([[ $fail == 0 ]] && echo met || echo "$fail over or failed")"
fi
exit $(( fail > 0 ? 1 : 0 ))
