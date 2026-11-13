#!/usr/bin/env bash
# Differential tests of the Lean `wasm-tools component …` against the pinned upstream
# wasm-tools 1.262.0 (pins.sh). Skips (exit 0) when the pinned binary, the Lean binary or the
# upstream source tree (for the corpora) is absent.
#
#   tools/wasm-tools/tests/component/run.sh [--keep] [SECTION...]
#
# Sections (default: all):
#   cli         argument handling: for each invocation, stdout (bytes), the first stderr line
#               and the exit status must agree
#   interfaces  crates/wit-component/tests/interfaces: `component wit X` (text) and
#               `component wit --wasm X` (bytes) must agree
#   components  crates/wit-component/tests/components: `component embed` (bytes) must agree;
#               `component new` must succeed or fail as upstream's does; when both succeed, ours
#               must pass upstream's validator and have the same `component wit` world; our
#               `component wit` of upstream's component must equal upstream's
#   targets     crates/wit-component/tests/targets: the exit status of `component targets`
#               and `component unbundle --threshold 0` of upstream's component (bytes of the
#               output and of every module)
#   unbundle    tests/cli/unbundle-*.wat: bytes of `component unbundle` and of each module
#
# Prints one line per failure and a summary per section; exit status 1 when a `cli` or
# `unbundle` case fails (the corpora sections report parity, see docs/projects/wasm-components.md).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../../.." && pwd)
source "$here/pins.sh"
wtc_require_upstream
OURS=${WASM_TOOLS_LEAN:-$repo/.lake/build/bin/wasm-tools}
if [[ ! -x $OURS ]]; then echo "SKIP: $OURS not built (lake build wasm-tools)"; exit 0; fi
SRC="$SIL_TOOLS/src/wasm-tools-1.262.0-cli/wasm-tools-1.262.0"
WT=$WT_UPSTREAM

keep=0
if [[ ${1:-} == --keep ]]; then keep=1; shift; fi
sections=("$@")
[[ ${#sections[@]} -eq 0 ]] && sections=(cli interfaces components targets unbundle)
tmp=$(mktemp -d /tmp/wasm-tools-comp-component-XXXXXX)
[[ $keep == 1 ]] || trap 'rm -rf "$tmp"' EXIT

hard_fail=0
declare -A PASS FAIL BOTH
note() { echo "  $1: $2"; }

# --- cli ---------------------------------------------------------------------------------
cli_case() {
  local i=$1; shift
  local d="$tmp/cli/$i"; mkdir -p "$d/u" "$d/o"
  (cd "$tmp/cli/data" && "$WT" "$@" >"$d/u/out" 2>"$d/u/err" </dev/null); local ue=$?
  (cd "$tmp/cli/data" && "$OURS" "$@" >"$d/o/out" 2>"$d/o/err" </dev/null); local oe=$?
  local uh oh; uh=$(head -1 "$d/u/err"); oh=$(head -1 "$d/o/err")
  if [[ $ue == "$oe" ]] && cmp -s "$d/u/out" "$d/o/out" && [[ $uh == "$oh" ]]; then
    PASS[cli]=$(( ${PASS[cli]:-0} + 1 ))
  else
    FAIL[cli]=$(( ${FAIL[cli]:-0} + 1 )); hard_fail=1
    note cli "[$*] exit $ue/$oe, stderr '$uh' / '$oh'$(cmp -s "$d/u/out" "$d/o/out" || echo ', stdout differs')"
  fi
}

section_cli() {
  mkdir -p "$tmp/cli/data"; local D="$tmp/cli/data"
  printf 'package a:b;\n\ninterface i {\n  record r { x: u32, y: string }\n  f: func(a: r) -> list<u8>;\n}\n\nworld w {\n  import i;\n  export g: func(x: u32) -> u32;\n}\n' > "$D/w.wit"
  printf 'package a:b;\nworld x { export f: func(); }\nworld y { export g: func(); }\n' > "$D/multi.wit"
  printf 'package a:b;\ninterface i { f: func(); }\n' > "$D/none.wit"
  "$WT" component embed "$D/w.wit" --dummy -o "$D/d.wasm"
  "$WT" strip "$D/d.wasm" -o "$D/core.wasm"
  "$WT" component new "$D/d.wasm" -o "$D/c.wasm"
  local n=0
  while IFS= read -r line; do
    [[ -z $line || $line == \#* ]] && continue
    n=$((n + 1)); eval "cli_case $n $line"
  done <<'EOF'
component
component -h
component --help
component help
component help new
component help embed
component foo
component new -h
component new --help
component embed -h
component embed --help
component wit -h
component wit --help
component targets -h
component targets --help
component unbundle -h
component unbundle --help
component link -h
component semver-check --help
component new --bogus
component new a b
component new --validate true x
component new --validate=maybe
component new -o
component new -o a -o b
component new -t -t
component new nonexist.wasm
component new c.wasm -o out.wasm
component embed
component embed --dummy --dummy-names legacy x.wit
component embed --async-callback x.wit
component embed --only-custom -t w.wit
component embed w.wit --encoding latin1 core.wasm
component embed multi.wit core.wasm -o out.wasm
component embed none.wit core.wasm -o out.wasm
component embed multi.wit -w z core.wasm -o out.wasm
component embed multi.wit -w a:b/z core.wasm -o out.wasm
component embed multi.wit -w c:d/x core.wasm -o out.wasm
component embed nofile.wit core.wasm -o out.wasm
component embed w.wit core.wasm -o /dev/stdout
component embed w.wit --world w core.wasm -o /dev/stdout
component embed w.wit -ww core.wasm -o /dev/stdout
component embed w.wit --world=w core.wasm --encoding utf16 -o /dev/stdout
component embed --only-custom w.wit -o /dev/stdout
component embed multi.wit -w a:b/x core.wasm -o /dev/stdout
component wit
component wit --wasm --wat
component wit w.wit
component wit c.wasm
component wit core.wasm
component wit --wasm w.wit -o /dev/stdout
component wit -w w.wit -o /dev/stdout
component wit w.wit -o /dev/stdout
component wit nofile.wit
component wit --merge-world-imports-based-on-semver w w.wit
component wit --merge-world-imports-based-on-semver nope w.wit
component wit --merge-world-imports-based-on-semver w c.wasm
component targets
component targets w.wit c.wasm
component targets multi.wit -w y c.wasm
component targets w.wit nonexist.wasm
component unbundle
component unbundle --module-dir
component unbundle --threshold x --module-dir m c.wasm
EOF
}

# --- interfaces --------------------------------------------------------------------------
section_interfaces() {
  local I="$SRC/crates/wit-component/tests/interfaces"
  [[ -d $I ]] || { echo "SKIP interfaces: $I absent"; return; }
  local d="$tmp/if"; mkdir -p "$d"
  for x in "$I"/*.wit "$I"/*/; do
    x=${x%/}; local b; b=$(basename "$x")
    [[ -d $x && ! -e $x/$(ls "$x" | head -1) ]] && continue
    "$WT" component wit "$x" >"$d/u.wit" 2>/dev/null; local ue=$?
    "$OURS" component wit "$x" >"$d/o.wit" 2>/dev/null; local oe=$?
    if [[ $ue == 0 && $oe == 0 ]] && cmp -s "$d/u.wit" "$d/o.wit"; then PASS[if-text]=$(( ${PASS[if-text]:-0} + 1 ))
    elif [[ $ue != 0 && $oe != 0 ]]; then BOTH[if-text]=$(( ${BOTH[if-text]:-0} + 1 ))
    else FAIL[if-text]=$(( ${FAIL[if-text]:-0} + 1 )); note if-text "$b (exit $ue/$oe)"; fi
    rm -f "$d/u.wasm" "$d/o.wasm"
    "$WT" component wit --wasm "$x" -o "$d/u.wasm" 2>/dev/null; ue=$?
    "$OURS" component wit --wasm "$x" -o "$d/o.wasm" 2>/dev/null; oe=$?
    if [[ $ue == 0 && $oe == 0 ]] && cmp -s "$d/u.wasm" "$d/o.wasm"; then PASS[if-wasm]=$(( ${PASS[if-wasm]:-0} + 1 ))
    elif [[ $ue != 0 && $oe != 0 ]]; then BOTH[if-wasm]=$(( ${BOTH[if-wasm]:-0} + 1 ))
    else FAIL[if-wasm]=$(( ${FAIL[if-wasm]:-0} + 1 )); note if-wasm "$b (exit $ue/$oe)"; fi
  done
}

# --- components --------------------------------------------------------------------------
section_components() {
  local C="$SRC/crates/wit-component/tests/components"
  [[ -d $C ]] || { echo "SKIP components: $C absent"; return; }
  for x in "$C"/*/; do
    x=${x%/}; local b; b=$(basename "$x")
    [[ -f $x/module.wat && -f $x/module.wit ]] || continue
    local d="$tmp/comp/$b"; mkdir -p "$d"
    "$WT" parse "$x/module.wat" -o "$d/m.wasm" 2>/dev/null || continue
    "$WT" component embed "$x" -w module "$d/m.wasm" -o "$d/eu.wasm" 2>"$d/eu.err"; local ue=$?
    "$OURS" component embed "$x" -w module "$d/m.wasm" -o "$d/eo.wasm" 2>"$d/eo.err"; local oe=$?
    if [[ $ue == 0 && $oe == 0 ]] && cmp -s "$d/eu.wasm" "$d/eo.wasm"; then PASS[embed]=$(( ${PASS[embed]:-0} + 1 ))
    elif [[ $ue != 0 && $oe != 0 ]]; then BOTH[embed]=$(( ${BOTH[embed]:-0} + 1 ))
    else FAIL[embed]=$(( ${FAIL[embed]:-0} + 1 )); note embed "$b (exit $ue/$oe) $(head -c 160 "$d/eo.err")"; fi
    [[ $ue == 0 ]] || continue
    # adapters: adapt-NAME.wat with its world adapt-NAME embedded, as components.rs does
    local ad=()
    for a in "$x"/adapt-*.wat; do
      [[ -f $a ]] || continue
      local an; an=$(basename "$a" .wat); an=${an#adapt-}
      "$WT" parse "$a" -o "$d/adapt-$an.raw.wasm" 2>/dev/null || continue
      if [[ -f $x/adapt-$an.wit ]]; then
        "$WT" component embed "$x" -w "adapt-$an" "$d/adapt-$an.raw.wasm" -o "$d/adapt-$an.wasm" 2>/dev/null || continue
      else cp "$d/adapt-$an.raw.wasm" "$d/adapt-$an.wasm"; fi
      ad+=(--adapt "$an=$d/adapt-$an.wasm")
    done
    "$WT" component new "$d/eu.wasm" "${ad[@]}" -o "$d/nu.wasm" 2>"$d/nu.err"; ue=$?
    "$OURS" component new "$d/eu.wasm" "${ad[@]}" -o "$d/no.wasm" 2>"$d/no.err"; oe=$?
    if [[ $ue != 0 && $oe != 0 ]]; then BOTH[new]=$(( ${BOTH[new]:-0} + 1 ))
    elif [[ $ue != "$oe" ]]; then FAIL[new]=$(( ${FAIL[new]:-0} + 1 )); note new "$b (exit $ue/$oe) $(head -c 200 "$d/no.err" | tr '\n' ' ')"
    else
      if ! "$WT" validate --features all "$d/no.wasm" 2>"$d/v.err"; then
        FAIL[new]=$(( ${FAIL[new]:-0} + 1 )); note new "$b: invalid output: $(head -c 160 "$d/v.err")"
      elif "$WT" component wit "$d/nu.wasm" >"$d/nu.wit" 2>/dev/null && \
           "$WT" component wit "$d/no.wasm" >"$d/no.wit" 2>/dev/null && cmp -s "$d/nu.wit" "$d/no.wit"; then
        PASS[new]=$(( ${PASS[new]:-0} + 1 ))
      else FAIL[new]=$(( ${FAIL[new]:-0} + 1 )); note new "$b: worlds differ"; fi
    fi
    if [[ $ue == 0 ]]; then
      # unbundle every module of upstream's component (threshold 0)
      "$WT" component unbundle --module-dir "$d/uu" --threshold 0 "$d/nu.wasm" -o "$d/uu.wasm" 2>/dev/null; local xe=$?
      "$OURS" component unbundle --module-dir "$d/uo" --threshold 0 "$d/nu.wasm" -o "$d/uo.wasm" 2>"$d/uo.err"; local ye=$?
      if [[ $xe == "$ye" ]] && { [[ $xe != 0 ]] || { cmp -s "$d/uu.wasm" "$d/uo.wasm" && diff -rq "$d/uu" "$d/uo" >/dev/null; }; }; then
        PASS[unbundle-corpus]=$(( ${PASS[unbundle-corpus]:-0} + 1 ))
      else FAIL[unbundle-corpus]=$(( ${FAIL[unbundle-corpus]:-0} + 1 )); note unbundle-corpus "$b (exit $xe/$ye) $(head -c 160 "$d/uo.err" | tr '\n' ' ')"; fi
      "$WT" component wit "$d/nu.wasm" >"$d/wu.wit" 2>/dev/null; ue=$?
      "$OURS" component wit "$d/nu.wasm" >"$d/wo.wit" 2>"$d/wo.err"; oe=$?
      if [[ $ue == "$oe" ]] && cmp -s "$d/wu.wit" "$d/wo.wit"; then PASS[wit-of-comp]=$(( ${PASS[wit-of-comp]:-0} + 1 ))
      else FAIL[wit-of-comp]=$(( ${FAIL[wit-of-comp]:-0} + 1 )); note wit-of-comp "$b (exit $ue/$oe) $(head -c 160 "$d/wo.err" | tr '\n' ' ')"; fi
    fi
  done
}

# --- targets -----------------------------------------------------------------------------
section_targets() {
  local T="$SRC/crates/wit-component/tests/targets"
  [[ -d $T ]] || { echo "SKIP targets: $T absent"; return; }
  for x in "$T"/*/; do
    x=${x%/}; local b; b=$(basename "$x")
    local d="$tmp/targets/$b"; mkdir -p "$d"
    "$WT" parse "$x/test.wat" -o "$d/c.wasm" 2>/dev/null || continue
    "$WT" component targets "$x/test.wit" "$d/c.wasm" >/dev/null 2>&1; local ue=$?
    "$OURS" component targets "$x/test.wit" "$d/c.wasm" >/dev/null 2>"$d/o.err"; local oe=$?
    if [[ $ue == "$oe" ]]; then PASS[targets]=$(( ${PASS[targets]:-0} + 1 ))
    else FAIL[targets]=$(( ${FAIL[targets]:-0} + 1 )); note targets "$b (exit $ue/$oe) $(head -c 160 "$d/o.err" | tr '\n' ' ')"; fi
  done
}

# --- unbundle ----------------------------------------------------------------------------
section_unbundle() {
  local U="$SRC/tests/cli"
  [[ -d $U ]] || { echo "SKIP unbundle: $U absent"; return; }
  for x in "$U"/unbundle-*.wat; do
    local b; b=$(basename "$x" .wat)
    local args; args=$(head -1 "$x" | sed -n 's/^;; RUN: component unbundle //p')
    [[ -n $args ]] || continue
    local th; th=$(echo "$args" | sed -n 's/.*--threshold \([0-9]*\).*/\1/p'); th=${th:-10240}
    local d="$tmp/unbundle/$b"; mkdir -p "$d/u" "$d/o"
    "$WT" parse "$x" -o "$d/in.wasm" 2>/dev/null || continue
    "$WT" component unbundle --module-dir "$d/u" --threshold "$th" "$d/in.wasm" -o "$d/u.wasm" 2>/dev/null; local ue=$?
    "$OURS" component unbundle --module-dir "$d/o" --threshold "$th" "$d/in.wasm" -o "$d/o.wasm" 2>"$d/o.err"; local oe=$?
    local same=1
    [[ $ue == "$oe" ]] || same=0
    if [[ $ue == 0 && $same == 1 ]]; then
      cmp -s "$d/u.wasm" "$d/o.wasm" || same=0
      for m in "$d"/u/*.wasm; do [[ -f $m ]] || continue; cmp -s "$m" "$d/o/$(basename "$m")" || same=0; done
      [[ $(ls "$d/u" | wc -l) == $(ls "$d/o" | wc -l) ]] || same=0
    fi
    if [[ $same == 1 ]]; then PASS[unbundle]=$(( ${PASS[unbundle]:-0} + 1 ))
    else FAIL[unbundle]=$(( ${FAIL[unbundle]:-0} + 1 )); hard_fail=1; note unbundle "$b (exit $ue/$oe) $(head -c 160 "$d/o.err")"; fi
  done
}

for s in "${sections[@]}"; do
  echo "== $s"
  "section_$s"
done
echo "== summary (upstream $WT, ours $OURS)"
for k in cli if-text if-wasm embed new wit-of-comp unbundle-corpus targets unbundle; do
  [[ -n ${PASS[$k]:-}${FAIL[$k]:-}${BOTH[$k]:-} ]] && \
    echo "$k: ${PASS[$k]:-0} agree, ${BOTH[$k]:-0} both refuse, ${FAIL[$k]:-0} differ"
done
[[ $keep == 1 ]] && echo "kept $tmp"
exit $hard_fail
