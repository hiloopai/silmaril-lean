#!/usr/bin/env bash
# Differential suite of wasm-jco against wit-component on a real-producer corpus: core modules
# written by the pinned Rust toolchain with wit-bindgen bindings (corpus/build.sh), std crates
# with five component-type sections and WASI imports at two versions, a no_std crate, sync
# records/variants/enums/flags/strings/lists, resources, async exports and imports with streams.
#
#   tools/wasm-jco/tests/corpus.sh [N]    N random arguments per numeric invocation (default 5)
#
# For every core module NAME.core.wasm it checks
#   * `wasm-jco new` (the world from the module's sections) succeeds;
#   * `wasm-tools validate --features all` accepts the output;
#   * the output's world (`wasm-tools component wit`) is the world of `wasm-tools component new`
#     on the same module, text for text;
#   * `wasm-jco validate` reads it back (`reference-valid:` verdict recorded, not required);
# and for every line `TARGET<TAB>INVOCATION` of corpus/invoke.txt (TARGET a module, or
# MAIN+PLUG composed with `wac plug`, the same way for wasm-jco's and wit-component's
# components) the output of `wasmtime run --invoke` on wasm-jco's component equals the output
# on wit-component's, which must succeed. `%N` in an invocation is replaced by N random u32 values in turn.
#
# Environment: SIL_JCO (default .lake/build/bin/wasm-jco), SIL_TOOLS (pins.sh),
# SIL_CORPUS (a directory of NAME.core.wasm; default: built by corpus/build.sh into a scratch
# directory). Skips with a message (exit 0) when wasm-jco, a pinned tool or the toolchain is
# absent.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$here/pins.sh"
JCO=${SIL_JCO:-$root/.lake/build/bin/wasm-jco}
nrand=${1:-5}

if [[ ! -x $JCO ]]; then echo "skip: wasm-jco not built at $JCO (lake build wasm-jco)"; exit 0; fi
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0
have_tool wasmtime "$WASMTIME" "$WASMTIME_SHA256" || exit 0
have_tool wac "$WAC" "$WAC_SHA256" || exit 0

work=$(mktemp -d /tmp/wasm-jco-corpus-XXXXXX)
corpus=${SIL_CORPUS:-}
if [[ -z $corpus ]]; then
  corpus=$work/core
  "$here/corpus/build.sh" "$corpus" > "$work/build.log" 2>&1 || { echo "corpus build failed: $(tail -3 "$work/build.log")"; exit 1; }
  if grep -q '^skip:' "$work/build.log"; then grep '^skip:' "$work/build.log"; exit 0; fi
fi
pass=0 fail=0
ok() { pass=$((pass + 1)); echo "  ok    $*"; }
bad() { fail=$((fail + 1)); echo "  FAIL  $*"; }
WT_FLAGS=(-W component-model-async=y,component-model-async-stackful=y)

declare -A built
for core in "$corpus"/*.core.wasm; do
  n=$(basename "$core" .core.wasm)
  echo "module $n ($(stat -c %s "$core") bytes)"
  "$WASM_TOOLS" component new "$core" -o "$work/$n.wc.wasm" 2> "$work/$n.wc.err" || { bad "$n: wasm-tools component new: $(tail -1 "$work/$n.wc.err")"; continue; }
  t0=$(date +%s%N)
  if "$JCO" new "$core" -o "$work/$n.mj.wasm" > "$work/$n.mj.log" 2>&1; then
    ms=$(( ($(date +%s%N) - t0) / 1000000 ))
    # a regression bound, far above the measured time (0.75 s for the 3.4 MB debug module)
    if (( ms < 20000 )); then ok "$n: wasm-jco new (${ms} ms)"; else bad "$n: wasm-jco new took ${ms} ms (bound 20000)"; fi
  else bad "$n: wasm-jco new: $(tail -1 "$work/$n.mj.log")"; continue; fi
  "$WASM_TOOLS" validate --features all "$work/$n.mj.wasm" 2> "$work/$n.val.err" && ok "$n: wasm-tools validate" || { bad "$n: wasm-tools validate: $(head -3 "$work/$n.val.err" | tr '\n' ' ')"; continue; }
  "$WASM_TOOLS" component wit "$work/$n.mj.wasm" > "$work/$n.mj.wit"
  "$WASM_TOOLS" component wit "$work/$n.wc.wasm" > "$work/$n.wc.wit"
  if cmp -s "$work/$n.mj.wit" "$work/$n.wc.wit"; then ok "$n: world equals wit-component's"
  else bad "$n: world differs from wit-component's ($(diff "$work/$n.wc.wit" "$work/$n.mj.wit" | grep -c '^[<>]') lines; diff $work/$n.wc.wit $work/$n.mj.wit)"; fi
  "$JCO" validate "$work/$n.mj.wasm" > "$work/$n.mj.validate" 2>&1
  echo "  info  $n: $(grep '^reference-valid' "$work/$n.mj.validate")"
  built[$n]=1
done

# compose MAIN+PLUG for both producers
target() {
  local t=$1 kind=$2
  if [[ $t != *+* ]]; then echo "$work/$t.$kind.wasm"; return; fi
  local main=${t%%+*} plug=${t#*+} f=$work/$t.$kind.wasm
  if [[ ! -f $f ]]; then "$WAC" plug "$work/$main.$kind.wasm" --plug "$work/$plug.$kind.wasm" -o "$f" 2> "$f.err" || return 1; fi
  echo "$f"
}

RANDOM=42
while IFS=$'\t' read -r tgt inv; do
  [[ -z $tgt || $tgt == \#* ]] && continue
  skipme=0
  for part in ${tgt//+/ }; do [[ -n ${built[$part]:-} ]] || skipme=1; done
  [[ $skipme == 1 ]] && { bad "$tgt: $inv (a component was not built)"; continue; }
  reps=1; [[ $inv == *%N* ]] && reps=$nrand
  for ((k = 0; k < reps; k++)); do
    i=${inv//%N/$(( (RANDOM << 15 | RANDOM) % 4294967296 ))}
    mj=$(target "$tgt" mj) || { bad "$tgt: wac plug (wasm-jco)"; break; }
    wc=$(target "$tgt" wc) || { bad "$tgt: wac plug (wit-component)"; break; }
    a=$(timeout 60 "$WASMTIME" run "${WT_FLAGS[@]}" --invoke "$i" "$mj" 2>&1); ea=$?
    b=$(timeout 60 "$WASMTIME" run "${WT_FLAGS[@]}" --invoke "$i" "$wc" 2>&1); eb=$?
    if [[ $eb != 0 ]]; then bad "$tgt: $i: wit-component's component fails (exit $eb): ${b//$'\n'/ }"
    elif [[ $ea == "$eb" && $a == "$b" ]]; then ok "$tgt: $i = ${a//$'\n'/ } (exit $ea)"
    else bad "$tgt: $i: wasm-jco '${a//$'\n'/ }' (exit $ea), wit-component '${b//$'\n'/ }' (exit $eb)"; fi
  done
done < "$here/corpus/invoke.txt"

echo "corpus: $pass passed, $fail failed (work: $work)"
[[ $fail == 0 ]]
