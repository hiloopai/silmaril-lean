#!/usr/bin/env bash
# Stream components whose core modules come from the drop-aware generator `KDrop.genD`
# (Silmaril/Wasm/JcoTool/KDrop; theorems in KDrop.Thms), built with wasm-jco, validated with
# wasm-tools, compared with wit-component and run under wasmtime, alone and in chains.
#
#   tools/wasm-jco/tests/kdrop.sh [SEEDS]      (default 5 seeds per pipeline)
#
# As tools/wasm-jco/tests/kcore.sh, with `wasm-kdrop` in place of `wasm-jco kcore`, and the
# chains are counted: every chain run must print 42 (`T.run` of the composite). These are the
# chains that trap with `KCore.gen` (the DROPPED event on an idle end, and a downstream reader
# that drops while the module writes), plus more of them.
#
# Pinned tools: tools/wasm-jco/tests/pins.sh (wasm-tools 1.262.0, wasmtime 50.0.0 run with
# -W component-model-async=y,component-model-async-stackful=y, wac 0.12.0). Skips (exit 0) with a
# message when a tool is absent; fails when its SHA-256 differs from the pin.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$here/pins.sh"
seeds=${1:-5}
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0
have_tool wasmtime "$WASMTIME" "$WASMTIME_SHA256" || exit 0
have_tool wac "$WAC" "$WAC_SHA256" || exit 0
cd "$root"
log=$(mktemp)
lake build wasm-jco wasm-kdrop wasm-streams-gen > "$log" 2>&1 || { tail -20 "$log"; exit 1; }
G=$root/.lake/build/bin/wasm-streams-gen
J=$root/.lake/build/bin/wasm-jco
K=$root/.lake/build/bin/wasm-kdrop
work=$(mktemp -d /tmp/wasm-jco-kdrop-XXXXXX)
pass=0 fail=0
ok() { pass=$((pass + 1)); }
bad() { fail=$((fail + 1)); echo "  FAIL  $*"; }
WT=("$WASMTIME" run -W component-model-async=y,component-model-async-stackful=y --invoke 'run()')

# build NAME KERNEL N into $work/{mj,wc}/NAME.wasm
build() {
  local n=$1 k=$2 b=$3
  "$K" "$n" "$k" "$b" > "$work/$n.wat" || { bad "$k: wasm-kdrop"; return 1; }
  "$G" wit "$n" > "$work/$n.wit"
  "$WASM_TOOLS" parse "$work/$n.wat" -o "$work/$n.core.wasm" || { bad "$k: wasm-tools parse"; return 1; }
  mkdir -p "$work/mj" "$work/wc"
  "$J" new "$work/$n.core.wasm" --wit "$work/$n.wit" --world "$n" -o "$work/mj/$n.wasm" > "$work/$n.mj.log" 2>&1 \
    || { bad "$k: wasm-jco new: $(tail -1 "$work/$n.mj.log")"; return 1; }
  if grep -q "^proc:  export $n " "$work/$n.mj.log"; then ok; else bad "$k: no Proc shape reported"; fi
  "$WASM_TOOLS" validate --features all "$work/mj/$n.wasm" || { bad "$k: validate (wasm-jco)"; return 1; }
  "$WASM_TOOLS" component embed --world "$n" "$work/$n.wit" "$work/$n.core.wasm" -o "$work/$n.emb.wasm" \
    && "$WASM_TOOLS" component new "$work/$n.emb.wasm" -o "$work/wc/$n.wasm" \
    || { bad "$k: wit-component"; return 1; }
  "$WASM_TOOLS" validate --features all "$work/wc/$n.wasm" || { bad "$k: validate (wit-component)"; return 1; }
  if [[ $("$WASM_TOOLS" component wit "$work/mj/$n.wasm") == $("$WASM_TOOLS" component wit "$work/wc/$n.wasm") ]]; then ok
  else bad "$k: worlds differ (wasm-jco vs wit-component)"; return 1; fi
  ok
}

# run TAG DRIVER-ARGS... : plug the driver with t0..t2 of mj and wc, expect 42
run() {
  local tag=$1; shift
  "$G" "$@" > "$work/drv.wat" && "$WASM_TOOLS" parse "$work/drv.wat" -o "$work/drv.wasm" || { bad "$tag: driver"; return; }
  local plugs out
  for v in mj wc; do
    plugs=()
    for t in t0 t1 t2; do
      if "$WASM_TOOLS" component wit "$work/drv.wasm" | grep -q "import $t:"; then plugs+=(--plug "$work/$v/$t.wasm"); fi
    done
    "$WAC" plug "$work/drv.wasm" "${plugs[@]}" -o "$work/comp.wasm" > "$work/wac.log" 2>&1 || { bad "$tag ($v): wac plug: $(tail -1 "$work/wac.log")"; continue; }
    out=$("${WT[@]}" "$work/comp.wasm" 2>&1)
    if [[ $(tail -1 <<< "$out") == 42 ]]; then ok; else bad "$tag ($v): got $(tail -3 <<< "$out" | tr '\n' ' ')"; fi
  done
}

kernels=(map filter take7 take0 lines rechunk3 rechunk1)
echo "single components (KDrop.genD)"
for k in "${kernels[@]}"; do
  for b in 1 5 64; do
    c0=$fail
    build t0 "$k" "$b" || continue
    for s in $(seq 1 "$seeds"); do run "$k batch $b seed $s" driver "$s" "$k"; done
    [[ $fail -eq $c0 ]] && echo "  ok    $k (read batch $b): $seeds seeds, wasm-jco and wit-component"
  done
done

echo "chains of separate generated components (counted: every run must print 42)"
chains=("lines filter" "filter rechunk3" "lines filter map" "take0 map lines" "map take7" "rechunk1 take7 map"
        "take7 map" "take0 map" "map take0" "lines take7" "take7 take0" "filter lines take7" "rechunk3 rechunk1"
        "map map map" "take7 lines filter")
for ch in "${chains[@]}"; do
  read -r -a ks <<< "$ch"
  c0=$fail
  for off in 2 1; do
    i=0
    for k in "${ks[@]}"; do build "t$i" "$k" $((i * 3 + off)) > /dev/null || true; i=$((i + 1)); done
    for s in $(seq 1 "$seeds"); do run "chain $ch (read sizes from $off) seed $s" driver "$s" "${ks[@]}"; done
  done
  [[ $fail -eq $c0 ]] && echo "  ok    chain $ch: $((seeds * 2)) runs, wasm-jco and wit-component"
done

echo "negative control"
build t0 map 4 > /dev/null
"$G" driver 1 filter > "$work/neg.wat" && "$WASM_TOOLS" parse "$work/neg.wat" -o "$work/neg.wasm" \
  && "$WAC" plug "$work/neg.wasm" --plug "$work/mj/t0.wasm" -o "$work/negc.wasm" > /dev/null 2>&1
out=$("${WT[@]}" "$work/negc.wasm" 2>&1 | tail -1)
if [[ $out != 42 ]]; then ok; echo "  ok    map component checked against filter's T.run: $out (not 42)"; else bad "negative control printed 42"; fi

echo "KDrop stream components: $pass passed, $fail failed"
rm -rf "$work"
[[ $fail -eq 0 ]]
