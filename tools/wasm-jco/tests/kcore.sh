#!/usr/bin/env bash
# Stream components whose core modules come from `wasm-jco kcore`, i.e. the drop-aware generator
# `KDrop.genD` (Silmaril/Wasm/JcoTool/KDrop; theorems in KDrop.Thms: `step_sim`, `kchain_correct`,
# `ktee_correct`; the bytes and text in KDropEmit.Thms), built with wasm-jco, validated with
# wasm-tools, compared with wit-component and run under wasmtime: alone, in chains and in tees.
#
#   tools/wasm-jco/tests/kcore.sh [--baseline] [SEEDS]      (default 5 seeds per pipeline)
#
# For each kernel (map, filter, take7, take0, lines, rechunk3, rechunk1) and read sizes 1, 5, 64:
#   1. `wasm-jco kcore t0 KERNEL N` prints the module (WAT); `wasm-tools parse` assembles it;
#   2. `wasm-jco new --wit` builds the component and must report the export's `Proc` shape
#      (`proc:` line, StreamSem.xfShape); `wasm-tools validate --features all`; its world must
#      equal wit-component's (`wasm-tools component embed` + `component new` on the same module);
#   3. a driver component of `wasm-streams-gen driver SEED KERNEL` (random input in random chunks,
#      random read sizes; it returns 42 iff the output is `T.run` of the specification
#      transformer) is plugged with `wac plug`, and `wasmtime run -W
#      component-model-async=y,component-model-async-stackful=y --invoke 'run()'` must print 42,
#      for wasm-jco's and wit-component's component;
# then chains of two and three separately generated components (counted: every run must print
# 42), tees whose two branches are generated components (`wasm-streams-gen teedriver SEED K1 K2`:
# input → tee → (K1, K2), both outputs checked), first with the template tee of
# `wasm-streams-gen tee`, then with the GENERATED tee `wasm-streams-gen gtee` (`KTee.genT`,
# proved to refine the `Net` tee node: KTee.Thms `step_sim`, KTeeNet.Thms `gtee_correct`; its
# bytes and text in KTeeEmit.Thms), and a negative control.
#
# With --baseline the modules come from `wasm-jco kcore --baseline` (round 1's `KCore.gen`, a
# documented baseline over the `Async` model): single components are counted as above, and the
# chain runs are only reported (correct / trapped outside the model / other), as 
# (17 correct and 13 trapped with 5 seeds). Tees are not run in this mode.
#
# Pinned tools: tools/wasm-jco/tests/pins.sh. Skips (exit 0) with a message when a tool is
# absent; fails when its SHA-256 differs from the pin.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$here/pins.sh"
base=()
if [[ ${1:-} == --baseline ]]; then base=(--baseline); shift; fi
seeds=${1:-5}
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0
have_tool wasmtime "$WASMTIME" "$WASMTIME_SHA256" || exit 0
have_tool wac "$WAC" "$WAC_SHA256" || exit 0
cd "$root"
log=$(mktemp)
lake build wasm-jco wasm-streams-gen > "$log" 2>&1 || { tail -20 "$log"; exit 1; }
G=$root/.lake/build/bin/wasm-streams-gen
J=$root/.lake/build/bin/wasm-jco
work=$(mktemp -d /tmp/wasm-jco-kcore-XXXXXX)
pass=0 fail=0
ok() { pass=$((pass + 1)); }
bad() { fail=$((fail + 1)); echo "  FAIL  $*"; }

# build NAME KERNEL N into $work/{mj,wc}/NAME.wasm
build() {
  local n=$1 k=$2 b=$3
  if [[ $k == tee ]]; then
    "$G" tee "$n" "$b" > "$work/$n.wat"; "$G" teewit "$n" > "$work/$n.wit"
  elif [[ $k == gtee ]]; then
    "$G" gtee "$n" "$b" > "$work/$n.wat" || { bad "gtee: wasm-streams-gen gtee"; return 1; }
    "$G" teewit "$n" > "$work/$n.wit"
  else "$J" kcore "$n" "$k" "$b" "${base[@]}" > "$work/$n.wat" || { bad "$k: wasm-jco kcore"; return 1; }
    "$G" wit "$n" > "$work/$n.wit"
  fi
  "$WASM_TOOLS" parse "$work/$n.wat" -o "$work/$n.core.wasm" || { bad "$k: wasm-tools parse"; return 1; }
  mkdir -p "$work/mj" "$work/wc"
  "$J" new "$work/$n.core.wasm" --wit "$work/$n.wit" --world "$n" -o "$work/mj/$n.wasm" > "$work/$n.mj.log" 2>&1 \
    || { bad "$k: wasm-jco new: $(tail -1 "$work/$n.mj.log")"; return 1; }
  if [[ $k == tee || $k == gtee ]] || grep -q "^proc:  export $n " "$work/$n.mj.log"; then ok; else bad "$k: no Proc shape reported"; fi
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
  local plugs
  for v in mj wc; do
    plugs=()
    for t in t0 t1 t2; do
      if "$WASM_TOOLS" component wit "$work/drv.wasm" | grep -q "import $t:"; then plugs+=(--plug "$work/$v/$t.wasm"); fi
    done
    "$WAC" plug "$work/drv.wasm" "${plugs[@]}" -o "$work/comp.wasm" > "$work/wac.log" 2>&1 || { bad "$tag ($v): wac plug: $(tail -1 "$work/wac.log")"; continue; }
    out=$("$WASMTIME" run -W component-model-async=y,component-model-async-stackful=y --invoke 'run()' "$work/comp.wasm" 2>&1 | tail -1)
    if [[ $out == 42 ]]; then ok; else bad "$tag ($v): got $out"; fi
  done
}

kernels=(map filter take7 take0 lines rechunk3 rechunk1)
if [[ ${#base[@]} -gt 0 ]]; then gen=KCore.gen; else gen=KDrop.genD; fi
echo "single components ($gen)"
for k in "${kernels[@]}"; do
  for b in 1 5 64; do
    c0=$fail
    build t0 "$k" "$b" || continue
    for s in $(seq 1 "$seeds"); do run "$k batch $b seed $s" driver "$s" "$k"; done
    [[ $fail -eq $c0 ]] && echo "  ok    $k (read batch $b): $seeds seeds, wasm-jco and wit-component"
  done
done

chains=("lines filter" "filter rechunk3" "lines filter map" "take0 map lines" "map take7" "rechunk1 take7 map")
if [[ ${#base[@]} -gt 0 ]]; then
  echo "chains of separate generated components (baseline: reported, not counted)"
  # A chain can leave the model 's proofs in two ways, and a `KCore.gen` module traps:
  #  * wasmtime 50 posts a STREAM_READ DROPPED event on an *idle* readable end when the writer
  #    drops (and a later read traps); Silmaril.Wasm.Component.Async posts no such event, so
  #    `Proc.tStep` has no transition for it (the module traps on the unexpected event);
  #  * a downstream `take` drops its readable end while the upstream module writes: the write
  #    reports DROPPED, which is `Proc.TPc.fault`, a state without transitions.
  # `KDrop.genD` (the default generator) handles both.
  cpass=0 ctrap=0 cother=0
  for ch in "${chains[@]}"; do
    read -r -a ks <<< "$ch"
    i=0
    for k in "${ks[@]}"; do build "t$i" "$k" $((i * 3 + 2)) > /dev/null || true; i=$((i + 1)); done
    for s in $(seq 1 "$seeds"); do
      "$G" driver "$s" "${ks[@]}" > "$work/drv.wat" && "$WASM_TOOLS" parse "$work/drv.wat" -o "$work/drv.wasm" || continue
      plugs=()
      for t in t0 t1 t2; do
        if "$WASM_TOOLS" component wit "$work/drv.wasm" | grep -q "import $t:"; then plugs+=(--plug "$work/mj/$t.wasm"); fi
      done
      "$WAC" plug "$work/drv.wasm" "${plugs[@]}" -o "$work/comp.wasm" > /dev/null 2>&1 || continue
      out=$("$WASMTIME" run -W component-model-async=y,component-model-async-stackful=y --invoke 'run()' "$work/comp.wasm" 2>&1)
      if [[ $(tail -1 <<< "$out") == 42 ]]; then cpass=$((cpass + 1))
      elif grep -q "unreachable\|cannot read from stream" <<< "$out"; then ctrap=$((ctrap + 1))
      else cother=$((cother + 1)); echo "  chain $ch seed $s: unexpected: $(tail -1 <<< "$out")"; fi
    done
  done
  echo "  chains: $cpass correct (42), $ctrap trapped outside the model, $cother other"
  [[ $cother -eq 0 ]] && ok || bad "chains: $cother runs neither correct nor a known trap"
else
  echo "chains of separate generated components (counted: every run must print 42)"
  chains+=("take7 map" "take0 map" "map take0" "lines take7" "take7 take0" "filter lines take7"
           "rechunk3 rechunk1" "map map map" "take7 lines filter")
  cruns=0
  for ch in "${chains[@]}"; do
    read -r -a ks <<< "$ch"
    c0=$fail
    for off in 2 1; do
      i=0
      for k in "${ks[@]}"; do build "t$i" "$k" $((i * 3 + off)) > /dev/null || true; i=$((i + 1)); done
      for s in $(seq 1 "$seeds"); do run "chain $ch (read sizes from $off) seed $s" driver "$s" "${ks[@]}"; cruns=$((cruns + 2)); done
    done
    [[ $fail -eq $c0 ]] && echo "  ok    chain $ch: $((seeds * 2)) runs, wasm-jco and wit-component"
  done
  echo "  chains: $cruns runs"
  echo "tees with generated branches (counted: every run must print 42)"
  tees=("map filter" "take7 lines" "take0 map" "lines rechunk3" "filter take0" "rechunk1 take7")
  truns=0
  for tp in "${tees[@]}"; do
    read -r -a ks <<< "$tp"
    c0=$fail
    for tb in 3 8; do
      build t0 tee "$tb" > /dev/null || true
      build t1 "${ks[0]}" "$((tb - 1))" > /dev/null || true
      build t2 "${ks[1]}" "$((tb + 2))" > /dev/null || true
      for s in $(seq 1 "$seeds"); do run "tee $tp (tee batch $tb) seed $s" teedriver "$s" "${ks[0]}" "${ks[1]}"; truns=$((truns + 2)); done
    done
    [[ $fail -eq $c0 ]] && echo "  ok    tee $tp: $((seeds * 2)) runs, wasm-jco and wit-component"
  done
  echo "  tees: $truns runs"
  echo "generated tees (KTee.genT) with generated branches (counted: every run must print 42)"
  gruns=0
  for tp in "${tees[@]}"; do
    read -r -a ks <<< "$tp"
    c0=$fail
    for tb in 1 3 8 256; do
      build t0 gtee "$tb" > /dev/null || true
      "$G" gtee t0 "$tb" -o "$work/gtee.wasm" && cmp -s "$work/gtee.wasm" "$work/t0.core.wasm" \
        || bad "gtee $tb: the bytes of -o differ from wasm-tools parse of the text"
      build t1 "${ks[0]}" "$(( (tb % 7) + 1 ))" > /dev/null || true
      build t2 "${ks[1]}" "$(( (tb % 5) + 2 ))" > /dev/null || true
      for s in $(seq 1 "$seeds"); do run "gtee $tp (tee batch $tb) seed $s" teedriver "$s" "${ks[0]}" "${ks[1]}"; gruns=$((gruns + 2)); done
    done
    [[ $fail -eq $c0 ]] && echo "  ok    generated tee $tp: $((seeds * 4 * 2)) runs, wasm-jco and wit-component"
  done
  echo "  generated tees: $gruns runs"
fi

echo "negative control"
build t0 map 4 > /dev/null
"$G" driver 1 filter > "$work/neg.wat" && "$WASM_TOOLS" parse "$work/neg.wat" -o "$work/neg.wasm" \
  && "$WAC" plug "$work/neg.wasm" --plug "$work/mj/t0.wasm" -o "$work/negc.wasm" > /dev/null 2>&1
out=$("$WASMTIME" run -W component-model-async=y,component-model-async-stackful=y --invoke 'run()' "$work/negc.wasm" 2>&1 | tail -1)
if [[ $out != 42 ]]; then ok; echo "  ok    map component checked against filter's T.run: $out (not 42)"; else bad "negative control printed 42"; fi

echo "kcore stream components ($gen): $pass passed, $fail failed"
rm -rf "$work"
[[ $fail -eq 0 ]]
