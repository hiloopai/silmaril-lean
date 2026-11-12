#!/usr/bin/env bash
# The emission of the generated stream modules (Silmaril/Wasm/JcoTool/KCoreEmit): the bytes
# `wasm-jco kcore NAME KERNEL N -o OUT.wasm` writes (silmaril's verified encoder,
# `KCoreEmit.wasmOf_encodes`), the checked text of the original printer (`--printer`,
# `watChecked_encodes`) and the text of silmaril's proved printer (the default,
# `watOf_encodes`), against
# wasm-tools, then the verified bytes through `wasm-jco new` and wasmtime. Both generators are
# covered: the default `KDrop.genD` (`KDropEmit.kdrop_bytes`, `kdrop_wat`) and, with
# `--baseline`, round 1's `KCore.gen`.
#
#   tools/wasm-jco/tests/kcore-emit.sh [SEEDS]      (default 2 seeds per component)
#
# For each kernel (map, filter, take0, take1, take7, lines, rechunk1, rechunk3, rechunk255) and
# read size N in 1, 5, 64, 256:
#   1. the three outputs succeed (the tool refuses an output whose check fails);
#   2. `wasm-tools parse` of the printer's text, without custom sections (`strip --all`: the
#      text names its imports, which wasm-tools records in a `name` section), is byte-identical
#      to the verified bytes, and so is `wasm-tools parse` of the canonical text;
#   3. `wasm-tools validate --features all` of the verified bytes;
#   4. `wasm-jco new --wit` on the verified bytes reports the export's `Proc` shape, its
#      output validates, and a driver of `wasm-streams-gen driver SEED KERNEL` plugged with
#      `wac plug` prints 42 under `wasmtime run -W
#      component-model-async=y,component-model-async-stackful=y` (N in 1, 64 only).
#
# Pinned tools: tools/wasm-jco/tests/pins.sh. Skips (exit 0) with a message when a tool is
# absent; fails when its SHA-256 differs from the pin.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$here/pins.sh"
seeds=${1:-2}
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0
have_tool wasmtime "$WASMTIME" "$WASMTIME_SHA256" || exit 0
have_tool wac "$WAC" "$WAC_SHA256" || exit 0
cd "$root"
log=$(mktemp)
lake build wasm-jco wasm-streams-gen > "$log" 2>&1 || { tail -20 "$log"; exit 1; }
G=$root/.lake/build/bin/wasm-streams-gen
J=$root/.lake/build/bin/wasm-jco
work=$(mktemp -d /tmp/wasm-jco-kcore-emit-XXXXXX)
pass=0 fail=0
ok() { pass=$((pass + 1)); }
bad() { fail=$((fail + 1)); echo "  FAIL  $*"; }

kernels=(map filter take0 take1 take7 lines rechunk1 rechunk3 rechunk255)
for mode in genD gen; do
if [[ $mode == gen ]]; then fl=(--baseline); else fl=(); fi
echo "generator: $mode"
for k in "${kernels[@]}"; do
  for b in 1 5 64 256; do
    c0=$fail
    "$J" kcore t0 "$k" "$b" "${fl[@]}" --printer > "$work/p.wat" || { bad "$k $b: kcore --printer (checked printer)"; continue; }
    "$J" kcore t0 "$k" "$b" "${fl[@]}" > "$work/c.wat" || { bad "$k $b: kcore (proved canonical printer)"; continue; }
    "$J" kcore t0 "$k" "$b" "${fl[@]}" -o "$work/v.wasm" || { bad "$k $b: kcore -o"; continue; }
    ok
    "$WASM_TOOLS" parse "$work/p.wat" -o "$work/p.wasm" && "$WASM_TOOLS" strip --all "$work/p.wasm" -o "$work/ps.wasm" \
      || { bad "$k $b: wasm-tools parse (printer)"; continue; }
    if cmp -s "$work/ps.wasm" "$work/v.wasm"; then ok; else bad "$k $b: printer's text and verified bytes differ"; fi
    "$WASM_TOOLS" parse "$work/c.wat" -o "$work/c.wasm" || { bad "$k $b: wasm-tools parse (canonical)"; continue; }
    if cmp -s "$work/c.wasm" "$work/v.wasm"; then ok; else bad "$k $b: canonical text and verified bytes differ"; fi
    if "$WASM_TOOLS" validate --features all "$work/v.wasm"; then ok; else bad "$k $b: validate"; continue; fi
    [[ $b == 1 || $b == 64 ]] || { [[ $fail -eq $c0 ]] && echo "  ok    $k (N $b): bytes, printer, canonical text"; continue; }
    "$G" wit t0 > "$work/t0.wit"
    "$J" new "$work/v.wasm" --wit "$work/t0.wit" --world t0 -o "$work/t0.wasm" > "$work/new.log" 2>&1 \
      || { bad "$k $b: wasm-jco new: $(tail -1 "$work/new.log")"; continue; }
    if grep -q "^proc:  export t0 " "$work/new.log"; then ok; else bad "$k $b: no Proc shape reported"; fi
    if "$WASM_TOOLS" validate --features all "$work/t0.wasm"; then ok; else bad "$k $b: validate component"; continue; fi
    for s in $(seq 1 "$seeds"); do
      "$G" driver "$s" "$k" > "$work/drv.wat" && "$WASM_TOOLS" parse "$work/drv.wat" -o "$work/drv.wasm" \
        || { bad "$k $b seed $s: driver"; continue; }
      "$WAC" plug "$work/drv.wasm" --plug "$work/t0.wasm" -o "$work/comp.wasm" > "$work/wac.log" 2>&1 \
        || { bad "$k $b seed $s: wac plug: $(tail -1 "$work/wac.log")"; continue; }
      out=$("$WASMTIME" run -W component-model-async=y,component-model-async-stackful=y --invoke 'run()' "$work/comp.wasm" 2>&1 | tail -1)
      if [[ $out == 42 ]]; then ok; else bad "$k $b seed $s: got $out"; fi
    done
    [[ $fail -eq $c0 ]] && echo "  ok    $k (N $b): bytes, printer, canonical text, $seeds runs"
  done
done
done

echo "negative control"
"$J" kcore t0 map 300 -o "$work/neg.wasm" > /dev/null 2>&1 && bad "kcore accepted N = 300" || { ok; echo "  ok    N = 300 refused"; }

echo "KCore emission: $pass passed, $fail failed"
rm -rf "$work"
[[ $fail -eq 0 ]]
