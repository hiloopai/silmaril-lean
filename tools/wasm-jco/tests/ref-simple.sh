#!/usr/bin/env bash
# `wasm-jco new --ref` (Silmaril/Wasm/JcoTool/RefSimple): components in the layout of the
# reference bridge `Simple.toRef`, which the reference machine runs as their IR component
# (`RefSimple.newRef_sound`). For the world `refs` of refsimple/ (bool, integers, char,
# no imports) and its core module:
#   1. `wasm-jco new --ref` succeeds and prints the `ref:` lines and `reference-valid: yes`;
#   2. `wasm-tools validate` accepts the output, and `wasm-jco validate` reports
#      `reference-valid: yes`;
#   3. every invocation of refsimple/invoke.txt gives the expected result under wasmtime, both
#      for the `--ref` output and for the default output of `wasm-jco new` (the two agree);
#      `boom` traps in both; `count` keeps its state across calls in one instance is not
#      observable through `--invoke` (one call per run), so it is called once;
#   4. a WAC document instantiating the `--ref` package twice is composed by `wasm-wac compose
#      --wasm` and by the pinned wac; both outputs validate, have the same WIT and run
#      `add(1, 2)` and `neg(5)` (the algebra reads such packages with `RefSimple.rdRef`:
#      `Wac.RefPkg.composeText_ref`); skipped when wac is absent;
#   5. imports (`RefSimpleI`, the layout of `SimpleI.toRef`): the world `quad` (two imports, two
#      exports; its core module imports them as "env" "name") with `--ref`: `ref:` lines,
#      `reference-valid: yes` from the tool and from `wasm-jco validate`, wasm-tools validate;
#      plugged (`wasm-wac plug` and `wac plug`) with the `--ref` output of world `dbl`, both
#      plugs validate and compute `quad(3) = 12` and `odd-double(3) = false` (wac part skipped
#      when wac is absent);
#   6. negative controls: `--ref` refuses a float type, a world import the core module does not
#      import from "env", a world export the core module lacks and one at a mismatched core type.
#
#   tools/wasm-jco/tests/ref-simple.sh
#
# Pinned wasm-tools and wasmtime (tools/wasm-jco/tests/pins.sh); skips (exit 0) with a message
# when one is absent.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$here/pins.sh"
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0
have_tool wasmtime "$WASMTIME" "$WASMTIME_SHA256" || exit 0
cd "$root"
log=$(mktemp)
lake build wasm-jco wasm-wac > "$log" 2>&1 || { tail -20 "$log"; exit 1; }
J=$root/.lake/build/bin/wasm-jco
MW=$root/.lake/build/bin/wasm-wac
d=$here/refsimple
work=$(mktemp -d /tmp/wasm-jco-refsimple-XXXXXX)
pass=0 fail=0
ok() { pass=$((pass + 1)); }
bad() { fail=$((fail + 1)); echo "  FAIL  $*"; }

"$WASM_TOOLS" parse "$d/refs.wat" -o "$work/core.wasm" || { echo "wasm-tools parse failed"; exit 1; }

if "$J" new "$work/core.wasm" --ref --wit "$d/refs.wit" --world refs -o "$work/ref.wasm" > "$work/ref.log" 2>&1; then
  ok
  grep -q "^ref: the bytes are the reference component Simple.toRef" "$work/ref.log" && ok || bad "no ref: line"
  grep -q "^reference-valid: yes" "$work/ref.log" && ok || bad "new --ref: $(grep reference-valid "$work/ref.log")"
else
  bad "new --ref: $(tail -1 "$work/ref.log")"
fi
"$J" new "$work/core.wasm" --wit "$d/refs.wit" --world refs -o "$work/def.wasm" > "$work/def.log" 2>&1 \
  && ok || bad "new: $(tail -1 "$work/def.log")"

for c in ref def; do
  "$WASM_TOOLS" validate "$work/$c.wasm" && ok || bad "$c: wasm-tools validate"
  "$J" validate "$work/$c.wasm" | grep -q "^reference-valid: yes" && ok \
    || bad "$c: $("$J" validate "$work/$c.wasm" | grep reference-valid)"
done
# the --ref layout: parameter names of Simple.toRef
"$WASM_TOOLS" component wit "$work/ref.wasm" > "$work/ref.wit" 2>&1 \
  && grep -q "add: func(a: u32, ax: u32) -> u32" "$work/ref.wit" && ok \
  || bad "ref: unexpected component type: $(grep 'add:' "$work/ref.wit")"

while IFS=$'\t' read -r inv want; do
  for c in ref def; do
    got=$("$WASMTIME" run --invoke "$inv" "$work/$c.wasm" 2>&1)
    if [[ $got == "$want" ]]; then ok; else bad "$c $inv: got '$got', want '$want'"; fi
  done
done < "$d/invoke.txt"
for c in ref def; do
  got=$("$WASMTIME" run --invoke 'tick()' "$work/$c.wasm" 2>&1) && ok || bad "$c tick(): $got"
  if "$WASMTIME" run --invoke 'boom(1)' "$work/$c.wasm" > "$work/boom.log" 2>&1; then
    bad "$c boom(1) did not trap"
  else
    grep -q "unreachable" "$work/boom.log" && ok || bad "$c boom(1): $(tail -1 "$work/boom.log")"
  fi
done
echo "  ok    refs: --ref and default outputs agree on $(wc -l < "$d/invoke.txt") invocations, tick, boom"

if have_tool wac "$WAC" "$WAC_SHA256"; then
  mkdir -p "$work/m/deps/test" "$work/w/deps/test"
  cp "$work/ref.wasm" "$work/m/deps/test/refs.wasm"; cp "$work/ref.wasm" "$work/w/deps/test/refs.wasm"
  printf 'package test:refcomp;\n\nlet a = new test:refs {};\nlet b = new test:refs {};\nexport a.add;\nexport b.neg;\n' > "$work/c.wac"
  "$MW" compose "$work/c.wac" --deps "$work/m/deps" --wasm -o "$work/m.wasm" > "$work/wac.log" 2>&1 && ok \
    || bad "wasm-wac compose: $(tail -1 "$work/wac.log")"
  "$WAC" compose "$work/c.wac" --deps-dir "$work/w/deps" -o "$work/w.wasm" > "$work/wac.log" 2>&1 && ok \
    || bad "wac compose: $(tail -1 "$work/wac.log")"
  for c in m w; do
    "$WASM_TOOLS" validate "$work/$c.wasm" && ok || bad "wac $c: wasm-tools validate"
    [[ $("$WASMTIME" run --invoke 'add(1, 2)' "$work/$c.wasm" 2>&1) == 3 ]] && ok || bad "wac $c: add(1, 2)"
    [[ $("$WASMTIME" run --invoke 'neg(5)' "$work/$c.wasm" 2>&1) == -5 ]] && ok || bad "wac $c: neg(5)"
    "$WASM_TOOLS" component wit "$work/$c.wasm" > "$work/$c.wit" 2>&1
  done
  cmp -s "$work/m.wit" "$work/w.wit" && ok || bad "wac: the two compositions have different WIT"
  echo "  ok    WAC composition of two --ref instances (wasm-wac and wac agree)"
fi

"$WASM_TOOLS" parse "$d/quad.wat" -o "$work/quad.core.wasm" && "$WASM_TOOLS" parse "$d/dbl.wat" -o "$work/dbl.core.wasm" \
  || { echo "wasm-tools parse failed"; exit 1; }
if "$J" new "$work/quad.core.wasm" --ref --wit "$d/quad.wit" --world quad -o "$work/quad.wasm" > "$work/quad.log" 2>&1; then
  ok
  grep -q "^ref: the bytes are the reference component SimpleI.toRef" "$work/quad.log" && ok || bad "quad: no ref: line"
  grep -q "^reference-valid: yes" "$work/quad.log" && ok || bad "quad: $(grep reference-valid "$work/quad.log")"
else
  bad "quad: new --ref: $(tail -1 "$work/quad.log")"
fi
"$J" new "$work/dbl.core.wasm" --ref --wit "$d/dbl.wit" --world dbl -o "$work/dbl.wasm" > "$work/dbl.log" 2>&1 \
  && ok || bad "dbl: new --ref: $(tail -1 "$work/dbl.log")"
for c in quad dbl; do
  "$WASM_TOOLS" validate "$work/$c.wasm" && ok || bad "$c: wasm-tools validate"
  "$J" validate "$work/$c.wasm" | grep -q "^reference-valid: yes" && ok || bad "$c: not reference-valid"
done
if have_tool wac "$WAC" "$WAC_SHA256"; then
  "$MW" plug "$work/quad.wasm" --plug "$work/dbl.wasm" -o "$work/pm.wasm" > "$work/plug.log" 2>&1 && ok \
    || bad "wasm-wac plug: $(tail -1 "$work/plug.log")"
  "$WAC" plug "$work/quad.wasm" --plug "$work/dbl.wasm" -o "$work/pw.wasm" > "$work/plug.log" 2>&1 && ok \
    || bad "wac plug: $(tail -1 "$work/plug.log")"
  for c in pm pw; do
    "$WASM_TOOLS" validate "$work/$c.wasm" && ok || bad "plug $c: wasm-tools validate"
    [[ $("$WASMTIME" run --invoke 'quad(3)' "$work/$c.wasm" 2>&1) == 12 ]] && ok || bad "plug $c: quad(3)"
    [[ $("$WASMTIME" run --invoke 'odd-double(3)' "$work/$c.wasm" 2>&1) == false ]] && ok || bad "plug $c: odd-double(3)"
  done
  echo "  ok    imports: quad --ref plugged with dbl --ref (wasm-wac and wac)"
fi

echo "negative controls"
for w in float imports missing mistyped; do
  if "$J" new "$work/core.wasm" --ref --wit "$d/$w.wit" --world "$w" -o "$work/neg.wasm" > "$work/neg.log" 2>&1; then
    bad "$w: --ref accepted it"
  else
    ok; echo "  ok    $w refused: $(tail -1 "$work/neg.log")"
  fi
done

echo "ref-simple: $pass passed, $fail failed"
rm -rf "$work"
[[ $fail -eq 0 ]]
