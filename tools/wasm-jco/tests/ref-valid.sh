#!/usr/bin/env bash
# wasm-jco's outputs read as reference components (Silmaril/Wasm/JcoTool/LayoutRef): for every
# component of tools/wasm-jco/tests/cases (NAME.wat + NAME.wit), and for the stream modules
# of `wasm-streams-gen core/tee -o` (certified bytes) and `wasm-jco kcore -o` (KCore.gen):
#   1. `wasm-jco new --wit` (and `--lime`, except for `--adaptor` cases) succeeds;
#   2. for worlds with interfaces, named types or resources, its summary has the `reference:`
#      line (`ToolV.newFullR`: the output translates to the reference `Syntax.Component` and
#      `readRef` of it is the layout the world describes, `newFullR_correct`);
#   3. `wasm-jco validate` prints `reference-valid: yes`: the bytes, read as a reference
#      Core 3.0 component (silmaril's verified decoder for the core modules), pass the
#      reference validator `Reference.check?` with every feature gate (`refCheck_valid`:
#      `Reference.Valid`);
# and negative controls: two invalid components (a dangling export, a lift at a mismatched type)
# that `wasm-tools parse` assembles are reported `reference-valid: no`.
#
#   tools/wasm-jco/tests/ref-valid.sh
#
# Pinned wasm-tools (tools/wasm-jco/tests/pins.sh) assembles the cases' WAT; skips (exit 0)
# with a message when it is absent.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$here/pins.sh"
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0
cd "$root"
log=$(mktemp)
lake build wasm-jco wasm-streams-gen > "$log" 2>&1 || { tail -20 "$log"; exit 1; }
J=$root/.lake/build/bin/wasm-jco
G=$root/.lake/build/bin/wasm-streams-gen
work=$(mktemp -d /tmp/wasm-jco-refvalid-XXXXXX)
pass=0 fail=0 refs=0
ok() { pass=$((pass + 1)); }
bad() { fail=$((fail + 1)); echo "  FAIL  $*"; }

# one LABEL CORE WIT WORLD [FLAGS...]
one() {
  local label=$1 core=$2 wit=$3 world=$4; shift 4
  "$J" new "$core" --wit "$wit" --world "$world" "$@" -o "$work/o.wasm" > "$work/new.log" 2>&1 \
    || { bad "$label: wasm-jco new: $(tail -1 "$work/new.log")"; return; }
  ok
  if grep -q "^layout:" "$work/new.log"; then
    if grep -q "^reference: " "$work/new.log"; then ok; refs=$((refs + 1)); else bad "$label: no reference line"; fi
  fi
  if "$J" validate "$work/o.wasm" | grep -q "^reference-valid: yes"; then ok
  else bad "$label: $("$J" validate "$work/o.wasm" | grep '^reference-valid')"; fi
}

for dir in "$here"/cases/*/; do
  c0=$fail; n0=$pass
  for wit in "$dir"*.wit; do
    n=$(basename "$wit" .wit)
    "$WASM_TOOLS" parse "$dir/$n.wat" -o "$work/$n.core.wasm" || { bad "$n: wasm-tools parse"; continue; }
    if [[ $(cat "$dir/$n.ir") == adaptor ]]; then
      one "$n --adaptor" "$work/$n.core.wasm" "$wit" "$n" --adaptor
    else
      one "$n" "$work/$n.core.wasm" "$wit" "$n"
      one "$n --lime" "$work/$n.core.wasm" "$wit" "$n" --lime
    fi
  done
  [[ $fail -eq $c0 ]] && echo "  ok    case $(basename "$dir"): $((pass - n0)) checks"
done

c0=$fail
for k in map filter take7 lines rechunk3; do
  "$G" wit t0 > "$work/t0.wit"
  "$G" core t0 "$k" 8 -o "$work/k.wasm" && one "streams-gen $k" "$work/k.wasm" "$work/t0.wit" t0
  "$J" kcore t0 "$k" 8 -o "$work/kc.wasm" && one "kcore $k" "$work/kc.wasm" "$work/t0.wit" t0
done
"$G" teewit t0 > "$work/tee.wit"
"$G" tee t0 4 -o "$work/tee.wasm" && one "tee" "$work/tee.wasm" "$work/tee.wit" t0
[[ $fail -eq $c0 ]] && echo "  ok    generated stream modules"

echo "negative controls"
# a component exporting a function that does not exist, and one lifting a core function at a
# component type whose flattening does not match it
printf '(component (export "f" (func 0)))' > "$work/bad1.wat"
printf '(component (core module (func (export "g"))) (core instance (instantiate 0)) (type (func (param "x" u32))) (alias core export 0 "g" (core func)) (func (type 0) (canon lift (core func 0))) (export "f" (func 0)))' > "$work/bad2.wat"
for b in bad1 bad2; do
  "$WASM_TOOLS" parse "$work/$b.wat" -o "$work/$b.wasm" || { bad "$b: wasm-tools parse"; continue; }
  if "$J" validate "$work/$b.wasm" | grep -q "^reference-valid: no"; then ok; echo "  ok    $b rejected by the reference validator"
  else bad "$b: not rejected"; fi
done

echo "reference reading: $pass passed, $fail failed ($refs outputs with the reference layout line)"
rm -rf "$work"
[[ $fail -eq 0 ]]
