#!/usr/bin/env bash
# The shapes the reference translation leaves out (Silmaril/Wasm/JcoTool/LayoutRefX):
#   1. a component with core module types, which `LayoutRef.toRef` rejected, is translated by
#      `toRefX` and reported `reference-valid: yes` by `wasm-jco validate`
#      (`ToolV.refCheckX_valid`); wasm-tools validates it too;
#   2. each shape `toRefX` still rejects, written in the binary format (one section appended to
#      a valid prefix; the text format has no syntax for most of them), is rejected by
#      `wasm-tools validate` and reported `reference-valid: no` by `wasm-jco validate`: an
#      export of a core function, an export of a core instance, an alias of a core function
#      from a component instance export, an outer alias of a core function, a core-instance
#      export alias of a component function, a resource with an `f32` representation; a
#      control (the valid alias of the core export alone) is accepted by both.
#
#   tools/wasm-jco/tests/ref-gaps.sh
#
# Pinned wasm-tools (tools/wasm-jco/tests/pins.sh); skips (exit 0) with a message when absent.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$here/pins.sh"
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0
cd "$root"
log=$(mktemp)
lake build wasm-jco > "$log" 2>&1 || { tail -20 "$log"; exit 1; }
J=$root/.lake/build/bin/wasm-jco
work=$(mktemp -d /tmp/wasm-jco-refgaps-XXXXXX)
pass=0 fail=0
ok() { pass=$((pass + 1)); }
bad() { fail=$((fail + 1)); echo "  FAIL  $*"; }

# 1. core module types
cat > "$work/mt.wat" <<'WAT'
(component
  (core type $mt (module
    (type $f (func (param i32) (result i32)))
    (import "env" "g" (func (type $f)))
    (import "env" "mem" (memory 1 2))
    (import "env" "tab" (table 1 funcref))
    (import "env" "glob" (global (mut i64)))
    (export "f" (func (type $f)))))
  (core module $m (func (export "f") (param i32) (result i32) local.get 0))
  (core instance $i (instantiate $m))
  (type $t (func (param "x" u32) (result u32)))
  (alias core export $i "f" (core func $cf))
  (func $f (type $t) (canon lift (core func $cf)))
  (export "f" (func $f)))
WAT
"$WASM_TOOLS" parse "$work/mt.wat" -o "$work/mt.wasm" && ok || bad "mt: wasm-tools parse"
"$WASM_TOOLS" validate "$work/mt.wasm" && ok || bad "mt: wasm-tools validate"
if "$J" validate "$work/mt.wasm" | grep -q "^reference-valid: yes"; then ok; echo "  ok    core module type: reference-valid: yes"
else bad "mt: $("$J" validate "$work/mt.wasm" | grep reference-valid)"; fi

# 2. shapes outside the Component Model, written in the binary format (the text format has no
# syntax for most of them): one section appended to a valid prefix, b1 (a core module exporting
# "f" and its instance) or b2 (an imported instance exporting a function "f").
printf '(component (core module $m (func (export "f"))) (core instance $i (instantiate $m)))' > "$work/b1.wat"
printf '(component (type $ft (func)) (import "i" (instance $i (export "f" (func (type $ft))))))' > "$work/b2.wat"
"$WASM_TOOLS" parse "$work/b1.wat" -o "$work/b1.wasm" && "$WASM_TOOLS" parse "$work/b2.wat" -o "$work/b2.wasm" \
  || { echo "wasm-tools parse of the prefixes failed"; exit 1; }
# NAME PREFIX BYTES
negative() {
  cp "$work/$2.wasm" "$work/$1.wasm"
  printf "$3" >> "$work/$1.wasm"
  if "$WASM_TOOLS" validate "$work/$1.wasm" > "$work/$1.log" 2>&1; then bad "$1: wasm-tools accepts it"
  else ok; echo "  ok    $1: wasm-tools: $(head -1 "$work/$1.log")"; fi
  if "$J" validate "$work/$1.wasm" | grep -q "^reference-valid: no"; then ok
  else bad "$1: wasm-jco validate: $("$J" validate "$work/$1.wasm" | grep reference-valid)"; fi
}
# control: the alias of the core export alone is valid
negative_control() {
  cp "$work/b1.wasm" "$work/ctl.wasm"
  printf '\x06\x07\x01\x00\x00\x01\x00\x01f' >> "$work/ctl.wasm"
  "$WASM_TOOLS" validate "$work/ctl.wasm" && ok || bad "control: wasm-tools rejects it"
  "$J" validate "$work/ctl.wasm" | grep -q "^reference-valid: yes" && ok || bad "control: not reference-valid"
}
negative_control
# (alias core export 0 "f" (core func)) (export "f" (core func 0))
negative export-core-func b1 '\x06\x07\x01\x00\x00\x01\x00\x01f\x0b\x08\x01\x00\x01f\x00\x00\x00\x00'
# (export "i" (core instance 0))
negative export-core-instance b1 '\x0b\x08\x01\x00\x01i\x00\x12\x00\x00'
# (alias export 0 "f" (core func))
negative alias-export-core-func b2 '\x06\x07\x01\x00\x00\x00\x00\x01f'
# (alias outer 0 0 (core func))
negative alias-outer-core-func b1 '\x06\x06\x01\x00\x00\x02\x00\x00'
# (alias core export 0 "f" (func))
negative core-alias-of-func b1 '\x06\x06\x01\x01\x01\x00\x01f'
# (type (resource (rep f32)))
negative resource-rep-f32 b1 '\x07\x04\x01\x3f\x7d\x00'

echo "ref-gaps: $pass passed, $fail failed"
rm -rf "$work"
[[ $fail -eq 0 ]]
