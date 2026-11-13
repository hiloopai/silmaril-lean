#!/usr/bin/env bash
# `wasm-jco new --adaptor` with an exported interface (AdaptorI, theorem AdaptorI.newAdaptorI_correct).
#
#   tools/wasm-jco/tests/adaptor-iface.sh
#
# Case tools/wasm-jco/tests/adaptoriface: `cconvi.wat` follows the C convention of
# Silmaril.Wasm.Jco.Meta and exports the functions of interface `test:ai/greet` under
# wit-component's core names, and a world-level function. Checks:
#   1. `wasm-jco new --wit cconvi.wit --world cconvi --adaptor` succeeds; `wasm-tools validate
#      --features all`; the world (`wasm-tools component wit`) equals that of wit-component on a
#      dummy module of the same world (`component embed --dummy` + `component new`);
#   2. a canonical-ABI user component (`user.wat`, thin wrapper by `wasm-jco new`) importing the
#      interface is plugged with `wac plug`; under wasmtime `run(20, 22)` = 42 and `hi("x")` =
#      "hello, x" go through the adaptor's lifts in the interface instance; `count([1, 2, 3])` = 3
#      on the adaptor component itself.
# Pinned tools: tools/wasm-jco/tests/pins.sh; skips (exit 0) when a tool is absent.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$here/pins.sh"
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0
have_tool wasmtime "$WASMTIME" "$WASMTIME_SHA256" || exit 0
have_tool wac "$WAC" "$WAC_SHA256" || exit 0
cd "$root"
log=$(mktemp)
lake build wasm-jco > "$log" 2>&1 || { tail -20 "$log"; exit 1; }
J=$root/.lake/build/bin/wasm-jco
D=$here/adaptoriface
W=$(mktemp -d /tmp/wasm-jco-adaptor-iface-XXXXXX)
pass=0 fail=0
ok() { pass=$((pass + 1)); echo "  ok    $*"; }
bad() { fail=$((fail + 1)); echo "  FAIL  $*"; }
"$WASM_TOOLS" parse "$D/cconvi.wat" -o "$W/cconvi.core.wasm"
if "$J" new "$W/cconvi.core.wasm" --wit "$D/cconvi.wit" --world cconvi --adaptor -o "$W/cconvi.wasm" > "$W/mj.log" 2>&1; then
  ok "wasm-jco new --adaptor (interface test:ai/greet)"
else bad "wasm-jco new --adaptor: $(tail -1 "$W/mj.log")"; fi
"$WASM_TOOLS" validate --features all "$W/cconvi.wasm" && ok "validate" || bad "validate"
"$WASM_TOOLS" component embed --dummy --world cconvi "$D/cconvi.wit" -o "$W/d.wasm" \
  && "$WASM_TOOLS" component new "$W/d.wasm" -o "$W/dn.wasm"
if [[ $("$WASM_TOOLS" component wit "$W/cconvi.wasm") == $("$WASM_TOOLS" component wit "$W/dn.wasm") ]]; then
  ok "world equals wit-component's (dummy module)"
else bad "world differs from wit-component's"; fi
"$WASM_TOOLS" parse "$D/user.wat" -o "$W/user.core.wasm"
"$J" new "$W/user.core.wasm" --wit "$D/user.wit" --world user -o "$W/user.wasm" > /dev/null 2>&1 || bad "user component"
"$WAC" plug "$W/user.wasm" --plug "$W/cconvi.wasm" -o "$W/comp.wasm" > /dev/null 2>&1 || bad "wac plug"
check() {
  local comp=$1 call=$2 want=$3 got
  got=$("$WASMTIME" run --invoke "$call" "$comp" 2>&1 | tail -1)
  [[ $got == "$want" ]] && ok "$call = $want" || bad "$call: got $got, want $want"
}
check "$W/comp.wasm" 'run(20, 22)' 42
check "$W/comp.wasm" 'hi("x")' '"hello, x"'
check "$W/comp.wasm" 'hi("")' '"hello, "'
check "$W/cconvi.wasm" 'count([1, 2, 3])' 3
echo "adaptor with interfaces: $pass passed, $fail failed"
rm -rf "$W"
[[ $fail -eq 0 ]]
