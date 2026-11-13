#!/usr/bin/env bash
# `wasm-jco component wit` and `wasm-jco embed` against `wasm-tools component wit` and
# `wasm-tools component embed` (wasm-tools 1.262.0), on wit-component's test corpus
# (crates/wit-component/tests/components; install.sh):
#   * embed: for every case with a `module.wat` and a WIT package, `wasm-jco embed DIR m.wasm
#     --world module` must succeed exactly when `wasm-tools component embed` does, and write
#     the same bytes (`embed-bytes`), else the same world (`embed-world`: the embedded world
#     printed by `wasm-wit extract`-equivalent `wasm-tools component wit`);
#   * component wit: on the component `wasm-tools component new` writes from that module, and on
#     the WIT package `wasm-tools component wit DIR --wasm`, the text must be wasm-tools'.
#
#   tools/wasm-jco/tests/wit-cmd.sh [CASE…]
#
# Known differences are listed with their reason in wit-cmd.xfail (counted as xfail).
#
# Environment: SIL_JCO, SIL_TOOLS (pins.sh). Skips (exit 0) when wasm-jco, wasm-tools or
# the corpus is absent.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$here/pins.sh"
JCO=${SIL_JCO:-$root/.lake/build/bin/wasm-jco}

if [[ ! -x $JCO ]]; then echo "skip: wasm-jco not built at $JCO (lake build wasm-jco)"; exit 0; fi
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0
if [[ ! -d $WIT_COMPONENT_TESTS ]]; then echo "skip: wit-component tests not installed at $WIT_COMPONENT_TESTS (install.sh)"; exit 0; fi

work=$(mktemp -d /tmp/wasm-jco-witcmd-XXXXXX)
pass=0 fail=0 both=0 xfail=0 xpass=0
xf=$here/wit-cmd.xfail
# KEY: "CASE KIND" (KIND: embed, wit-comp, wit-pkg); a listed difference is an xfail, a listed
# case that passes is an xpass (reported; the list should then be cut)
listed() { grep -q "^$1	" "$xf"; }
ok() { if listed "$1"; then xpass=$((xpass + 1)); echo "  XPASS $1 (listed in wit-cmd.xfail)"; else pass=$((pass + 1)); fi; }
bad() { if listed "$1"; then xfail=$((xfail + 1)); else fail=$((fail + 1)); echo "  FAIL  $1: $2"; fi; }

cases=("$@")
[[ ${#cases[@]} -eq 0 ]] && cases=($(ls "$WIT_COMPONENT_TESTS"))
for c in "${cases[@]}"; do
  d=$WIT_COMPONENT_TESTS/$c
  [[ -f $d/module.wat ]] || continue
  o=$work/$c
  mkdir -p "$o"
  "$WASM_TOOLS" parse "$d/module.wat" -o "$o/m.wasm" 2> /dev/null || continue
  # embed
  "$WASM_TOOLS" component embed "$d" "$o/m.wasm" --world module -o "$o/e-wt.wasm" 2> "$o/e-wt.err"; wt=$?
  "$JCO" embed "$d" "$o/m.wasm" --world module -o "$o/e-mj.wasm" > "$o/e-mj.log" 2>&1; mj=$?
  if [[ $wt != 0 && $mj != 0 ]]; then both=$((both + 1))
  elif [[ $wt != 0 ]]; then bad "$c embed" "accepted what wasm-tools rejects ($(tail -1 "$o/e-wt.err"))"
  elif [[ $mj != 0 ]]; then bad "$c embed" "refused ($(tail -1 "$o/e-mj.log"))"
  elif cmp -s "$o/e-wt.wasm" "$o/e-mj.wasm"; then ok "$c embed"; echo "  ok    $c embed: same bytes"
  elif LC_ALL=C sed 's/wit-component\x070\.263\.0/wit-component\x070.262.0/' "$o/e-mj.wasm" | cmp -s "$o/e-wt.wasm" -; then
    # wasm-wit's encoder records `processed-by: wit-component 0.263.0` (it follows wasm-tools
    # 1.263.0, tests/wasm-wit/differential.sh); the pinned 1.262.0 writes 0.262.0
    ok "$c embed"; echo "  ok    $c embed: same bytes up to the wit-component version (0.263.0 for 0.262.0)"
  else
    "$WASM_TOOLS" component wit "$o/e-wt.wasm" > "$o/e-wt.wit" 2>&1
    "$WASM_TOOLS" component wit "$o/e-mj.wasm" > "$o/e-mj.wit" 2>&1
    if cmp -s "$o/e-wt.wit" "$o/e-mj.wit"; then ok "$c embed"; echo "  ok    $c embed: same world (bytes differ)"
    else bad "$c embed" "another world (diff $o/e-wt.wit $o/e-mj.wit)"; fi
  fi
  # component wit on wit-component's component and on the WIT package
  for kind in comp pkg; do
    if [[ $kind == comp ]]; then
      [[ $wt == 0 ]] || continue
      "$WASM_TOOLS" component new "$o/e-wt.wasm" -o "$o/in-$kind.wasm" 2> /dev/null || continue
    else
      "$WASM_TOOLS" component wit "$d" --wasm -o "$o/in-$kind.wasm" 2> /dev/null || continue
    fi
    "$WASM_TOOLS" component wit "$o/in-$kind.wasm" > "$o/wt-$kind.wit" 2> /dev/null || continue
    if ! "$JCO" component wit "$o/in-$kind.wasm" -o "$o/mj-$kind.wit" > "$o/mj-$kind.log" 2>&1; then
      bad "$c wit-$kind" "refused ($(tail -1 "$o/mj-$kind.log"))"
    elif cmp -s "$o/wt-$kind.wit" "$o/mj-$kind.wit"; then ok "$c wit-$kind"; echo "  ok    $c wit-$kind"
    else bad "$c wit-$kind" "differs (diff $o/wt-$kind.wit $o/mj-$kind.wit)"; fi
  done
done

echo "component wit / embed: $pass passed, $fail failed, $xfail xfail, $xpass xpass, $both rejected by both (work: $work)"
[[ $fail == 0 ]]
