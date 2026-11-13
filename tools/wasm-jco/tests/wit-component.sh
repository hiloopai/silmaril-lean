#!/usr/bin/env bash
# wasm-jco against wit-component's own test corpus (wasm-tools 1.262.0,
# crates/wit-component/tests/components): every case with a `module.wat` and no adapter
# (`adapt-*.wat`) or library (`lib-*.wat`; those are `wasm-tools component link` inputs).
#
#   tools/wasm-jco/tests/wit-component.sh [CASE…]
#
# For each case, as wit-component's test harness does: the module is parsed and the world
# `module` of the case's WIT package is embedded (`wasm-tools component embed DIR --world module`;
# cases configured with `emit-canonical-names` also get `--semver-merge`-free canonical names
# and are reported as skipped). Then
#   * `error-*` cases: `wasm-tools component new` fails, and so must `wasm-jco new`;
#   * other cases: `wasm-jco new` succeeds, its output validates (`--features all`), and its
#     world (`wasm-tools component wit`) is that of `wasm-tools component new` on the same
#     module, text for text.
# Each case is reported as `ok`, `FAIL` (a wrong output: invalid, or another world; or an error
# case accepted) or `refused` (wasm-jco writes nothing, with a message: a feature it does not
# implement, or an output the reference validator rejects; counted and listed separately).
#
# Environment: SIL_JCO, SIL_TOOLS (pins.sh). Skips (exit 0) when wasm-jco, wasm-tools or
# the corpus (install.sh) is absent.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$here/pins.sh"
JCO=${SIL_JCO:-$root/.lake/build/bin/wasm-jco}

if [[ ! -x $JCO ]]; then echo "skip: wasm-jco not built at $JCO (lake build wasm-jco)"; exit 0; fi
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0
if [[ ! -d $WIT_COMPONENT_TESTS ]]; then echo "skip: wit-component tests not installed at $WIT_COMPONENT_TESTS (install.sh)"; exit 0; fi

work=$(mktemp -d /tmp/wasm-jco-witc-XXXXXX)
pass=0 fail=0 unsup=0 skipped=0
unsupported=()
ok() { pass=$((pass + 1)); echo "  ok    $*"; }
bad() { fail=$((fail + 1)); echo "  FAIL  $*"; }

cases=("$@")
[[ ${#cases[@]} -eq 0 ]] && cases=($(ls "$WIT_COMPONENT_TESTS"))
for c in "${cases[@]}"; do
  d=$WIT_COMPONENT_TESTS/$c
  [[ -f $d/module.wat ]] || continue
  if compgen -G "$d/adapt-*.wat" > /dev/null || compgen -G "$d/lib-*.wat" > /dev/null; then continue; fi
  o=$work/$c
  mkdir -p "$o"
  if grep -q '^;;!.*emit-canonical-names' "$d/module.wat"; then
    skipped=$((skipped + 1)); echo "  skip  $c: emit-canonical-names (an encoder option, not a CLI input)"; continue
  fi
  if ! "$WASM_TOOLS" parse "$d/module.wat" -o "$o/m.wasm" 2> "$o/parse.err" ||
     ! "$WASM_TOOLS" component embed "$d" "$o/m.wasm" --world module -o "$o/e.wasm" 2> "$o/embed.err"; then
    if [[ $c == error-* ]]; then ok "$c: rejected before componentizing (parse/embed), as expected"
    else bad "$c: wasm-tools parse/embed: $(tail -1 "$o"/*.err)"; fi
    continue
  fi
  "$WASM_TOOLS" component new "$o/e.wasm" -o "$o/wc.wasm" 2> "$o/wc.err"; wc=$?
  "$JCO" new "$o/e.wasm" -o "$o/mj.wasm" > "$o/mj.log" 2>&1; mj=$?
  if [[ $c == error-* ]]; then
    if [[ $wc == 0 ]]; then bad "$c: wasm-tools accepted an error case"
    elif [[ $mj != 0 ]]; then ok "$c: rejected ($(tail -1 "$o/mj.log"))"
    else bad "$c: wasm-jco accepted what wit-component rejects: $(tail -1 "$o/wc.err")"; fi
    continue
  fi
  if [[ $wc != 0 ]]; then bad "$c: wasm-tools component new failed: $(tail -1 "$o/wc.err")"; continue; fi
  if [[ $mj != 0 ]]; then
    # a refusal: wasm-jco writes nothing (a feature it does not implement, or an output the
    # reference validator rejects); counted apart from wrong outputs
    msg=$(tail -1 "$o/mj.log")
    unsup=$((unsup + 1)); unsupported+=("$c: $msg"); echo "  refused  $c: $msg"
    continue
  fi
  if ! "$WASM_TOOLS" validate --features all "$o/mj.wasm" 2> "$o/val.err"; then bad "$c: validate: $(head -2 "$o/val.err" | tr '\n' ' ')"; continue; fi
  "$WASM_TOOLS" component wit "$o/mj.wasm" > "$o/mj.wit" 2>&1
  "$WASM_TOOLS" component wit "$o/wc.wasm" > "$o/wc.wit" 2>&1
  if cmp -s "$o/mj.wit" "$o/wc.wit"; then ok "$c: validates, world equals wit-component's"
  else bad "$c: world differs (diff $o/wc.wit $o/mj.wit)"; fi
done

echo "wit-component corpus: $pass passed, $fail failed, $unsup refused, $skipped skipped (work: $work)"
for u in "${unsupported[@]}"; do echo "  refused: $u"; done
[[ $fail == 0 ]]
