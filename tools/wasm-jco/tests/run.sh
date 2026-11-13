#!/usr/bin/env bash
# The wasm-jco test suite: build every case component with wasm-jco, validate it with the
# pinned wasm-tools, compare its world with wit-component's (`wasm-tools component new`) and
# jco's (`jco new`) output for the same core module, compose with the pinned wac, and run the
# invocations of each case under the pinned wasmtime (and, for synchronous cases, under node
# through `jco transpile`), on wasm-jco's (default and `--lime`) and on wit-component's
# components alike.
#
#   tools/wasm-jco/tests/run.sh [CASE…]       (default: every directory of cases/)
#
# Environment: SIL_JCO (default .lake/build/bin/wasm-jco; build it with
# `lake build wasm-jco`), SIL_TOOLS (see pins.sh). Skips, with a message and exit 0,
# when wasm-jco or a pinned tool is absent, so CI without the tools is unaffected.
#
# A case directory holds components NAME.wat + NAME.wit (world NAME) with NAME.ir (`yes` when
# wasm-jco must read the output back as a thin wrapper, `no` otherwise, `adaptor` for a
# C-convention module built with `--adaptor`; wit-component cannot wrap such a module, so its
# reference world is that of `wasm-tools component embed --dummy`), optionally
# compose.txt (lines `MAIN PLUG…`: `wac plug MAIN --plug PLUG…`, named MAIN+PLUG+…),
# invoke.txt (lines `TARGET<TAB>INVOCATION<TAB>EXPECTED`, in WAVE) and flags.txt (the -W flags
# of wasmtime) and NAME.proc (exports that must pass the shape check of
# Silmaril.Wasm.JcoTool.StreamSem, the hypothesis of `newWith_stream_semantics`).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$here/pins.sh"
JCO=${SIL_JCO:-$root/.lake/build/bin/wasm-jco}

if [[ ! -x $JCO ]]; then echo "skip: wasm-jco not built at $JCO (lake build wasm-jco)"; exit 0; fi
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0
have_tool wasmtime "$WASMTIME" "$WASMTIME_SHA256" || exit 0
have_tool wac "$WAC" "$WAC_SHA256" || exit 0
use_jco=0
if command -v node >/dev/null && have_tool jco "$JCO_JS" "$JCO_JS_SHA256"; then use_jco=1; fi

work=$(mktemp -d /tmp/wasm-jco-tests-XXXXXX)
pass=0 fail=0 skip=0
ok() { pass=$((pass + 1)); echo "  ok    $*"; }
bad() { fail=$((fail + 1)); echo "  FAIL  $*"; }
note() { skip=$((skip + 1)); echo "  skip  $*"; }

cases=("$@")
[[ ${#cases[@]} -eq 0 ]] && cases=($(ls "$here/cases"))

for c in "${cases[@]}"; do
  dir=$here/cases/$c
  out=$work/$c
  mkdir -p "$out"
  echo "case $c"
  flags=""
  [[ -f $dir/flags.txt ]] && flags="-W $(cat "$dir/flags.txt")"
  for wit in "$dir"/*.wit; do
    n=$(basename "$wit" .wit)
    "$WASM_TOOLS" parse "$dir/$n.wat" -o "$out/$n.core.wasm" || { bad "$n: wasm-tools parse"; continue; }
    want_ir=$(cat "$dir/$n.ir")
    mode=()
    [[ $want_ir == adaptor ]] && { mode=(--adaptor); want_ir=no; }
    # wasm-jco, world from WIT text
    if "$JCO" new "$out/$n.core.wasm" --wit "$wit" --world "$n" "${mode[@]}" -o "$out/$n.mj.wasm" > "$out/$n.mj.log" 2>&1; then
      ok "$n: wasm-jco new --wit ${mode[*]}"
    else bad "$n: wasm-jco new --wit: $(tail -1 "$out/$n.mj.log")"; continue; fi
    if [[ -f $dir/$n.proc ]]; then
      for e in $(cat "$dir/$n.proc"); do
        grep -q "^proc:  export $e has the shape" "$out/$n.mj.log" && ok "$n: export $e has the Proc transformer shape" || bad "$n: export $e fails the Proc shape check"
      done
    fi
    got_ir=$(sed -n 's/^ir: *\([a-z]*\).*/\1/p' "$out/$n.mj.log")
    [[ $got_ir == "$want_ir" ]] && ok "$n: ir read-back $got_ir" || bad "$n: ir read-back $got_ir, expected $want_ir"
    "$WASM_TOOLS" validate --features all "$out/$n.mj.wasm" && ok "$n: wasm-tools validate" || bad "$n: wasm-tools validate"
    "$JCO" validate "$out/$n.mj.wasm" > "$out/$n.mj.validate"
    # Lime-preserving mode: the module through the 3.0 -> Lime compiler, every core module Lime1
    if "$JCO" new "$out/$n.core.wasm" --wit "$wit" --world "$n" "${mode[@]}" --lime -o "$out/$n.ml.wasm" > "$out/$n.ml.log" 2>&1 &&
       "$WASM_TOOLS" validate --features all "$out/$n.ml.wasm"; then
      ok "$n: wasm-jco new --lime ${mode[*]}, validate"
    else bad "$n: wasm-jco new --lime: $(tail -1 "$out/$n.ml.log")"; fi
    "$WASM_TOOLS" component wit "$out/$n.mj.wasm" > "$out/$n.mj.wit"
    if [[ ${#mode[@]} -gt 0 ]]; then
      # the reference world: a dummy module of the same world through wit-component
      "$WASM_TOOLS" component embed "$wit" --dummy --world "$n" -o "$out/$n.dummy.wasm"
      "$WASM_TOOLS" component new "$out/$n.dummy.wasm" -o "$out/$n.dummy.c.wasm"
      "$WASM_TOOLS" component wit "$out/$n.dummy.c.wasm" > "$out/$n.dummy.wit"
      cmp -s "$out/$n.mj.wit" "$out/$n.dummy.wit" && ok "$n: same world as wit-component's dummy" || bad "$n: world differs from the dummy's"
      "$WASM_TOOLS" component embed "$wit" "$out/$n.core.wasm" --world "$n" -o "$out/$n.embed.wasm"
      if "$JCO" new "$out/$n.embed.wasm" --adaptor -o "$out/$n.mje.wasm" > "$out/$n.mje.log" 2>&1; then
        "$WASM_TOOLS" component wit "$out/$n.mje.wasm" > "$out/$n.mje.wit"
        cmp -s "$out/$n.mje.wit" "$out/$n.dummy.wit" && ok "$n: wasm-jco new --adaptor (embedded world)" || bad "$n: embedded world differs"
      else bad "$n: wasm-jco new --adaptor (embedded world): $(tail -1 "$out/$n.mje.log")"; fi
      continue
    fi
    # the reference: wit-component through wasm-tools
    "$WASM_TOOLS" component embed "$wit" "$out/$n.core.wasm" --world "$n" -o "$out/$n.embed.wasm"
    "$WASM_TOOLS" component new "$out/$n.embed.wasm" -o "$out/$n.wc.wasm" || { bad "$n: wasm-tools component new"; continue; }
    "$WASM_TOOLS" component wit "$out/$n.wc.wasm" > "$out/$n.wc.wit"
    cmp -s "$out/$n.mj.wit" "$out/$n.wc.wit" && ok "$n: same world as wit-component" || bad "$n: world differs from wit-component (diff $out/$n.mj.wit $out/$n.wc.wit)"
    # wasm-jco, world from the embedded component-type section
    if "$JCO" new "$out/$n.embed.wasm" -o "$out/$n.mje.wasm" > "$out/$n.mje.log" 2>&1; then
      "$WASM_TOOLS" component wit "$out/$n.mje.wasm" > "$out/$n.mje.wit"
      cmp -s "$out/$n.mje.wit" "$out/$n.wc.wit" && ok "$n: wasm-jco new (embedded world)" || bad "$n: embedded world differs"
    elif grep -q 'disagree on async' "$out/$n.mje.log"; then
      note "$n: embedded world: wasm-wit's decoder rejects the async function names of wasm-tools $WASM_TOOLS_VERSION (known gap, docs/projects/wasm-components.md)"
    else bad "$n: wasm-jco new (embedded world): $(tail -1 "$out/$n.mje.log")"; fi
    # jco new (wit-component in JS)
    if [[ $use_jco == 1 ]]; then
      if node "$JCO_JS" new "$out/$n.embed.wasm" -o "$out/$n.jco.wasm" > /dev/null 2>&1; then
        "$WASM_TOOLS" component wit "$out/$n.jco.wasm" > "$out/$n.jco.wit"
        cmp -s "$out/$n.mj.wit" "$out/$n.jco.wit" && ok "$n: same world as jco new" || bad "$n: world differs from jco new"
      else note "$n: jco new rejects the module"; fi
    fi
  done
  # compositions
  if [[ -f $dir/compose.txt ]]; then
    while read -r main plugs; do
      [[ -z $main ]] && continue
      name=$main
      for impl in mj ml wc; do
        [[ -f $out/$main.$impl.wasm ]] || continue
        args=()
        name=$main
        for p in $plugs; do args+=(--plug "$out/$p.$impl.wasm"); name=$name+$p; done
        if "$WAC" plug "$out/$main.$impl.wasm" "${args[@]}" -o "$out/$name.$impl.wasm" 2> "$out/$name.$impl.wac.log" &&
           "$WASM_TOOLS" validate --features all "$out/$name.$impl.wasm"; then
          ok "$name ($impl): wac plug, validate"
        else bad "$name ($impl): wac plug: $(tail -1 "$out/$name.$impl.wac.log")"; fi
      done
    done < "$dir/compose.txt"
  fi
  # invocations
  if [[ -f $dir/invoke.txt ]]; then
    while IFS=$'\t' read -r target inv want; do
      [[ -z $target ]] && continue
      for impl in mj ml wc; do
        [[ -f $out/$target.$impl.wasm ]] || continue
        got=$("$WASMTIME" run $flags --invoke "$inv" "$out/$target.$impl.wasm" 2>&1)
        [[ $got == "$want" ]] && ok "$target ($impl): $inv = $want" || bad "$target ($impl): $inv = $got, expected $want"
      done
      if [[ $use_jco == 1 && -z $flags ]]; then
        js=$out/js-$target
        if [[ ! -d $js ]]; then node "$JCO_JS" transpile "$out/$target.mj.wasm" -o "$js" --name m > /dev/null 2>&1; fi
        r=$(node "$here/jco-run.mjs" "$js/m.js" "$inv" "$want" 2>&1 | tail -1)
        case $r in
          ok) ok "$target (wasm-jco, jco transpile, node): $inv = $want" ;;
          skip*) note "$target (node): $inv: ${r#skip: }" ;;
          *) bad "$target (node): $inv: $r" ;;
        esac
      fi
    done < "$dir/invoke.txt"
  fi
done

echo "wasm-jco tests: $pass passed, $fail failed, $skip skipped (work: $work)"
[[ $fail -eq 0 ]]
