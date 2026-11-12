#!/usr/bin/env bash
# The general layout of `wasm-jco new` (`Adapt.emit`) on behaviour: the cases of
# tools/wasm-jco/tests/general/<case>/ (module.wat, module.wit with world `module`,
# invoke.txt). For each case, the module with its world embedded (`wasm-tools component embed`)
# is componentized by wit-component (`wasm-tools component new`) and by `wasm-jco new`; the
# output must validate, have wit-component's world, and give the same output as
# wit-component's component under pinned wasmtime for every line of invoke.txt.
#
#   tools/wasm-jco/tests/general.sh [CASE…]
#
# Cases: task-hook (`__wasm_task_hook` around allocators and exports), import-memory (a module
# importing its memory). Each output is also run through pinned jco (`jco transpile`, node) on
# the same calls when jco is installed. Skips (exit 0) when wasm-jco, wasm-tools or wasmtime is absent.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$here/pins.sh"
JCO=${SIL_JCO:-$root/.lake/build/bin/wasm-jco}
if [[ ! -x $JCO ]]; then echo "skip: wasm-jco not built at $JCO (lake build wasm-jco)"; exit 0; fi
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0
have_tool wasmtime "$WASMTIME" "$WASMTIME_SHA256" || exit 0

work=$(mktemp -d /tmp/wasm-jco-general-XXXXXX)
pass=0 fail=0
ok() { pass=$((pass + 1)); echo "  ok    $*"; }
bad() { fail=$((fail + 1)); echo "  FAIL  $*"; }

cases=("$@")
[[ ${#cases[@]} -eq 0 ]] && cases=($(ls "$here/general"))
for c in "${cases[@]}"; do
  d=$here/general/$c
  o=$work/$c
  mkdir -p "$o"
  if ! "$WASM_TOOLS" parse "$d/module.wat" -o "$o/m.wasm" 2> "$o/err" ||
     ! "$WASM_TOOLS" component embed "$d/module.wit" "$o/m.wasm" --world module -o "$o/e.wasm" 2> "$o/err"; then
    bad "$c: parse/embed: $(tail -1 "$o/err")"; continue
  fi
  "$WASM_TOOLS" component new "$o/e.wasm" -o "$o/wc.wasm" 2> "$o/wc.err" || { bad "$c: wasm-tools component new: $(tail -1 "$o/wc.err")"; continue; }
  "$JCO" new "$o/e.wasm" -o "$o/mj.wasm" > "$o/mj.log" 2>&1 || { bad "$c: wasm-jco new: $(tail -1 "$o/mj.log")"; continue; }
  "$WASM_TOOLS" validate --features all "$o/mj.wasm" 2> "$o/val.err" || { bad "$c: validate: $(head -2 "$o/val.err" | tr '\n' ' ')"; continue; }
  "$WASM_TOOLS" component wit "$o/mj.wasm" > "$o/mj.wit" 2>&1
  "$WASM_TOOLS" component wit "$o/wc.wasm" > "$o/wc.wit" 2>&1
  if cmp -s "$o/mj.wit" "$o/wc.wit"; then ok "$c: validates, world equals wit-component's"
  else bad "$c: world differs (diff $o/wc.wit $o/mj.wit)"; continue; fi
  # jco transpile of wasm-jco's component (node resolves the WASI shims through a link to the
  # pinned jco's node_modules)
  js=
  if have_tool jco "$JCO_JS" "$JCO_JS_SHA256" > /dev/null && command -v node > /dev/null; then
    if node "$JCO_JS" transpile "$o/mj.wasm" -o "$o/js" --name m > "$o/jco.log" 2>&1 &&
       node "$JCO_JS" transpile "$o/wc.wasm" -o "$o/jswc" --name m > "$o/jcowc.log" 2>&1; then
      ln -s "$JCO_DIR/node_modules" "$o/node_modules"
      js=$o/js/m.js
      ok "$c: jco transpile accepts wasm-jco's component"
    else bad "$c: jco transpile: $(tail -1 "$o/jco.log")"; fi
  fi
  while IFS= read -r call; do
    [[ -n $call ]] || continue
    a=$("$WASMTIME" run -W component-model-async=y --invoke "$call" "$o/wc.wasm" 2>&1); ra=$?
    b=$("$WASMTIME" run -W component-model-async=y --invoke "$call" "$o/mj.wasm" 2>&1); rb=$?
    if [[ $ra == 0 && $a == "$b" && $ra == "$rb" ]]; then ok "$c: $call = $b"
    else bad "$c: $call: wit-component's gives '$a' ($ra), wasm-jco's '$b' ($rb)"; continue; fi
    if [[ -n $js ]]; then
      # under jco, wasm-jco's component must answer as wit-component's does (jco may itself
      # differ from wasmtime: it lowers an empty string without calling the allocator)
      r=$(node "$here/jco-run.mjs" "$js" "$call" "$a" 2>&1 | tail -1)
      rw=$(node "$here/jco-run.mjs" "$o/jswc/m.js" "$call" "$a" 2>&1 | tail -1)
      case $r in
        skip*) echo "  note  $c (node): $call: ${r#skip: }" ;;
        *) if [[ $r == "$rw" ]]; then ok "$c (jco transpile, node): $call: ${r} (as wit-component's)"
           else bad "$c (jco transpile, node): $call: wasm-jco's '$r', wit-component's '$rw'"; fi ;;
      esac
    fi
  done < "$d/invoke.txt"
done
echo "general: $pass passed, $fail failed (work: $work)"
[[ $fail == 0 ]]
