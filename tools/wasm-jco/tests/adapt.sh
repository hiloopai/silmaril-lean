#!/usr/bin/env bash
# `wasm-jco new --adapt` against wit-component (`wasm-tools component new --adapt`, 1.262.0).
#
#   tools/wasm-jco/tests/adapt.sh [CASE…]
#
# Part 1, wit-component's own adapter cases (crates/wit-component/tests/components of wasm-tools
# 1.262.0: every case with an `adapt-*.wat`). As its harness does, the module gets the world
# `module` of the case's WIT and each adapter `adapt-NAME.wat` the world `adapt-NAME` (the
# adapter's name is NAME, or the `;; module name:` line); a `;;! realloc-via-memory-grow`
# case passes `--realloc-via-memory-grow` to both tools. `error-*` cases must be rejected by
# both; every other case must be accepted by wasm-jco, validate, and have wit-component's world.
#
# Part 2, real WASI preview 1 programs: the Rust (pinned 1.99.1, target wasm32-wasip1) and C
# (wasi-sdk 27, with wit-bindgen 0.62.0 C bindings for `lang: c-bindgen`) programs of corpus/p1,
# componentized with the official adapters of wasmtime 50.0.0 (command and reactor,
# pinned in pins.sh) by both tools: each output must validate, have wit-component's world, and
# behave the same under pinned wasmtime (stdout, stderr, exit status) on the runs of
# corpus/p1/runs.txt.
#
# Each case is `ok`, `FAIL` or `refused` (wasm-jco writes nothing, with a message). Exit 1 on a
# FAIL. Skips (exit 0) when wasm-jco, wasm-tools or the corpus is absent; part 2 needs the
# adapters, wasmtime and the Rust wasm32-wasip1 standard library (install.sh) and is skipped
# without them.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
. "$here/pins.sh"
JCO=${SIL_JCO:-$root/.lake/build/bin/wasm-jco}

if [[ ! -x $JCO ]]; then echo "skip: wasm-jco not built at $JCO (lake build wasm-jco)"; exit 0; fi
have_tool wasm-tools "$WASM_TOOLS" "$WASM_TOOLS_SHA256" || exit 0

work=$(mktemp -d /tmp/wasm-jco-adapt-XXXXXX)
pass=0 fail=0 unsup=0
unsupported=()
ok() { pass=$((pass + 1)); echo "  ok    $*"; }
bad() { fail=$((fail + 1)); echo "  FAIL  $*"; }
refused() { unsup=$((unsup + 1)); unsupported+=("$*"); echo "  refused  $*"; }

# --- Part 1 -------------------------------------------------------------------------------
if [[ -d $WIT_COMPONENT_TESTS ]]; then
  cases=("$@")
  [[ ${#cases[@]} -eq 0 ]] && cases=($(ls "$WIT_COMPONENT_TESTS"))
  for c in "${cases[@]}"; do
    d=$WIT_COMPONENT_TESTS/$c
    [[ -f $d/module.wat ]] || continue
    compgen -G "$d/adapt-*.wat" > /dev/null || continue
    o=$work/$c
    mkdir -p "$o"
    flags=()
    if grep -qh '^;;!.*realloc-via-memory-grow *= *true' "$d"/*.wat; then flags+=(--realloc-via-memory-grow); fi
    if grep -qh '^;;!.*return-call-ref *= *true' "$d"/*.wat; then
      echo "  skip  $c: return-call-ref (an encoder option of wit-component's library, not a CLI input)"; continue
    fi
    if ! "$WASM_TOOLS" parse "$d/module.wat" -o "$o/m.wasm" 2> "$o/err" ||
       ! "$WASM_TOOLS" component embed "$d" "$o/m.wasm" --world module -o "$o/e.wasm" 2> "$o/err"; then
      bad "$c: wasm-tools parse/embed of the module: $(tail -1 "$o/err")"; continue
    fi
    wt=() mj=() ok_in=1
    for a in "$d"/adapt-*.wat; do
      stem=$(basename "$a" .wat)
      name=$(sed -n 's/^;; module name: //p' "$a" | head -1)
      [[ -n $name ]] || name=${stem#adapt-}
      if ! "$WASM_TOOLS" parse "$a" -o "$o/$stem.raw.wasm" 2> "$o/err" ||
         ! "$WASM_TOOLS" component embed "$d" "$o/$stem.raw.wasm" --world "$stem" -o "$o/$stem.wasm" 2> "$o/err"; then
        bad "$c: wasm-tools parse/embed of $stem: $(tail -1 "$o/err")"; ok_in=0; break
      fi
      wt+=(--adapt "$name=$o/$stem.wasm"); mj+=(--adapt "$name=$o/$stem.wasm")
    done
    [[ $ok_in == 1 ]] || continue
    "$WASM_TOOLS" component new "$o/e.wasm" "${wt[@]}" "${flags[@]}" -o "$o/wc.wasm" 2> "$o/wc.err"; wcrc=$?
    "$JCO" new "$o/e.wasm" "${mj[@]}" "${flags[@]}" -o "$o/mj.wasm" > "$o/mj.log" 2>&1; mjrc=$?
    if [[ $c == error-* ]]; then
      if [[ $wcrc == 0 ]]; then bad "$c: wasm-tools accepted an error case"
      elif [[ $mjrc != 0 ]]; then ok "$c: rejected ($(tail -1 "$o/mj.log"))"
      else bad "$c: wasm-jco accepted what wit-component rejects: $(tail -1 "$o/wc.err")"; fi
      continue
    fi
    if [[ $wcrc != 0 ]]; then bad "$c: wasm-tools component new failed: $(tail -1 "$o/wc.err")"; continue; fi
    if [[ $mjrc != 0 ]]; then refused "$c: $(tail -1 "$o/mj.log")"; continue; fi
    if ! "$WASM_TOOLS" validate --features all "$o/mj.wasm" 2> "$o/val.err"; then bad "$c: validate: $(head -2 "$o/val.err" | tr '\n' ' ')"; continue; fi
    "$WASM_TOOLS" component wit "$o/mj.wasm" > "$o/mj.wit" 2>&1
    "$WASM_TOOLS" component wit "$o/wc.wasm" > "$o/wc.wit" 2>&1
    if cmp -s "$o/mj.wit" "$o/wc.wit"; then ok "$c: validates, world equals wit-component's"
    else bad "$c: world differs (diff $o/wc.wit $o/mj.wit)"; fi
  done
else
  echo "skip part 1: wit-component tests not installed at $WIT_COMPONENT_TESTS (install.sh)"
fi

# --- Part 2 -------------------------------------------------------------------------------
p1() {
  have_tool wasmtime "$WASMTIME" "$WASMTIME_SHA256" || return 0
  have_tool "command adapter" "$WASI_ADAPTER_COMMAND" "$WASI_ADAPTER_COMMAND_SHA256" || return 0
  have_tool "reactor adapter" "$WASI_ADAPTER_REACTOR" "$WASI_ADAPTER_REACTOR_SHA256" || return 0
  local rustc_bin=$RUST_TOOLCHAIN/bin/rustc have_rust=1 have_c=1
  if [[ ! -x $rustc_bin ]] || [[ $("$rustc_bin" --version) != "$RUSTC_ID" ]]; then
    echo "skip the Rust programs: Rust $RUST_VERSION not installed at $RUST_TOOLCHAIN"; have_rust=0
  elif [[ ! -d $RUST_TOOLCHAIN/lib/rustlib/wasm32-wasip1 ]]; then
    echo "skip the Rust programs: no wasm32-wasip1 standard library in $RUST_TOOLCHAIN (pins.sh)"; have_rust=0
  fi
  have_tool "wasi-sdk clang" "$WASI_SDK/bin/clang-20" "$WASI_SDK_CLANG_SHA256" || have_c=0
  have_tool wit-bindgen "$WIT_BINDGEN" "$WIT_BINDGEN_SHA256" > /dev/null || have_c=0
  local src=$here/corpus/p1
  for rs in "$src"/*.rs "$src"/*.c; do
    local n kind lang adapter
    n=$(basename "${rs%.*}")
    kind=$(sed -n 's|^// kind: ||p' "$rs" | head -1)
    lang=$(sed -n 's|^// lang: ||p' "$rs" | head -1)
    [[ -n $lang ]] || lang=rust
    if [[ $lang == rust && $have_rust == 0 ]] || [[ $lang == c* && $have_c == 0 ]]; then continue; fi
    local o=$work/p1-$n
    mkdir -p "$o"
    if [[ $kind == reactor ]]; then adapter=$WASI_ADAPTER_REACTOR; else adapter=$WASI_ADAPTER_COMMAND; fi
    if [[ $lang == rust ]]; then
      local extra=()
      [[ $kind == reactor ]] && extra=(--crate-type cdylib)
      if ! RUSTUP_HOME=$RUST_HOME/rustup "$rustc_bin" --target wasm32-wasip1 -O --edition 2021 "${extra[@]}" "$rs" -o "$o/core.wasm" 2> "$o/rustc.err"; then
        bad "p1/$n: rustc: $(tail -1 "$o/rustc.err")"; continue
      fi
    else
      # C: wasi-sdk's clang; with `lang: c-bindgen`, the wit-bindgen C bindings of $n.wit (their
      # component-type object is linked in, so the world comes from the module)
      local cextra=() csrc=("$rs")
      [[ $kind == reactor ]] && cextra=(-mexec-model=reactor)
      if [[ $lang == c-bindgen ]]; then
        local world
        world=$(sed -n 's/^world \([a-z0-9-]*\).*/\1/p' "$src/$n.wit" | head -1)
        "$WIT_BINDGEN" c "$src/$n.wit" --world "$world" --out-dir "$o/gen" > /dev/null 2>&1 || { bad "p1/$n: wit-bindgen c"; continue; }
        cextra+=(-I"$o/gen")
        csrc+=("$o/gen/$world.c" "$o/gen/${world}_component_type.o")
      fi
      if ! "$WASI_SDK/bin/clang" --target=wasm32-wasip1 -O2 "${cextra[@]}" "${csrc[@]}" -o "$o/core.wasm" 2> "$o/cc.err"; then
        bad "p1/$n: clang: $(tail -1 "$o/cc.err")"; continue
      fi
    fi
    local core=$o/core.wasm
    if [[ -f $src/$n.wit && $lang != c-bindgen ]]; then
      "$WASM_TOOLS" component embed "$src/$n.wit" "$core" -o "$o/core.e.wasm" 2> "$o/err" || { bad "p1/$n: embed: $(tail -1 "$o/err")"; continue; }
      core=$o/core.e.wasm
    fi
    "$WASM_TOOLS" component new "$core" --adapt "wasi_snapshot_preview1=$adapter" -o "$o/wc.wasm" 2> "$o/wc.err" || { bad "p1/$n: wasm-tools component new: $(tail -1 "$o/wc.err")"; continue; }
    local t0 t1
    t0=$(date +%s%N)
    if ! "$JCO" new "$core" --adapt "wasi_snapshot_preview1=$adapter" -o "$o/mj.wasm" > "$o/mj.log" 2>&1; then
      refused "p1/$n: $(tail -1 "$o/mj.log")"; continue
    fi
    t1=$(date +%s%N)
    if ! "$WASM_TOOLS" validate --features all "$o/mj.wasm" 2> "$o/val.err"; then bad "p1/$n: validate: $(head -2 "$o/val.err" | tr '\n' ' ')"; continue; fi
    "$WASM_TOOLS" component wit "$o/mj.wasm" > "$o/mj.wit" 2>&1
    "$WASM_TOOLS" component wit "$o/wc.wasm" > "$o/wc.wit" 2>&1
    if cmp -s "$o/mj.wit" "$o/wc.wit"; then ok "p1/$n: validates, world equals wit-component's ($(( (t1 - t0) / 1000000 )) ms, $(stat -c %s "$core") byte module)"
    else bad "p1/$n: world differs (diff $o/wc.wit $o/mj.wit)"; continue; fi
    # behaviour: the runs of runs.txt for this program
    local k=0
    while IFS='|' read -r rn stdin args; do
      [[ $rn == "$n" ]] || continue
      k=$((k + 1))
      local w
      for w in wc mj; do
        if [[ $args == invoke:* ]]; then
          printf '%b' "$stdin" | "$WASMTIME" run -W component-model-async=y -S cli=y --invoke "${args#invoke:}" "$o/$w.wasm" > "$o/$w.$k.out" 2> "$o/$w.$k.err"
        else
          # shellcheck disable=SC2086
          printf '%b' "$stdin" | "$WASMTIME" run -W component-model-async=y -S cli=y --env SIL_P1=yes --dir "$o::/sandbox" "$o/$w.wasm" $args > "$o/$w.$k.out" 2> "$o/$w.$k.err"
        fi
        echo "exit $?" >> "$o/$w.$k.out"
      done
      if cmp -s "$o/wc.$k.out" "$o/mj.$k.out" && cmp -s "$o/wc.$k.err" "$o/mj.$k.err"; then
        ok "p1/$n run $k ($args): same stdout, stderr and exit status as wit-component's"
      else bad "p1/$n run $k ($args): differs (diff $o/wc.$k.out $o/mj.$k.out; .err)"; fi
    done < "$src/runs.txt"
  done
}
p1

echo "adapt: $pass passed, $fail failed, $unsup refused (work: $work)"
for u in "${unsupported[@]}"; do echo "  refused: $u"; done
[[ $fail == 0 ]]
