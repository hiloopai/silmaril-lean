#!/usr/bin/env bash
# Check the committed WASI 0.3 example components (dist/) with the pinned tools:
#   * dist/SHA256SUMS;
#   * wasm-tools 1.262.0: `validate --features all`, and the world of each component
#     (imports wasi:cli/*@0.3.0 only, exports wasi:cli/run@0.3.0);
#   * wasmtime 50.0.0 (`-S p3 -W component-model-async`): hello prints its line, echo its
#     arguments, cat copies 0 B, 1 B, 4095 B, 4096 B, 4097 B and 1 MiB of random bytes (release and
#     debug builds) exactly.
# Each tool step prints SKIP when its pinned binary is absent from ~/.cache/silmaril-tools.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
TOOLS=${SIL_TOOLS:-$HOME/.cache/silmaril-tools}
WT=$TOOLS/wasm-tools-1.262.0/wasm-tools
WM=$TOOLS/wasmtime-50.0.0/wasmtime
cd "$here/dist"
sha256sum -c --quiet SHA256SUMS && echo "ok: SHA256SUMS"
fail=0
if [[ -x $WT ]]; then
  for f in hello.wasm echo.wasm cat.wasm cat-debug.wasm; do
    "$WT" validate --features all "$f" || { echo "FAIL: validate $f"; fail=1; continue; }
    world=$("$WT" component wit "$f" | sed -n '/^world root {/,/^}/p' | grep -E '^\s+(import|export) ')
    if grep -vqE '^\s+(import wasi:cli/(types|stdin|stdout|environment)@0\.3\.0;|export wasi:cli/run@0\.3\.0;)$' <<<"$world"; then
      echo "FAIL: unexpected world for $f:"; echo "$world"; fail=1
    else
      echo "ok: $f validates; world $(tr -s ' \n' ' ' <<<"$world")"
    fi
  done
else
  echo "SKIP: wasm-tools 1.262.0 absent ($WT)"
fi
if [[ -x $WM ]]; then
  run() { "$WM" run -S p3 -W component-model-async "$@"; }
  [[ $(run hello.wasm) == "Hello, WASI 0.3!" ]] && echo "ok: hello" || { echo "FAIL: hello"; fail=1; }
  [[ $(run echo.wasm a 'b c' d) == "a b c d" ]] && echo "ok: echo" || { echo "FAIL: echo"; fail=1; }
  tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
  for n in 0 1 4095 4096 4097 1048576; do
    head -c "$n" /dev/urandom > "$tmp/in"
    for f in cat.wasm cat-debug.wasm; do
      run "$f" < "$tmp/in" > "$tmp/out"
      cmp -s "$tmp/in" "$tmp/out" && echo "ok: $f copies $n bytes" || { echo "FAIL: $f on $n bytes"; fail=1; }
    done
  done
else
  echo "SKIP: wasmtime 50.0.0 absent ($WM)"
fi
exit $fail
