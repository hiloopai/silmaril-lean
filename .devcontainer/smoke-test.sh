#!/bin/sh
set -eu

lean --version
lake --version
elan --version
python3 -c 'import sys; assert sys.version_info >= (3, 11); print(sys.version)'
node -e 'if (Number(process.versions.node.split(".")[0]) < 24) process.exit(1); if (!WebAssembly.validate(Uint8Array.of(0,97,115,109,1,0,0,0))) process.exit(1); console.log(process.version)'
make --version

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
printf '%s\n' 'int main(void) { return 0; }' > "$tmp/smoke.c"
cc "$tmp/smoke.c" -o "$tmp/smoke"
"$tmp/smoke"
printf '%s\n' 'def main : IO Unit := IO.println "Lean environment OK"' > "$tmp/Smoke.lean"
lean --run "$tmp/Smoke.lean"
lean --root="$tmp" -c "$tmp/Smoke.c" "$tmp/Smoke.lean"
leanc "$tmp/Smoke.c" -o "$tmp/lean-smoke"
"$tmp/lean-smoke"
make help
sh scripts/sil --help

if [ "${1:-}" = --cross-test ]; then
  wasm-opt --version
  wasmtime --version
  printf '%s\n' '(module (func (export "answer") (result i32) (i32.const 42)))' > "$tmp/answer.wat"
  wasm-as "$tmp/answer.wat" -o "$tmp/answer.wasm"
  test "$(wasmtime run --invoke answer "$tmp/answer.wasm")" = 42
fi
