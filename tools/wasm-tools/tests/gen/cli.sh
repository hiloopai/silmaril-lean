#!/usr/bin/env bash
# CLI parity of the gentool subcommands: run the same invocation against our binary and the
# pinned upstream wasm-tools 1.262.0 (by absolute path) and compare stdout, stderr and exit
# status. Each case is `cmd|stdin-file|args…`; stdout is compared byte for byte for help and
# errors, and only its exit status and stderr for generating runs (outputs differ by design).
#
#   tools/wasm-tools/tests/gen/cli.sh            (skips when a binary is missing)
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/pins.sh"
gt_require_upstream
gt_ours

work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
cd "$work"
printf 'seed bytes for smith 0123456789' > seed
"$GT_UPSTREAM" parse - -o a.wasm <<'WAT'
(module (func (export "f") (param i32) (result i32) local.get 0 i32.const 1 i32.add)
  (memory 1) (global (mut i32) (i32.const 3)))
WAT
printf '#!/bin/sh\nexit 1\n' > never.sh; chmod +x never.sh
printf '#!/bin/sh\nexit 0\n' > always.sh; chmod +x always.sh
printf '\0asm\1\0\0\0\1' > trunc.wasm
printf '(module (func (export "f") (param i32) (result i32) local.get 0 i32.const 1 i32.add))\n' > a.wat
printf '(module (func (export "f") (result i32) i32.const 1' > bad.wat
"$GT_UPSTREAM" parse - -o imp.wasm <<'WAT'
(module (import "env" "f" (func (param i32) (result i32))) (import "env" "g" (global (mut i64)))
  (import "env" "h" (func (param f32 f64))) (import "env" "m" (memory 1)))
WAT

pass=0; fail=0
# compare: full (stdout+stderr+status), status (stderr+status) or exit (status only: the
# message is the WAT parser's, which differs)
check() {
  local mode=$1; shift
  local stdin=$1; shift
  "$GT_UPSTREAM" "$@" <"$stdin" >u.out 2>u.err; local us=$?
  "$GT_OURS" "$@" <"$stdin" >o.out 2>o.err; local os=$?
  local ok=1
  [[ $us == "$os" ]] || ok=0
  if [[ $mode != exit ]]; then cmp -s u.err o.err || ok=0; fi
  if [[ $mode == full ]]; then cmp -s u.out o.out || ok=0; fi
  if [[ $ok == 1 ]]; then pass=$((pass+1)); else
    fail=$((fail+1)); echo "DIFF ($mode): $* [upstream $us, ours $os]"
    diff u.err o.err | head -5; [[ $mode == full ]] && diff u.out o.out | head -5
  fi
}

for c in smith mutate shrink wit-smith; do
  check full /dev/null "$c" -h
  check full /dev/null "$c" --help
done
# smith: usage errors (clap's messages, status 2)
for a in "--bogus" "-q" "-tq" "a b" "-t -t" "--wat=1" "--max-funcs=-1" "--max-funcs abc" \
  "--max-funcs 99999999999999999999" "--max-funcs 3 --max-funcs 4" "--fuel x" "--fuel=-1" \
  "--fuel 4294967296" "--fuel -1" "--fuel -t" "--max-funcs" "--simd-enabled x" "--simd-enabled" \
  "--min-uleb-size 256" "--color bad" "-o" "-o -t" "--max-type-size 4294967296" \
  "--allowed-instructions bogus" "--allowed-instructions numeric,bogus" \
  "--allowed-instructions NUMERIC,Control,xyz" "--allowed-instructions numeric --allowed-instructions control" \
  "--disallow-traps maybe" "--generate-custom-sections"; do
  # shellcheck disable=SC2086
  check full seed smith $a
done
check full /dev/null smith /nonexistent
check full seed smith --available-imports /nonexistent
check exit seed smith --available-imports seed
check full /dev/null smith /tmp
# smith --config (JSON): read and decode errors are `failed to … json config: PATH` (status 1);
# the cause is serde's, which names the position, so only status and the first line agree
printf '{"max-funcs": 2, "simd-enabled": false}' > c-ok.json
printf '{"allowed-instructions": 1024, "max-funcs": null, "min-uleb-size": 4}' > c-kinds.json
printf '{"bogus": 1}' > c-unknown.json
printf '{"max-funcs": "x"}' > c-type.json
printf '[]' > c-arr.json
check full seed smith -c /nonexistent.json
for f in c-unknown.json c-type.json c-arr.json; do check exit seed smith -c "$f"; done
check status seed smith -c c-ok.json -t
check status seed smith -c c-kinds.json -o k.wasm
check status seed smith --config c-ok.json --max-funcs 4 -o k.wasm
# smith --exports / --module-shape (outputs differ by design; status and stderr agree)
"$GT_UPSTREAM" parse - -o ex.wasm <<'WAT'
(module (func (export "foo") (param i32) (result i64) unreachable)
  (global (export "bar") f32 f32.const 0) (memory (export "baz") 1 10)
  (table (export "qux") 5 10 externref) (tag (export "quux") (param f32)))
WAT
"$GT_UPSTREAM" parse - -o shape.wasm <<'WAT'
(module (import "env" "ping" (func (param i32))) (import "env" "memory" (memory 1))
  (import "env" "g" (global (mut i64))) (func (export "foo") (param i32) (result i32) unreachable)
  (global (export "bar") i32 i32.const 0))
WAT
check status seed smith --exports ex.wasm -o e.wasm
check status seed smith --module-shape shape.wasm -o s.wasm
check status seed smith --min-uleb-size 5 -o u.wasm
# smith: generating runs (status and stderr)
for a in "" "-t" "-o out.wasm" "--max-funcs 0" "--multi-value-enabled false -t" \
  "--allow-floats false" "--reference-types-enabled false --max-memories 0" "-vvv -t" "-- seed" "--max-funcs +5 -t" \
  "--ensure-termination -t" "--disallow-traps true -t" "--allowed-instructions numeric,control -t" \
  "--allowed-instructions NUMERIC_NON_FLOAT,variable,memory_non_float -o g.wasm" \
  "--generate-custom-sections true -o c.wasm" "--generate-custom-sections true -t" \
  "--max-memories 4 --max-tables 4 -t" "--simd-enabled false --tail-call-enabled false -t" \
  "--available-imports a.wasm -t" "--available-imports imp.wasm -o i.wasm"; do
  # shellcheck disable=SC2086
  check status seed smith $a
done
# wit-smith: usage errors, read errors, generating runs
for a in "--bogus" "--max-packages x" "--max-packages" "--async x" "a b" "--max-type-size=-1" \
  "--max-world-items 18446744073709551616" "--async --async" "--color bad"; do
  # shellcheck disable=SC2086
  check full seed wit-smith $a
done
check full /dev/null wit-smith /nonexistent
for a in "" "-o w.wasm" "-t" "--async --futures --streams -t" "--arbitrary-config -o w.wasm" \
  "--world-include --fixed-length-lists -o w.wasm" "--max-pkg-items 1 --max-interface-items 0 -t"; do
  # shellcheck disable=SC2086
  check status seed wit-smith $a
done
# mutate
for a in "--bogus" "-s x" "-s 18446744073709551616" "--fuel x" "--seed" "a b"; do
  # shellcheck disable=SC2086
  check full /dev/null mutate $a
done
check full /dev/null mutate /nonexistent
check full /dev/null mutate trunc.wasm
check full /dev/null mutate a.wasm --preserve-semantics --reduce
check status /dev/null mutate a.wasm -s 3 -o m.wasm
# mutate: text input (read as upstream does) and malformed text
check status /dev/null mutate a.wat -s 3 -o m.wasm
check status /dev/null mutate a.wat -s 5 --preserve-semantics -o p.wasm
check exit /dev/null mutate bad.wat
# shrink
check full /dev/null shrink
check full /dev/null shrink ./missing.sh a.wasm
check full /dev/null shrink ./never.sh a.wasm -o x.wasm
check full /dev/null shrink ./always.sh a.wasm -o x.wasm
check full /dev/null shrink ./never.sh /nonexistent
check full /dev/null shrink --attempts 4294967296 ./never.sh a.wasm
check full /dev/null shrink -a x ./never.sh a.wasm
check full /dev/null shrink ./never.sh a.wasm extra
check full /dev/null shrink ./never.sh a.wat -o x.wasm

echo "cli parity: $pass passed, $fail differ"
[[ $fail == 0 ]]
