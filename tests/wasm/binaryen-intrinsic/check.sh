#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."
here=tests/wasm/binaryen-intrinsic
lake=${LAKE:-lake}
"$lake" build --wfail +Silmaril.Wasm.Binaryen.Intrinsic.Observations.Thms +Silmaril.Wasm.Binary.Core.Decode \
  +Silmaril.Wasm.Validation.Check.Validate
"$lake" env lean -DwarningAsError=true "$here/Observers.lean"

if [[ -z ${BINARYEN_BIN:-} ]]; then
  "$lake" env lean -DwarningAsError=true "$here/Regression.lean"
  exit
fi

assembler=$BINARYEN_BIN/wasm-as
runner=$BINARYEN_BIN/wasm-shell
[[ $("$assembler" --version) == *'133 (version_133)' ]]
[[ $("$runner" --version) == *'133 (version_133)' ]]
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
"$assembler" "$here/fixture.wat" -o "$work/fixture.wasm"
"$lake" env lean -DwarningAsError=true --run "$here/Regression.lean" "$work/fixture.wasm"
cat "$here/session-start.wast" "$here/fixture.wat" "$here/session-end.wast" > "$work/session.wast"
"$runner" "$work/session.wast"

sed -e 's/(call \$transform (local.get 0) (local.get 1))/(call $transform (local.get 1) (local.get 0))/' \
  "$here/fixture.wat" > "$work/bad.wat"
if "$assembler" "$work/bad.wat" -o "$work/bad.wasm" > "$work/bad.log" 2>&1; then
  echo 'Binaryen unexpectedly accepted swapped call operands' >&2
  exit 1
fi
rg -q 'call param types must match' "$work/bad.log"
echo 'Binaryen rejected the swapped call operands'
