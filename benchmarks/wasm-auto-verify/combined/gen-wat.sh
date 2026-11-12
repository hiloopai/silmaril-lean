#!/usr/bin/env bash
# Print the optimizer-run binaries of the combined benchmark as WAT (the module texts of the
# `pass` certificates, `wasm-check pass --wat`), with the pinned Binaryen wasm-opt
# version_123 (sha256 d66c6724c07334155720eb2def29c434dcaaf741ce859b4f7f389e22674f9c4a, see
# benchmarks/wasm-auto-verify/equiv/gen.sh). Records the sha256 of every source binary in
# wat/SOURCES; run.sh checks it before using the texts. Skips when the binary is absent.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root=$(cd "$here/../../.." && pwd)
W="${BINARYEN_WASM_OPT:-$HOME/.cache/silmaril-tools/binaryen-123/binaryen-version_123/bin/wasm-opt}"
if [[ ! -x $W ]]; then echo "gen-wat.sh: $W not found; skipping"; exit 0; fi
sum=$(sha256sum "$W" | cut -d' ' -f1)
if [[ $sum != d66c6724c07334155720eb2def29c434dcaaf741ce859b4f7f389e22674f9c4a ]]; then
  echo "gen-wat.sh: $W has sha256 $sum, not the pinned one; skipping"; exit 0
fi
C=$root/tools/wasm-egraph/corpus
: > "$here/wat/SOURCES"
for b in rand60 rand60.binaryen-O3; do
  "$W" "$C/$b.wasm" -S -o "$here/wat/$b.wat"
  echo "$(sha256sum "$C/$b.wasm" | cut -d' ' -f1)  $b.wasm" >> "$here/wat/SOURCES"
done
# The opt-in corpus has a multi-value function: Binaryen reads it only with the feature enabled
# (--all-features, which also prints every function's type use) and prints its result with its
# non-standard `tuple.make`, which the certificates read with `wat3b!` (Silmaril.Wasm.Auto2.Wat).
for b in opt-in opt-in.binaryen-O2 opt-in.peep; do
  "$W" --all-features "$C/$b.wasm" -S -o "$here/wat/$b.wat"
  echo "$(sha256sum "$C/$b.wasm" | cut -d' ' -f1)  $b.wasm" >> "$here/wat/SOURCES"
done
echo "gen-wat.sh: ok"
