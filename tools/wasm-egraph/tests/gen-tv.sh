#!/usr/bin/env bash
# Regenerate the pinned optimizer runs under tools/wasm-egraph/corpus/ and the Lean modules
# tests/wasm/auto/EGraph/Tv{Binaryen,Silmaril,Random}.lean.
#
# Optimizers (skipped with a message when absent):
#   Binaryen wasm-opt version_123, pinned with its SHA-256 in tools/wasm-tools/tests/pins.sh
#   (install it with tools/wasm-tools/tests/fetch-pins.sh binaryen; $BINARYEN_WASM_OPT overrides
#   the path, the hash is checked either way);
#   wasm-opt: .lake/build/bin/wasm-opt (lake target wasm-opt; $SIL_WASM_OPT
#   overrides).
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
repo="$(cd "$here/../.." && pwd)"
cd "$repo"
cargo build --offline --release --quiet --manifest-path "$here/Cargo.toml"
B="$here/target/release/wasm-egraph"
C=tools/wasm-egraph/corpus
W_OVERRIDE="${BINARYEN_WASM_OPT:-}"
# shellcheck source=../../wasm-tools/tests/pins.sh
source "$repo/tools/wasm-tools/tests/pins.sh"
W="${W_OVERRIDE:-$BINARYEN_WASM_OPT}"
M="${SIL_WASM_OPT:-$repo/.lake/build/bin/wasm-opt}"
"$B" emit-wasm $C/regression.sexp $C/opt-in.wasm
"$B" gen-random 60 7 $C/rand60.wasm
if [[ -x $W ]] && [[ $(wt_sha256 "$W") == "$BINARYEN_WASM_OPT_SHA256" ]]; then
  "$W" --enable-multivalue $C/opt-in.wasm -O2 -o $C/opt-in.binaryen-O2.wasm
  "$W" $C/rand60.wasm -O3 -o $C/rand60.binaryen-O3.wasm
else
  echo "gen-tv: Binaryen wasm-opt (SHA-256 $BINARYEN_WASM_OPT_SHA256) not found at $W; keeping the pinned outputs"
fi
if [[ -x $M ]]; then
  "$M" $C/opt-in.wasm --neutral-ops --eqz-pair --rounds 2 -o $C/opt-in.peep.wasm
else
  echo "gen-tv: wasm-opt not found at $M; keeping the pinned output"
fi
"$B" tv $C/opt-in.wasm $C/opt-in.binaryen-O2.wasm --names $C/regression.sexp \
  --lean tests/wasm/auto/EGraph/TvBinaryen.lean --module TvBinaryen || true
"$B" tv $C/opt-in.wasm $C/opt-in.peep.wasm --names $C/regression.sexp \
  --lean tests/wasm/auto/EGraph/TvPeep.lean --module TvPeep || true
"$B" tv $C/rand60.wasm $C/rand60.binaryen-O3.wasm \
  --lean tests/wasm/auto/EGraph/TvRandom.lean --module TvRandom || true
