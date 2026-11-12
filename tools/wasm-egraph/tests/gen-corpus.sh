#!/usr/bin/env bash
# Regenerate tests/wasm/auto/EGraph/Corpus.lean and print the benchmark table.
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
repo="$(cd "$here/../.." && pwd)"
cd "$repo"
cargo build --offline --release --quiet --manifest-path "$here/Cargo.toml"
"$here/target/release/wasm-egraph" bench tools/wasm-egraph/corpus/regression.sexp \
  --lean tests/wasm/auto/EGraph/Corpus.lean --module Corpus
