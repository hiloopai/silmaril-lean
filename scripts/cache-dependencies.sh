#!/usr/bin/env bash
# Thomas owns this nightly bridge. Delete it when CSLib supports Lean 4.37
# and restore the standard Mathlib cache command with the upstream pins.
set -euo pipefail
cd "$(dirname "$0")/.."
lake_bin=${LAKE:-lake}
"$lake_bin" env true
snapshot=$(git -C .lake/packages/mathlib rev-parse HEAD)
toolchain=$(cat lean-toolchain)
export LAKE_CONFIG="$PWD/.lake/packages/mathlib/.meta/lake-config.toml"
for package in mathlib:mathlib4 cslib:cslib batteries:batteries Qq:quote4 \
    aesop:aesop proofwidgets:ProofWidgets4 plausible:plausible \
    LeanSearchClient:LeanSearchClient importGraph:import-graph Cli:lean4-cli; do
    revision=$snapshot
    if [ "${package%%:*}" = cslib ]; then
        revision=$(git -C .lake/packages/cslib rev-parse HEAD)
    fi
    "$lake_bin" cache get --package="${package%%:*}" --rev="$revision" \
        --scope="$toolchain/${package#*:}"
done
