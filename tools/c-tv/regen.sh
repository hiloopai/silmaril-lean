#!/usr/bin/env bash
# Regenerate examples/compiles-to/* and the generated Lean modules from the saved probe outputs.
# Pass --probe to rerun the Lean probe (`lake env lean`) instead.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
cd "$root"
cargo build --release --locked --quiet --manifest-path tools/c-tv/Cargo.toml
c_tv=${CARGO_TARGET_DIR:-tools/c-tv/target}/release/c-tv
# The probe module the generated scratch modules import (`--probe` only).
[ "${1:-}" = --probe ] && lake build Silmaril.Project.CompilesTo.Probe.Defs
for ex in straight branch loop; do
  src=examples/compiles-to/$ex/$ex.c
  if [ "${1:-}" = --probe ]; then
    "$c_tv" gen --src "$src" --name "$ex" --core-probe "lake env lean {file}"
  else
    "$c_tv" gen --src "$src" --name "$ex" --core "examples/compiles-to/$ex/core-probe.txt"
  fi
done
# The rows read the C sources and the objects through the artifact registry
# (silmaril/artifacts.toml). Register a new one with
#   scripts/sil project artifacts add PATH --name NAME
# (`make project-tool` builds it), under the name `source_artifact` or `object_artifact` in
# src/emit.rs gives it.
