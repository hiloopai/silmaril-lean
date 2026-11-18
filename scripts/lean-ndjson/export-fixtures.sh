#!/usr/bin/env bash
# Regenerate the Lean-NDJSON fixture tests/lean-ndjson/pa-derivations.ndjson with lean4export
# (docs/projects/formal-rows.md, "Lean-NDJSON"). The exporter is the lean4export that the pinned
# Mathlib dependency vendors (.lake/packages/mathlib/lean4export, format version 3.1.0), run with no
# options: no --export-unsafe, no --export-mdata, no --ignore-missing. It writes the named
# declarations and their transitive dependencies.
#   scripts/lean-ndjson/export-fixtures.sh [--check]
# With --check, export to a temporary file and fail if it differs from the committed fixture.
set -euo pipefail
cd "$(dirname "$0")/../.."
exporter_dir=.lake/packages/mathlib/lean4export
module=Silmaril.Logic.Consequence.Arithmetic.Derivation.Exported
decls=(
  Silmaril.Consequence.Arithmetic.ND.Exported.zeroAddZero
  Silmaril.Consequence.Arithmetic.ND.Exported.instAddZero
  Silmaril.Consequence.Arithmetic.ND.Exported.eqSymm
  Silmaril.Consequence.Arithmetic.ND.Exported.zeroAdd
  Silmaril.Consequence.Arithmetic.ND.Exported.wrongAxiom
  Silmaril.Consequence.Arithmetic.ND.Examples.zeroAdd
)
fixture=tests/lean-ndjson/pa-derivations.ndjson
(cd "$exporter_dir" && lake build lean4export >/dev/null)
lake build "$module" >/dev/null
out=$(mktemp)
trap 'rm -f "$out"' EXIT
lake env "$exporter_dir/.lake/build/bin/lean4export" "$module" -- "${decls[@]}" > "$out"
if [[ "${1:-}" == "--check" ]]; then
  if ! cmp -s "$out" "$fixture"; then
    echo "error: $fixture is not what lean4export writes now; run $0" >&2
    exit 1
  fi
  echo "lean-ndjson fixture: up to date ($(wc -l < "$fixture") records)"
else
  cp "$out" "$fixture"
  echo "wrote $fixture ($(wc -l < "$fixture") lines, $(wc -c < "$fixture") bytes)"
fi
