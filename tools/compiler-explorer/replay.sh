#!/usr/bin/env bash
# Replay the kernel on the compiler explorer's evidence modules with the toolchain's `leanchecker`
# (`make compiler-explorer-check` runs it). Each named module's own declarations are re-added to an
# environment, through the kernel, on top of its imports as loaded from their .olean files; the
# imports are not replayed (`--fresh`, the whole closure with Mathlib, is not run). It is the same
# kernel as `lake build`, run again on the stored declarations, not an independent implementation.
set -euo pipefail
cd "$(dirname "$0")/../.."
LAKE="${LAKE:-lake}"
driver="tools/compiler-explorer/Replay.lean"
export LEAN_NUM_THREADS=1
modules=(
  CompilesToExamples.Explorer.C2C.Runs
  CompilesToExamples.Explorer.C2C.Elaborates
  CompilesToExamples.Straight.Proofs.Elaborates
  CompilesToExamples.Branch.Proofs.Elaborates
  Silmaril.Proofs.Compiler.CompilesTo.Sim.Compose
  Silmaril.Proofs.Compiler.Explorer.Basic
  Silmaril.Proofs.Compiler.Explorer.Det
  Silmaril.Compiler.Explorer.Decompiled.Thms
  Silmaril.Proofs.Project.Shapes.CompilesTo.Explorer
  CompilesToExamples.Explorer.Builds
  CompilesToExamples.Explorer.Code
  CompilesToExamples.Explorer.Decompiled
  CompilesToExamples.Explorer.Rows
  Silmaril.Proofs.Project.Shapes.CompilesTo.Translate
  Silmaril.Project.Shapes.C.Additive.Thms
  Silmaril.Proofs.Compiler.Explorer.Text
  Silmaril.Compiler.Explorer.Text.Thms
  CompilesToExamples.Explorer.TypeError
  Silmaril.Proofs.Compiler.C.Compact
  Silmaril.Proofs.Compiler.C.CompactBody
  Silmaril.Compiler.C.Compact.Thms
  CompilesToExamples.Explorer.Compact.Checks
  CompilesToExamples.Explorer.Compact.Core
)
# Each replay has its own environment. Bound concurrent processes to avoid multiplying
# Mathlib import memory by the host CPU count; keep a serial mode for small hosts.
jobs="${LEAN_REPLAY_JOBS:-4}"
if ! [[ "$jobs" =~ ^[1-9][0-9]*$ ]]; then
  echo "LEAN_REPLAY_JOBS must be a positive integer" >&2
  exit 1
fi
# Fail before launching any workers if discovery fails; never use process
# substitution here (its exit status would be lost).
selection=$(timeout 1200 env -u SILMARIL_REPLAY_MODULE SILMARIL_REPLAY_TARGETS="${modules[*]}" \
  "$LAKE" env lean -DwarningAsError=true "$driver")
if [ -z "$selection" ]; then
  echo "kernel replay selected no modules" >&2
  exit 1
fi
mapfile -t selected <<< "$selection"
pids=()
failed=0
wait_batch() {
  for pid in "${pids[@]}"; do
    if ! wait "$pid"; then failed=1; fi
  done
  pids=()
}
for m in "${selected[@]}"; do
  (
    start=$(date +%s)
    timeout 1200 env -u SILMARIL_REPLAY_TARGETS SILMARIL_REPLAY_MODULE="$m" \
      "$LAKE" env lean -DwarningAsError=true "$driver"
    echo "kernel replay $m: $(( $(date +%s) - start )) s"
  ) &
  pids+=("$!")
  if (( ${#pids[@]} >= jobs )); then wait_batch; fi
done
wait_batch
exit "$failed"
