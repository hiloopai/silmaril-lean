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
queued=${#selected[@]}
# The validated decimals have no leading zeros. Compare widths, then digits
# in ASCII order, so even a limit beyond Bash's integer range clamps safely.
if (( ${#jobs} > ${#queued} )) ||
  { (( ${#jobs} == ${#queued} )) && test "$jobs" \> "$queued"; }; then
  jobs=$queued
fi

# Discovery can return the longest replay last. Start it first and let xargs
# refill each slot as soon as its worker exits.
ordered=()
for m in "${selected[@]}"; do
  if [[ "$m" == CompilesToExamples.Explorer.C2C.Runs ]]; then
    ordered=("$m" "${ordered[@]}")
  else
    ordered+=("$m")
  fi
done
printf '%s\0' "${ordered[@]}" |
  xargs -0 -n 1 -P "$jobs" bash -c '
    lake=$1
    driver=$2
    m=$3
    start=$(date +%s)
    if timeout 1200 env -u SILMARIL_REPLAY_TARGETS SILMARIL_REPLAY_MODULE="$m" \
      "$lake" env lean -DwarningAsError=true "$driver"; then
      echo "kernel replay $m: $(( $(date +%s) - start )) s"
    else
      status=$?
      echo "kernel replay $m failed (exit $status)" >&2
      # A worker exit of 255 would make xargs abandon the remaining modules.
      exit 1
    fi
  ' replay "$LAKE" "$driver" || exit 1
