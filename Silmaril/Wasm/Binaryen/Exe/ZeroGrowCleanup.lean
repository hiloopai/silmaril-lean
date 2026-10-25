module

public import Silmaril.Wasm.Binaryen.Exe.SelectedCleanup
public import Silmaril.Wasm.Binaryen.GrowZeroSuccessRuntime

@[expose] public section

/-! # Explicit selection of successful zero growth

This separate policy path leaves every existing options type and byte runner
unchanged. It accepts only refinement or trap-insertion mode and uses the same
exact cleanup before selecting a successful execution of the completely
recognized zero-growth fatal-OOM wrapper. Other shapes retain the cleanup result.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Optimization

/-- This policy chooses success, so it cannot also request failure selection
or insertion of the fatal-OOM guard. Checks run before reading any input file. -/
def zeroGrowOptionsCheck (options : TrapGrowOptions) : Except String Unit := do
  options.check
  if options.base.mode == .equivalence then
    .error "zero-growth success selection requires refinement or trap-insertion mode"
  else if options.base.selectGrowthFailure || options.trapGrowthFailure then
    .error "zero-growth success selection cannot be combined with another growth policy"
  else
    .ok ()

/-- Compose an exact cleanup with the explicit success selector. The pure byte
certificate is separate; IO and native compilation remain outside it. -/
def optimizeZeroGrowBytesUsing
    (cleanup : Nat → ByteArray → Except String ProfileCleanupArtifact)
    (options : TrapGrowOptions) (input : ByteArray) :
    Except String ProfileCleanupArtifact := do
  zeroGrowOptionsCheck options
  let clean ← cleanup options.base.rounds input
  let result := (GrowZeroSuccess.optimize (checkedLift clean.result).1).lower
  let bytes ← encodeModule? result
  pure ⟨clean.source, result, ⟨bytes.toArray⟩⟩

/-- The actual ordered selected pipeline, followed by success selection. -/
def optimizeSelectedZeroGrowBytes (stages : List CleanupStage)
    (options : TrapGrowOptions) (input : ByteArray) :
    Except String ProfileCleanupArtifact :=
  optimizeZeroGrowBytesUsing (cleanupSelectedBytes stages) options input

end Silmaril.Wasm.Binaryen.Exe
