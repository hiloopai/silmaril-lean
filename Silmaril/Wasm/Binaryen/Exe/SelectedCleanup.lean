module

public import Silmaril.Wasm.Binaryen.Exe.AllFunctionBytes

@[expose] public section

/-! # Explicitly selected guarded optimizer stages

The selection is an ordered list, including repetitions and the empty list.
Every identifier has an arbitrary-profile certificate in `SelectedCleanupSound`.
The byte frontend uses validity-only stages, retaining their internal checks
without imposing the legacy whole-module output profile or unrelated inliner
type-section wrapper. The older guarded run remains available. Runtime imports
remain independent of proof packages. These are restricted algorithms, not
upstream pass-algorithm parity.
-/

namespace Silmaril.Wasm.Binaryen.Exe

inductive CleanupStage where
  | function (stage : FunctionStageId)
  | rume
  | inlining
  deriving DecidableEq, Repr

def CleanupStage.run : CleanupStage → BModule → BModule
  | .function stage => stage.run
  | .rume => rumeStage.2
  | .inlining => (inlineStage inlineBudget).2

/-- Every selected transformation preserves validity on every valid module.
Internal applicability checks remain; the legacy whole-module output-profile
guard and inliner's type-section wrapper are omitted. The inliner uses the same
callee search, eligibility, size heuristic and finite-fuel loop. RUME retains its
base-profile, imported-global and numeric-signature checks. -/
def CleanupStage.runValid : CleanupStage → BModule → BModule
  | .function stage => stage.transform
  | .rume => Binaryen.rume
  | .inlining => Inl.inlineSmall inlineBudget inlineFuel

def CleanupStage.name : CleanupStage → String
  | .function stage => stage.name
  | .rume => "remove-unused-module-elements"
  | .inlining => "inlining"

/-- Run exactly the requested stages, in the requested order. -/
def cleanupSelectedRound (stages : List CleanupStage) (m : BModule) : BModule :=
  stages.foldl (fun m stage => stage.run m) m

/-- Run the selected stages with only their proved validity input invariant.
An unrelated out-of-profile module feature does not suppress a local rewrite. -/
def cleanupSelectedValidRound (stages : List CleanupStage) (m : BModule) : BModule :=
  stages.foldl (fun m stage => stage.runValid m) m

def cleanupSelectedBytes (stages : List CleanupStage) (rounds : Nat) (input : ByteArray) :
    Except String ProfileCleanupArtifact :=
  cleanupTransformBytes ((cleanupSelectedValidRound stages)^[rounds]) input

/-- The selected exact pipeline composes with the existing checked policy
rewrites. Their mode checks, supported wrappers and fallbacks are unchanged. -/
def optimizeSelectedTrapGrowBytes (stages : List CleanupStage) (options : TrapGrowOptions)
    (input : ByteArray) : Except String ProfileCleanupArtifact :=
  optimizeTrapGrowBytesUsing (cleanupSelectedBytes stages) options input

end Silmaril.Wasm.Binaryen.Exe
