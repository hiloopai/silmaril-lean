module

public import Silmaril.Wasm.Binaryen.ArbitraryProfileWithCoalesce
public import Silmaril.Wasm.Binaryen.ArbitraryProfileThreePasses
public import Silmaril.Wasm.Binaryen.Exe.AllFunctionCleanup
public import Silmaril.Wasm.Binaryen.Exe.DCESound

@[expose] public section

/-! # All fifteen default function transformations at every numerical profile

Every actual registered function stage is composed in registry order, followed
by RUME. Both the executable output profile guards and each transform's internal
filters/fallbacks remain active. Module validity is the only input invariant;
the same arbitrary numerical profile is used on both sides under a closed host.
-/

namespace Silmaril.Wasm.Binaryen.ArbitraryProfile

open Execution.Core Numerics

variable {H : Type}

/-- Retain the executable's exact output-profile guard around any proven pass. -/
def outputGuardedP {P : Profile} (pass : EquivPass P (closedHost (H := H))) :
    EquivPass P (closedHost (H := H)) where
  run := Exe.guarded pass.run
  inv_run hm := by
    unfold Exe.guarded
    split
    · exact pass.inv_run hm
    · exact hm
  sound hm := by
    unfold Exe.guarded
    split
    · exact pass.sound hm
    · exact Exe.exportEquiv_refl _

/-- The arbitrary-profile certificate for each existing registry transformation. -/
def functionTransformP (P : Profile) : Exe.FunctionStageId → EquivPass P (closedHost (H := H))
  | .dce => dceP P closedHost closedHost_codeParametric
  | .removeUnusedNames => removeUnusedNamesP P
  | .mergeBlocks => mergeBlocksP P
  | .vacuum => vacuumP P closedHost closedHost_codeParametric
  | .simplifyGlobals => simplifyGlobalsP P
  | .directize => directizeP P
  | .precompute => precomputeP P closedHost closedHost_codeParametric
  | .constBranch => constBranchCheckedP P
  | .constSelect => constSelectCheckedP P
  | .addChain => addChainCheckedP P
  | .codeFolding => codeFoldingP P
  | .coalesceLocals => coalesceLocalsP P
  | .removeUnusedBrs => invertGuardsCheckedP P
  | .optimizeInstructions => ifSwapCheckedP P
  | .simplifyLocals => teeDropP P closedHost closedHost_codeParametric

@[simp] theorem functionTransformP_run (P : Profile) (stage : Exe.FunctionStageId) :
    (functionTransformP (H := H) P stage).run = stage.transform := by
  cases stage <;> first | rfl | exact Exe.Dce.dceChecked_eq.symm

/-- The exact guarded registered stage, with no deterministic-profile premise. -/
def functionStageP (P : Profile) (stage : Exe.FunctionStageId) : EquivPass P (closedHost (H := H)) :=
  outputGuardedP (functionTransformP P stage)

@[simp] theorem functionStageP_run (P : Profile) (stage : Exe.FunctionStageId) :
    (functionStageP (H := H) P stage).run = stage.run := by
  change Exe.guarded (functionTransformP P stage).run = Exe.guarded stage.transform
  rw [functionTransformP_run]

def functionStagesP (P : Profile) : List Exe.FunctionStageId → EquivPass P (closedHost (H := H))
  | [] => 1
  | stage :: stages => functionStageP P stage * functionStagesP P stages

theorem functionStagesP_run (P : Profile) (stages : List Exe.FunctionStageId) (m : BModule) :
    (functionStagesP (H := H) P stages).run m = stages.foldl (fun m stage => stage.run m) m := by
  induction stages generalizing m with
  | nil => rfl
  | cons stage stages ih =>
    simp only [functionStagesP, Silmaril.Compile.PassAPI.Pass.mul_run,
      functionStageP_run, List.foldl_cons]
    exact ih _

/-- All fifteen registered guarded function stages and the existing guarded RUME. -/
def cleanupAllFunctionsP (P : Profile) : EquivPass P (closedHost (H := H)) :=
  functionStagesP P Exe.functionStageIds * outputGuardedP (rumeP P)

def cleanupAllFunctions (m : BModule) : BModule := Exe.profileCleanupAllFunctionRound m

@[simp] theorem cleanupAllFunctionsP_run (P : Profile) :
    (cleanupAllFunctionsP (H := H) P).run = cleanupAllFunctions := by
  funext m
  simp only [cleanupAllFunctionsP, Silmaril.Compile.PassAPI.Pass.mul_run,
    functionStagesP_run]
  rfl

/-- Every valid input has a valid, exactly export-equivalent result at the
same arbitrary numerical profile, retaining admission, initialization and sessions. -/
theorem cleanupAllFunctions_sound (P : Profile) {m : BModule} (hm : m.Ok) :
    (cleanupAllFunctions m).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H))
      (cleanupAllFunctions m).lower m.lower := by
  have result : ((cleanupAllFunctionsP (H := H) P).run m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((cleanupAllFunctionsP (H := H) P).run m).lower m.lower :=
    ⟨(cleanupAllFunctionsP (H := H) P).inv_run hm,
      (cleanupAllFunctionsP (H := H) P).sound hm⟩
  simpa only [cleanupAllFunctionsP_run] using result

/-- Any finite number of the actual guarded sixteen-stage rounds is sound. -/
theorem cleanupAllFunctions_iterate_sound (P : Profile) (rounds : Nat) {m : BModule} (hm : m.Ok) :
    (cleanupAllFunctions^[rounds] m).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H))
      (cleanupAllFunctions^[rounds] m).lower m.lower := by
  have hrun := Silmaril.Compile.PassAPI.Pass.pow_run (cleanupAllFunctionsP (H := H) P) rounds
  rw [cleanupAllFunctionsP_run] at hrun
  have result : ((cleanupAllFunctionsP (H := H) P ^ rounds).run m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((cleanupAllFunctionsP (H := H) P ^ rounds).run m).lower m.lower :=
    ⟨(cleanupAllFunctionsP (H := H) P ^ rounds).inv_run hm,
      (cleanupAllFunctionsP (H := H) P ^ rounds).sound hm⟩
  rw [hrun] at result
  exact result

end Silmaril.Wasm.Binaryen.ArbitraryProfile
