module

public import Silmaril.Wasm.Binaryen.ArbitraryProfile
public import Silmaril.Wasm.Binaryen.Exe.UnusedBlocksProfile
public import Silmaril.Wasm.Binaryen.CodeFoldingProfile

@[expose] public section

/-! The unchanged unused-label, arbitrary-depth nested-block and common-tail
folding executables as composable shared passes at every numerical profile.
The only input invariant is module validity; their existing local guards remain.
-/

namespace Silmaril.Wasm.Binaryen.ArbitraryProfile

open Execution.Core Numerics

variable {H : Type}

/-- RemoveUnusedNames retains its existing eligible whole-wrapper fragment. -/
def removeUnusedNamesP (P : Profile) : EquivPass P (closedHost (H := H)) where
  run := removeUnusedNames
  inv_run hm := (Exe.removeUnusedNames_sound_profile P (H := H) hm).1
  sound hm := (Exe.removeUnusedNames_sound_profile P hm).2

/-- MergeBlocks retains its actual arbitrary-depth certified-site search. -/
def mergeBlocksP (P : Profile) : EquivPass P (closedHost (H := H)) where
  run := mergeBlocksAny
  inv_run hm := (Exe.mergeBlocks_sound_profile P (H := H) hm).1
  sound hm := (Exe.mergeBlocks_sound_profile P hm).2

/-- CodeFolding retains its common closed-void-tail applicability tests. -/
def codeFoldingP (P : Profile) : EquivPass P (closedHost (H := H)) where
  run := codeFolding
  inv_run hm := (CodeFolding.codeFolding_sound_profile P H hm).1
  sound hm := (CodeFolding.codeFolding_sound_profile P H hm).2

/-- The three existing transformations, in their default relative order. -/
def blockCleanupP (P : Profile) : EquivPass P (closedHost (H := H)) :=
  removeUnusedNamesP P * mergeBlocksP P * codeFoldingP P

def blockCleanup (m : BModule) : BModule :=
  codeFolding (mergeBlocksAny (removeUnusedNames m))

@[simp] theorem removeUnusedNamesP_run (P : Profile) :
    (removeUnusedNamesP (H := H) P).run = removeUnusedNames := rfl

@[simp] theorem mergeBlocksP_run (P : Profile) :
    (mergeBlocksP (H := H) P).run = mergeBlocksAny := rfl

@[simp] theorem codeFoldingP_run (P : Profile) :
    (codeFoldingP (H := H) P).run = codeFolding := rfl

@[simp] theorem blockCleanupP_run (P : Profile) :
    (blockCleanupP (H := H) P).run = blockCleanup := rfl

/-- Actual three-pass composition preserves all admission, initialization and
persistent-session observations at the same arbitrary numerical profile. -/
theorem blockCleanup_sound (P : Profile) {m : BModule} (hm : m.Ok) :
    (blockCleanup m).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H))
      (blockCleanup m).lower m.lower :=
  ⟨(blockCleanupP (H := H) P).inv_run hm, (blockCleanupP (H := H) P).sound hm⟩

/-- Every finite number of actual three-pass rounds has the same exact contract. -/
theorem blockCleanup_iterate_sound (P : Profile) (rounds : Nat) {m : BModule} (hm : m.Ok) :
    (blockCleanup^[rounds] m).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H))
      (blockCleanup^[rounds] m).lower m.lower := by
  have hrun := Silmaril.Compile.PassAPI.Pass.pow_run (blockCleanupP (H := H) P) rounds
  rw [blockCleanupP_run] at hrun
  have result : ((blockCleanupP (H := H) P ^ rounds).run m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((blockCleanupP (H := H) P ^ rounds).run m).lower m.lower :=
    ⟨(blockCleanupP (H := H) P ^ rounds).inv_run hm,
      (blockCleanupP (H := H) P ^ rounds).sound hm⟩
  rw [hrun] at result
  exact result

end Silmaril.Wasm.Binaryen.ArbitraryProfile
