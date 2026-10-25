module

public import Silmaril.Wasm.Binaryen.GrowWrapperMode

/-! # Executable recognition and mode-specific wrapper optimization

Recognize the complete no-import/no-start wrapper shape after lowering. This is
an intentionally small accepted family, with identity fallback elsewhere. Its
body may have any folded representation whose lowering is the same wrapper.
-/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowWrapper

open Execution.Core Numerics Validation MemoryGrowFailure

variable {H : Type}

/-- Successful recognition proves equality of the entire lowered module. -/
theorem recognize?_sound {m : Module} {p : Params} (h : recognize? m = some p) :
    m = mod p.address p.delta false := by
  unfold recognize? at h
  split at h
  · split at h
    · rename_i hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      cases h
      rfl
    · cases h
  · split at h
    · rename_i hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      cases h
      rfl
    · cases h
  · cases h

theorem recognize?_complete (a : AddrType) (n : BitVec a.intType.width) :
    recognize? (mod a n false) = some ⟨a, n⟩ := by
  cases a <;> with_unfolding_all rfl

/-- Modules with a start function are outside the accepted family. -/
theorem recognize?_reject_start (a : AddrType) (n : BitVec a.intType.width) :
    recognize? {mod a n false with start := some ⟨0⟩} = none := by
  cases a <;> rfl

/-- The recognizer checks the exported memory as part of the full module shape. -/
theorem recognize?_reject_missing_memory (a : AddrType) (n : BitVec a.intType.width) :
    recognize? {mod a n false with exports := [⟨"grow", .func ⟨0⟩⟩]} = none := by
  cases a <;> with_unfolding_all rfl

theorem optimize_of_rejected {m : BModule} (h : recognize? m.lower = none) :
    optimize m = m := by simp only [optimize, h]

/-- The mode-specific optimization is enabled only under feasible refinement. -/
def refinementP (nd : Bool := true) (r : RelaxedChoice := {}) :
    Silmaril.Compile.PassAPI.Pass
      (Modes.contract .refinement (Profile.spec nd r) (closedHost (H := H))) where
  run := optimize
  inv_run {m} hm := by
    unfold optimize
    split
    · rw [show (Modes.contract .refinement (Profile.spec nd r) (closedHost (H := H))).Inv
          (BModule.lift (mod _ _ true)) = (BModule.lift (mod _ _ true)).Ok from rfl]
      exact ⟨_, by rw [lower_lift]; exact module_ok _ _ true⟩
    · exact hm
  sound {m} _ := by
    change Modes.ExportCorrect .refinement (Profile.spec nd r) closedHost m.lower (optimize m).lower
    unfold optimize
    split
    · rename_i p hp
      rw [lower_lift, recognize?_sound hp]
      exact exportCorrect p.address p.delta nd r
    · exact Modes.ExportCorrect.refl _ _ _ _

@[simp] theorem optimize_wrapper (a : AddrType) (n : BitVec a.intType.width) :
    optimize (BModule.lift (mod a n false)) = BModule.lift (mod a n true) := by
  simp only [optimize, lower_lift, recognize?_complete]

/-- Exact mode leaves the input unchanged. Refinement and trap-insertion modes
may select failure, with the same executable identity fallback. -/
def modeP (mode : Optimization.Mode) (nd : Bool := true) (r : RelaxedChoice := {}) :
    Silmaril.Compile.PassAPI.Pass
      (Modes.contract mode (Profile.spec nd r) (closedHost (H := H))) :=
  match mode with
  | .equivalence => 1
  | .refinement => refinementP nd r
  | .trapInsertion => Silmaril.Compile.PassAPI.Pass.weaken
      (Modes.refinement_le_trapInsertion _ _) (refinementP nd r)

theorem modeP_equivalence_run (nd : Bool) (r : RelaxedChoice) :
    (modeP (H := H) .equivalence nd r).run = id := rfl

theorem modeP_refinement_run (nd : Bool) (r : RelaxedChoice) :
    (modeP (H := H) .refinement nd r).run = optimize := rfl

theorem modeP_trapInsertion_run (nd : Bool) (r : RelaxedChoice) :
    (modeP (H := H) .trapInsertion nd r).run = optimize := rfl

end Silmaril.Wasm.Binaryen.GrowWrapper
