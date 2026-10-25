module

public import Silmaril.Wasm.Binaryen.GrowOOMLiteralMode
public import Silmaril.Wasm.Binaryen.GrowOOMPass

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowOOMLiteral

open Execution.Core Numerics Validation Optimization

variable {H : Type}

/-- The widened family uses the shared Pass API. Existing zero-wrapper output
and all unsupported-module fallbacks are retained exactly. -/
def trapInsertionP (P : Profile) :
    Silmaril.Compile.PassAPI.Pass (Modes.contract .trapInsertion P (closedHost (H := H))) where
  run := optimize
  inv_run {m} hm := by
    unfold optimize
    split
    · exact ⟨_, by rw [lower_lift]; exact GrowOOM.module_ok _⟩
    · split
      · exact ⟨_, by rw [lower_lift]; exact module_ok _ _⟩
      · exact hm
  sound {m} _ := by
    change Modes.ExportCorrect .trapInsertion P closedHost m.lower (optimize m).lower
    unfold optimize
    split
    · rename_i a accepted
      rw [lower_lift, GrowOOM.recognize?_sound accepted]
      exact GrowOOM.exportCorrect a
    · split
      · rename_i p accepted
        rw [lower_lift, GrowWrapper.recognize?_sound accepted]
        exact exportCorrect p.address p.delta
      · exact Modes.ExportCorrect.refl _ _ _ _

@[simp] theorem optimize_zero_wrapper (a : AddrType) :
    optimize (BModule.lift (GrowWrapper.mod a 0 false)) = BModule.lift (GrowOOM.mod a) := by
  rw [optimize, lower_lift, GrowOOM.recognize?_complete]

theorem optimize_literal_wrapper (a : AddrType) (n : BitVec a.intType.width) (hn : n ≠ 0) :
    optimize (BModule.lift (GrowWrapper.mod a n false)) = BModule.lift (mod a n) := by
  cases a <;> simp_all [optimize, lower_lift, GrowOOM.recognize?, GrowWrapper.recognize?_complete]

theorem optimize_of_rejected {m : BModule} (h : GrowWrapper.recognize? m.lower = none) :
    optimize m = m := by simp [optimize, GrowOOM.recognize?, h]

end Silmaril.Wasm.Binaryen.GrowOOMLiteral
