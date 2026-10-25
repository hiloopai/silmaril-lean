module

public import Silmaril.Wasm.Binaryen.Profile
public import Silmaril.Wasm.Validation.Instructions.Properties

@[expose] public section

namespace Silmaril.Wasm.Binaryen.RenTyping

open Validation

/-- Vector instructions have no function or global indices, and their typing
does not depend on the renamed context fields. -/
theorem vector_ren {C : Context} {i : Instr} {it : InstrType}
    (ρ : Ren) (F : List DefType) (G : List CGlobalType) (R : List Nat)
    (h : VectorInstrOk C i it) :
    VectorInstrOk { C with funcs := F, globals := G, refs := R } i it ∧ ρ.instr i = i := by
  cases h <;> exact ⟨by constructor <;> assumption, by simp [Ren.instr]⟩

/-- The scalar profile's former vector exclusion cannot be retained for this slice. -/
theorem vector_exclusion_counterexample (C : Context) :
    ¬ (∀ (i : Instr) (it : InstrType), VectorInstrOk C i it → instrInProfile i → False) := by
  intro h
  exact h _ _ (.vecSplat (.int .i32x4)) (by simp [instrInProfile, profileInstr])

end Silmaril.Wasm.Binaryen.RenTyping
