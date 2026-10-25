module

public import Silmaril.Wasm.Binaryen.Profile

@[expose] public section

/-! Constant expressions in segment offsets. The independent Core validator checks
stack types, global immutability and indices; this only bounds the executable
profile. Keep `profileData` unchanged for RUME and Directize's simulations. -/

namespace Silmaril.Wasm.Binaryen

/-- Integer constant expressions, including Core's extended-const arithmetic. -/
def gcOffset (off : Expr) : Bool := off.all fun i => match i with
  | .intConst .. | .globalGet _ => true
  | .intBinOp _ .add | .intBinOp _ .sub | .intBinOp _ .mul => true
  | _ => false

/-- Data segments with integer constant-expression offsets of either width. -/
def gcData (d : Data) : Bool :=
  decide (d.bytes.size < 2 ^ 32) && match d.mode with
    | .passive => true
    | .active _ off => gcOffset off

theorem gcData_of_profile {d : Data} (h : profileData d = true) : gcData d = true := by
  simp only [profileData, gcData, Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  cases hm : d.mode with
  | passive => simp
  | active x off =>
    have ho : profileOffset off = true := by simpa [hm] using h.2
    obtain ⟨c, rfl⟩ := profileOffset_sound ho
    simp [gcOffset]

end Silmaril.Wasm.Binaryen
