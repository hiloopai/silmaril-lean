module

public import Silmaril.Compile.PassAPI.Pass

@[expose] public section

/-! Proofs for the checked-pass constructors. These use raw checker arguments
so the public definitions can depend on them without an import cycle. -/

namespace Silmaril.Compile.PassAPI.Proofs.Checked

universe u
variable {X : Type u} {C : Contract X}

theorem checked_spec (transform : X → X) (check : X → X → Bool)
    (sound : ∀ {x y}, check x y = true → C.Inv x → C.Rel x y ∧ C.Inv y)
    {x : X} (hx : C.Inv x) :
    C.Inv (if check x (transform x) then transform x else x) ∧
      C.Rel x (if check x (transform x) then transform x else x) := by
  by_cases hc : check x (transform x) = true
  · simp only [hc, ite_true]
    exact ⟨(sound hc hx).2, (sound hc hx).1⟩
  · simp only [hc]
    exact ⟨hx, C.refl x⟩

theorem seq_sound (transform : X → X) (check₁ check₂ : X → X → Bool)
    (sound₁ : ∀ {x y}, check₁ x y = true → C.Inv x → C.Rel x y ∧ C.Inv y)
    (sound₂ : ∀ {x y}, check₂ x y = true → C.Inv x → C.Rel x y ∧ C.Inv y)
    {x z : X} (h : (check₁ x (transform x) && check₂ (transform x) z) = true)
    (hx : C.Inv x) : C.Rel x z ∧ C.Inv z := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨r₁, i₁⟩ := sound₁ h.1 hx
  obtain ⟨r₂, i₂⟩ := sound₂ h.2 i₁
  exact ⟨C.trans r₁ r₂, i₂⟩

theorem normalizer_sound [DecidableEq X] [DecidablePred C.Inv] (n : Pass C)
    (hsymm : ∀ {x y}, C.Inv x → C.Rel x y → C.Rel y x) {x y : X}
    (h : (decide (n.run x = n.run y) && decide (C.Inv y)) = true)
    (hx : C.Inv x) : C.Rel x y ∧ C.Inv y := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨he, hy⟩ := h
  refine ⟨C.trans (n.sound hx) ?_, hy⟩
  rw [he]
  exact hsymm hy (n.sound hy)

end Silmaril.Compile.PassAPI.Proofs.Checked
