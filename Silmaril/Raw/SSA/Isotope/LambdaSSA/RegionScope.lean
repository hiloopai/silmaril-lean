module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Scope

/-! # Scope of arbitrary nested SSA regions -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {Φ : Type u}

/-- Value and label scopes are independent; a CFG extends the label scope for
its entry and every block, and each block binds its own argument. -/
def Scoped (labels vars : Nat) : Region Φ → Prop
  | .br label arg => label < labels ∧ arg.Scoped vars
  | .case discr left right => discr.Scoped vars ∧
      Scoped labels (vars + 1) left ∧ Scoped labels (vars + 1) right
  | .let₁ value body => value.Scoped vars ∧ Scoped labels (vars + 1) body
  | .let₂ value body => value.Scoped vars ∧ Scoped labels (vars + 2) body
  | .cfg entry count blocks => Scoped (count + labels) vars entry ∧
      ∀ i, Scoped (count + labels) (vars + 1) (blocks i)

instance scopedDecidable (labels vars : Nat) (r : Region Φ) : Decidable (Scoped labels vars r) :=
  match r with
  | .br label arg => inferInstanceAs (Decidable (label < labels ∧ arg.Scoped vars))
  | .case discr left right =>
    letI := scopedDecidable labels (vars + 1) left
    letI := scopedDecidable labels (vars + 1) right
    inferInstanceAs (Decidable (discr.Scoped vars ∧ _ ∧ _))
  | .let₁ value body =>
    letI := scopedDecidable labels (vars + 1) body
    inferInstanceAs (Decidable (value.Scoped vars ∧ _))
  | .let₂ value body =>
    letI := scopedDecidable labels (vars + 2) body
    inferInstanceAs (Decidable (value.Scoped vars ∧ _))
  | .cfg entry count blocks =>
    letI := scopedDecidable (count + labels) vars entry
    letI : ∀ i, Decidable (Scoped (count + labels) (vars + 1) (blocks i)) :=
      fun i => scopedDecidable (count + labels) (vars + 1) (blocks i)
    inferInstanceAs (Decidable (_ ∧ ∀ i, Scoped (count + labels) (vars + 1) (blocks i)))

variable {τ : Type v} [TypeFormers τ] [HasTy Φ τ]

/-- Exact typing bounds every value variable and every jump label, even under
nested mutually recursive CFG binders. -/
theorem HasType.scoped {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (h : HasType Γ r L) : Scoped L.length Γ.length r := by
  induction h with
  | br label arg =>
    obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp label
    exact ⟨inside, arg.scoped⟩
  | case arg _ _ left right => exact ⟨arg.scoped, left, right⟩
  | let₁ arg _ body | let₂ arg _ body => exact ⟨arg.scoped, body⟩
  | cfg R _ _ entry blocks =>
    constructor
    · simpa only [List.length_append, List.length_ofFn] using entry
    · intro i
      simpa only [List.length_append, List.length_ofFn, List.length_cons] using blocks i

end Silmaril.Isotope.LambdaSSA.Region
