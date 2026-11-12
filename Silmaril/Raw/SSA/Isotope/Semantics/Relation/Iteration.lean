module

public import Silmaril.Raw.SSA.Isotope.Semantics.Relation
public import Silmaril.Semantics.ElgotMonads.Thms

/-! # Finite relational iteration and powerset iteration

Both descriptions collect finite successful paths. Failure and divergence
contribute no successful outcome; this comparison does not identify their
operational behavior or impose fairness.
-/

@[expose] public section

universe u

namespace Silmaril.Isotope.Semantics.Relation

variable {A B : Type u}

theorem iterates_iff_runs {step : A → B ⊕ A → Prop} {f : A → SetM (B ⊕ A)}
    (h : ∀ a s, step a s ↔ s ∈ (f a).run) {a : A} {b : B} :
    Iterates step a b ↔ Elgot.Nondet.Runs f a b := by
  constructor
  · intro run
    induction run with
    | done hs => exact .done ((h _ _).mp hs)
    | more hs _ ih => exact .more ((h _ _).mp hs) ih
  · intro run
    induction run with
    | done hs => exact .done ((h _ _).mpr hs)
    | more hs _ ih => exact .more ((h _ _).mpr hs) ih

theorem iterates_iff_mem_iter {step : A → B ⊕ A → Prop} {f : A → SetM (B ⊕ A)}
    (h : ∀ a s, step a s ↔ s ∈ (f a).run) {a : A} {b : B} :
    Iterates step a b ↔ b ∈ (Elgot.iter f a).run :=
  iterates_iff_runs h

theorem Iterates.not_of_no_return {step : A → B ⊕ A → Prop}
    (h : ∀ a b, ¬ step a (.inl b)) {a : A} {b : B} : ¬ Iterates step a b := by
  intro run
  induction run with
  | done hs => exact h _ _ hs
  | more _ _ ih => exact ih

end Silmaril.Isotope.Semantics.Relation
