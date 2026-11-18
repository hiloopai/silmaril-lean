module

public import Silmaril.Logic.HOLLight.Check.Defs
import Silmaril.Proofs.Logic.HOLLight.Check.Basic

/-!
# A HOL Light type checker: soundness and completeness

`typeOf?_eq_some_iff`: `t.typeOf? sig Γ = some A ↔ HasType sig Γ t A`. So the checker accepts
exactly the typed terms, at their unique type, and `typeOf?_eq_none_iff` says that `none` means the
term has no type at all.
-/

@[expose] public section

namespace Silmaril.Logic.HOLLight

theorem Ty.wf?_iff (ops : List Nat) (A : Ty) : A.wf? ops = true ↔ A.WellFormed ops :=
  Proofs.Logic.HOLLight.Check.wf?_iff ops A

/-- **The type checker is sound and complete.** -/
theorem Tm.typeOf?_eq_some_iff (sig : Signature) (Γ : List Ty) (t : Tm) (A : Ty) :
    t.typeOf? sig Γ = some A ↔ HasType sig Γ t A :=
  ⟨Proofs.Logic.HOLLight.Check.typeOf?_sound sig t Γ A, Proofs.Logic.HOLLight.Check.typeOf?_complete⟩

/-- **Type errors are exact**: the checker fails exactly on untypable terms. -/
theorem Tm.typeOf?_eq_none_iff (sig : Signature) (Γ : List Ty) (t : Tm) :
    t.typeOf? sig Γ = none ↔ ∀ A, ¬ HasType sig Γ t A := by
  constructor
  · intro h A hA; rw [(typeOf?_eq_some_iff sig Γ t A).2 hA] at h; cases h
  · intro h; cases e : t.typeOf? sig Γ with
    | none => rfl
    | some A => exact absurd ((typeOf?_eq_some_iff sig Γ t A).1 e) (h A)

end Silmaril.Logic.HOLLight
