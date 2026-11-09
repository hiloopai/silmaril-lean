module

public import Silmaril.Project.Shapes.Format.Defs

/-! # Standard problem shapes: formats and values (transfer lemmas)

The format shapes on a registered value are its generated obligations: `parses_iff`
(`X.parses`), `agree_iff` (`X.agrees.k`) and `satisfies_iff` (`silmaril problem … about X`).
-/

@[expose] public section

namespace Silmaril.Project.Shapes

variable {V : Type}

theorem parses_iff (X : Value V) : Parses X.format X.bytes ↔ X.Parses := Iff.rfl

theorem agree_iff (X Y : Value V) : Agree X.format Y.format X.bytes Y.bytes ↔ X.Agrees Y :=
  Iff.rfl

theorem satisfies_iff (X : Value V) (P : V → Prop) : Satisfies X P ↔ X.Satisfies P := Iff.rfl

/-- A value that satisfies a predicate parses. -/
theorem Satisfies.parses {X : Value V} {P : V → Prop} (h : Satisfies X P) :
    Parses X.format X.bytes := by
  obtain ⟨v, hv, _⟩ := h
  show (X.format.parse X.bytes).isSome = true
  rw [show X.format.parse X.bytes = X.parse from rfl, hv]; rfl

end Silmaril.Project.Shapes
