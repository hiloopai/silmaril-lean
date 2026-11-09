module

public import Silmaril.Project.Core.Defs

/-!
# Proofs of the value lemmas

The proofs behind `Silmaril.Project.Core.Thms`, which restates each theorem.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.Core

open Silmaril.Project

theorem equivalent_of_decide {S T : ArtifactType} {V : Type} [DecidableEq V]
    {F : Format S V} {G : Format T V} {a : S.Carrier} {b : T.Carrier}
    (h : (match F.parse a, G.parse b with
      | some u, some v => decide (u = v)
      | _, _ => false) = true) : Equivalent F G a b := by
  unfold Equivalent
  revert h
  cases F.parse a <;> cases G.parse b <;> simp
  exact fun h => h ▸ rfl

theorem bytes_roundtrip : bytes.RoundTrip := by
  rintro p hp v a ha
  cases hp
  cases ha
  rfl

variable {V : Type} {x y : Value V} {P : V → Prop}

theorem satisfies_of_any [DecidablePred P] (h : (x.parse.any fun v => decide (P v)) = true) :
    x.Satisfies P := by
  unfold Value.Satisfies
  cases hx : x.parse with
  | none => simp [hx] at h
  | some w => exact ⟨w, rfl, by simpa [hx] using h⟩

theorem agrees_of_decide [DecidableEq V]
    (h : (match x.parse, y.parse with
      | some a, some b => decide (a = b)
      | _, _ => false) = true) : x.Agrees y := by
  unfold Value.Agrees Equivalent
  change ∃ w, x.parse = some w ∧ y.parse = some w
  revert h
  cases x.parse <;> cases y.parse <;> simp
  exact fun h => h ▸ rfl

end Silmaril.Proofs.Project.Core
