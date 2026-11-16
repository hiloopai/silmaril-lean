module

public import Silmaril.Logic.Consequence.Theory.Defs
public import Silmaril.Logic.Consequence.Institution.Thms

/-!
# Consequence relative to a theory: laws

* `theorySys_eq_listSys`, `roomTheorySeq_eq`: both systems are the list reading of an
  entailment relation (`ER.withTheory`), so they are closed under identity, weakening and cut
  (`theorySys_closed`, `roomTheorySeq_closed`).
* `theoryOf_empty`, `theorySys_empty`, `roomTheorySeq_empty`: the empty theory gives
  `ER.listSys` and `roomSeq`.
* `theoryOf_mono_theory`: a monotone relation gives more consequences from a larger theory.
* `theoryOf_le_of_sound`, `theorySys_le_roomTheorySeq`: a derivability relation that is sound
  for a room is sound relative to every theory.
-/

@[expose] public section

namespace Silmaril.Consequence

open Silmaril.Logic Silmaril.Logic.Institution

universe w m₁ m₂

theorem theorySys_eq_listSys (E : Metatheory.ER.{w}) (T : Set E.Sen) :
    ER.theorySys E T = ER.listSys (ER.withTheory E T) := rfl

theorem roomTheorySeq_eq (R : Room.{w, m₁, m₂}) (T : Set R.Sen) :
    roomTheorySeq R T = ER.theorySys R.semanticER T := rfl

/-- Derivability from a theory satisfies identity, weakening and cut. -/
theorem theorySys_closed (E : Metatheory.ER.{w}) (T : Set E.Sen) :
    Structural.Closed Structural.tarskiRules (ER.theorySys E T) :=
  listSys_closed (ER.withTheory E T)

/-- Semantic consequence over the models of a theory satisfies identity, weakening and cut. -/
theorem roomTheorySeq_closed (R : Room.{w, m₁, m₂}) (T : Set R.Sen) :
    Structural.Closed Structural.tarskiRules (roomTheorySeq R T) :=
  theorySys_closed R.semanticER T

theorem theoryOf_empty {S : Type w} (D : Set S → S → Prop) :
    theoryOf D ∅ = fun Γ φ => D {x | x ∈ Γ} φ := by
  funext Γ φ; simp [theoryOf]

theorem theorySys_empty (E : Metatheory.ER.{w}) : ER.theorySys E ∅ = ER.listSys E :=
  theoryOf_empty E.Derives

theorem roomTheorySeq_empty (R : Room.{w, m₁, m₂}) : roomTheorySeq R ∅ = roomSeq R := by
  rw [roomTheorySeq, theoryOf_empty]; funext Γ φ; exact propext (roomSeq_iff_entails R Γ φ).symm

/-- A larger theory has more consequences, for a monotone relation. -/
theorem theoryOf_mono_theory {S : Type w} {D : Set S → S → Prop}
    (hD : ∀ {Γ Γ' φ}, Γ ⊆ Γ' → D Γ φ → D Γ' φ) {T T' : Set S} (h : T ⊆ T') :
    theoryOf D T ≤ theoryOf D T' :=
  fun _ _ d => hD (Set.union_subset_union_left _ h) d

theorem theorySys_mono_theory (E : Metatheory.ER.{w}) {T T' : Set E.Sen} (h : T ⊆ T') :
    ER.theorySys E T ≤ ER.theorySys E T' :=
  theoryOf_mono_theory (D := E.Derives) (fun h d => E.mono h d) h

/-- **Soundness relative to a theory.** If `D` is sound for `R`, then `Γ ⊢_T φ` implies that
every model of `T` and of `Γ` satisfies `φ`. -/
theorem theoryOf_le_of_sound {R : Room.{w, m₁, m₂}} {D : Set R.Sen → R.Sen → Prop}
    (h : R.IsSound D) (T : Set R.Sen) : theoryOf D T ≤ roomTheorySeq R T :=
  fun _ φ d => h _ φ d

/-- `theoryOf_le_of_sound` for a sound logic, at a signature. -/
theorem theorySys_le_roomTheorySeq {Sign : Type*} [CategoryTheory.Category Sign]
    {L : Metatheory.LogicalSystem.{_, _, w, m₁, m₂} Sign} (h : L.Sound) (S : Sign)
    (T : Set (L.I.obj S).Sen) : ER.theorySys (L.er S) T ≤ roomTheorySeq (L.I.obj S) T :=
  theoryOf_le_of_sound (h S) T

end Silmaril.Consequence
