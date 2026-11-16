module

public import Silmaril.Logic.Consequence.Institution.Defs

/-!
# Consequence relative to a theory

A theory `T` (a set of sentences) turns a relation on sets of premises into a list-premise
consequence system, `Γ ⊢_T φ` when `T ∪ Γ ⊢ φ`. This is how PA, ZF and ZFC are consequence
systems over the language of arithmetic or of set theory. Derivability and semantic consequence
both take this form, and they stay separate:

* **Derivability from a theory.** `ER.theorySys E T` is `theoryOf E.Derives T`, for an
  entailment relation `E` (`Metatheory.ER`): `T ∪ Γ` derives `φ`.
* **Semantic consequence over the models of a theory.** `roomTheorySeq R T` is
  `theoryOf R.Entails T`: every model of `T` that satisfies all of `Γ` satisfies `φ`.

`ER.withTheory E T` is the entailment relation `E` with the axioms `T` added. Both systems are its
list reading (`ER.listSys`), so they satisfy identity, weakening and cut (`Thms`). Soundness of a
derivability relation with respect to a room (`Room.IsSound`) gives soundness relative to every
theory: `theoryOf D T ≤ roomTheorySeq R T` (`Thms`). With `T = ∅`, the systems are `ER.listSys` and
`roomSeq`.
-/

@[expose] public section

namespace Silmaril.Consequence

open Silmaril.Logic Silmaril.Logic.Institution

universe w m₁ m₂

/-- **`Γ ⊢_T φ`**: `D` relates `T ∪ Γ` (the members of `Γ`) to `φ`. -/
def theoryOf {S : Type w} (D : Set S → S → Prop) (T : Set S) : System (List S) S :=
  fun Γ φ => D (T ∪ {x | x ∈ Γ}) φ

/-- An entailment relation with the axioms `T` added: `Γ ⊢ φ` iff `T ∪ Γ ⊢ φ` in `E`. -/
def ER.withTheory (E : Metatheory.ER.{w}) (T : Set E.Sen) : Metatheory.ER.{w} where
  Sen := E.Sen
  Derives Γ φ := E.Derives (T ∪ Γ) φ
  refl φ := E.mono Set.subset_union_right (E.refl φ)
  mono h d := E.mono (Set.union_subset_union_right T h) d
  trans hΔ d := E.trans hΔ (by rwa [← Set.union_assoc] at d)

/-- **Derivability from a theory**: `T ∪ Γ ⊢ φ` in `E`. -/
def ER.theorySys (E : Metatheory.ER.{w}) (T : Set E.Sen) : System (List E.Sen) E.Sen :=
  theoryOf E.Derives T

/-- **Semantic consequence over the models of `T`**: every model of `T` and of all of `Γ`
satisfies `φ`. -/
def roomTheorySeq (R : Room.{w, m₁, m₂}) (T : Set R.Sen) : System (List R.Sen) R.Sen :=
  theoryOf R.Entails T

end Silmaril.Consequence
