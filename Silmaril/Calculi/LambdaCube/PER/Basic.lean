module

public import Silmaril.Calculi.LambdaCube.PER.Combinatory
public import Silmaril.Encoding.Per

@[expose] public section

set_option autoImplicit true

/-! # Partial equivalence relations over a combinatory algebra

Types of the polymorphic corners are interpreted as PERs on the realizers of a
total combinatory algebra (Girard 1972; Troelstra; Longo–Moggi). The PER
fields are universe-polymorphic; on `Type` they are exactly
`Silmaril.IsPartialEquivalence` (`Silmaril.Encoding.Per`, `PER.isPartialEquivalence`).

* `PER.arrow`: the extensional exponential `f ~ g ↔ ∀ a ~ a', f a ~ g a'`;
* `PER.iInf`: intersection of an arbitrary family. Quantifying over `PER D`
  stays in `Prop`, so `∀` lands in the same universe: this is the impredicativity
  used here. `Reynolds.lean` states the assumptions behind the comparison
  with full-function-space set models;
* `PER.Quo`: the subquotient `{a | a ~ a}/~`, the "set" a PER denotes.
-/

namespace Silmaril.Calculi.LambdaCube.PERModel

/-- A partial equivalence relation on `D`. -/
structure PER (D : Type u) where
  rel : D → D → Prop
  symm' : ∀ ⦃a b⦄, rel a b → rel b a
  trans' : ∀ ⦃a b c⦄, rel a b → rel b c → rel a c

namespace PER

variable {D : Type u}

@[ext] theorem ext {A B : PER D} (h : ∀ a b, A.rel a b ↔ B.rel a b) : A = B := by
  cases A; cases B
  congr
  funext a b
  exact propext (h a b)

theorem symm (A : PER D) {a b : D} (h : A.rel a b) : A.rel b a := A.symm' h

theorem trans (A : PER D) {a b c : D} (h : A.rel a b) (k : A.rel b c) : A.rel a c :=
  A.trans' h k

/-- On `Type`, a PER is exactly Silmaril's `IsPartialEquivalence`. -/
theorem isPartialEquivalence {D : Type} (A : PER D) : IsPartialEquivalence A.rel :=
  ⟨A.symm', A.trans'⟩

/-- Every `IsPartialEquivalence` on a `Type` is a PER. -/
def ofIsPartialEquivalence {D : Type} {R : D → D → Prop} (h : IsPartialEquivalence R) :
    PER D :=
  ⟨R, h.symm, h.trans⟩

/-- Elements in the domain of the PER. -/
def Dom (A : PER D) (a : D) : Prop := A.rel a a

theorem dom_left (A : PER D) {a b : D} (h : A.rel a b) : A.Dom a := A.trans h (A.symm h)

/-- The empty PER. -/
def bot : PER D := ⟨fun _ _ => False, by intro _ _ h; exact h, by intro _ _ _ h _; exact h⟩

instance : Inhabited (PER D) := ⟨bot⟩

/-- The extensional arrow PER. -/
def arrow (M : CombAlg.{u}) (A B : PER M.D) : PER M.D where
  rel f g := ∀ a a', A.rel a a' → B.rel (M.app f a) (M.app g a')
  symm' := by
    intro f g h a a' ha
    exact B.symm (h a' a (A.symm ha))
  trans' := by
    intro f g k hfg hgk a a' ha
    exact B.trans (hfg a a' ha) (hgk a' a' (A.trans (A.symm ha) ha))

/-- Intersection of a family of PERs (interprets `∀`). -/
def iInf {ι : Sort v} (F : ι → PER D) : PER D where
  rel a b := ∀ i, (F i).rel a b
  symm' := by intro _ _ h i; exact (F i).symm (h i)
  trans' := by intro _ _ _ h k i; exact (F i).trans (h i) (k i)

theorem iInf_rel {ι : Sort v} (F : ι → PER D) (a b : D) :
    (iInf F).rel a b ↔ ∀ i, (F i).rel a b := Iff.rfl

/-- The setoid on the domain of a PER. -/
def domSetoid (A : PER D) : Setoid {a // A.Dom a} where
  r x y := A.rel x.1 y.1
  iseqv := ⟨fun x => x.2, fun h => A.symm h, fun h k => A.trans h k⟩

/-- The subquotient denoted by a PER. -/
def Quo (A : PER D) : Type u := Quotient A.domSetoid

end PER

end Silmaril.Calculi.LambdaCube.PERModel
