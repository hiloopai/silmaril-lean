module

public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.Basic

@[expose] public section

namespace Silmaril.Logic.Metatheory

universe u v w x

namespace RefinementTheory

variable (S : IndexedSyntax.{u, v})

/-- The least contextual preorder containing the primitive refinement rules. -/
inductive Closure (R : S.Relation) : S.Relation where
  | base {i} {a b : S.Term i} : R a b → Closure R a b
  | refl {i} (a : S.Term i) : Closure R a a
  | trans {i} {a b c : S.Term i} : Closure R a b → Closure R b c → Closure R a c
  | congr {i j} {a b : S.Term i} (c : S.Term i → S.Term j) :
      S.Context c → Closure R a b → Closure R (c a) (c b)

def generated (R : S.Relation) : RefinementTheory S where
  Rel := Closure S R
  refl := Closure.refl
  trans := Closure.trans
  congr := Closure.congr

variable {S}

/-- Soundness for a presented theory reduces to its primitive rules. -/
theorem generated_le_iff (R : S.Relation) (Q : RefinementTheory S) :
    generated S R ≤ Q ↔ ∀ {i} {a b : S.Term i}, R a b → Q.Rel a b := by
  constructor
  · intro h i a b hab
    exact h (Closure.base hab)
  · intro h i a b hab
    induction hab with
    | base hab => exact h hab
    | refl a => exact Q.refl a
    | trans _ _ ih₁ ih₂ => exact Q.trans ih₁ ih₂
    | congr c hc _ ih => exact Q.congr c hc ih

theorem generated_mono {R Q : S.Relation}
    (h : ∀ {i} {a b : S.Term i}, R a b → Q a b) : generated S R ≤ generated S Q :=
  (generated_le_iff R _).2 fun hab => Closure.base (h hab)

@[simp] theorem generated_rel (R : RefinementTheory S) : generated S R.Rel = R := by
  apply le_antisymm
  · exact (generated_le_iff R.Rel R).2 fun h => h
  · exact fun h => Closure.base h

/-- Translate a generated refinement by checking primitive rules and contexts. -/
theorem Closure.map {T : IndexedSyntax.{w, x}} {R : S.Relation} {Q : T.Relation}
    (f : S.Translation T) (hf : f.Contextual)
    (hbase : ∀ {i} {a b : S.Term i}, R a b → Q (f.term a) (f.term b))
    {i} {a b : S.Term i} (h : Closure S R a b) :
    Closure T Q (f.term a) (f.term b) := by
  induction h with
  | base h => exact Closure.base (hbase h)
  | refl a => exact Closure.refl (f.term a)
  | trans _ _ ih₁ ih₂ => exact Closure.trans ih₁ ih₂
  | congr c hc _ ih =>
    obtain ⟨d, hd, hfd⟩ := hf c hc
    rw [hfd, hfd]
    exact Closure.congr d hd ih

end RefinementTheory

namespace EquationalTheory

variable (S : IndexedSyntax.{u, v})

/-- The least contextual equivalence containing the primitive equations. -/
inductive Closure (R : S.Relation) : S.Relation where
  | base {i} {a b : S.Term i} : R a b → Closure R a b
  | refl {i} (a : S.Term i) : Closure R a a
  | symm {i} {a b : S.Term i} : Closure R a b → Closure R b a
  | trans {i} {a b c : S.Term i} : Closure R a b → Closure R b c → Closure R a c
  | congr {i j} {a b : S.Term i} (c : S.Term i → S.Term j) :
      S.Context c → Closure R a b → Closure R (c a) (c b)

def generated (R : S.Relation) : EquationalTheory S where
  Rel := Closure S R
  refl := Closure.refl
  trans := Closure.trans
  congr := Closure.congr
  symm := Closure.symm

variable {S}

theorem generated_le_iff (R : S.Relation) (Q : EquationalTheory S) :
    generated S R ≤ Q ↔ ∀ {i} {a b : S.Term i}, R a b → Q.Rel a b := by
  constructor
  · intro h i a b hab
    exact h (Closure.base hab)
  · intro h i a b hab
    induction hab with
    | base hab => exact h hab
    | refl a => exact Q.refl a
    | symm _ ih => exact Q.symm ih
    | trans _ _ ih₁ ih₂ => exact Q.trans ih₁ ih₂
    | congr c hc _ ih => exact Q.congr c hc ih

theorem generated_mono {R Q : S.Relation}
    (h : ∀ {i} {a b : S.Term i}, R a b → Q a b) : generated S R ≤ generated S Q :=
  (generated_le_iff R _).2 fun hab => Closure.base (h hab)

@[simp] theorem generated_rel (R : EquationalTheory S) : generated S R.Rel = R := by
  apply le_antisymm
  · exact (generated_le_iff R.Rel R).2 fun h => h
  · exact fun h => Closure.base h

theorem Closure.map {T : IndexedSyntax.{w, x}} {R : S.Relation} {Q : T.Relation}
    (f : S.Translation T) (hf : f.Contextual)
    (hbase : ∀ {i} {a b : S.Term i}, R a b → Q (f.term a) (f.term b))
    {i} {a b : S.Term i} (h : Closure S R a b) :
    Closure T Q (f.term a) (f.term b) := by
  induction h with
  | base h => exact Closure.base (hbase h)
  | refl a => exact Closure.refl (f.term a)
  | symm _ ih => exact Closure.symm ih
  | trans _ _ ih₁ ih₂ => exact Closure.trans ih₁ ih₂
  | congr c hc _ ih =>
    obtain ⟨d, hd, hfd⟩ := hf c hc
    rw [hfd, hfd]
    exact Closure.congr d hd ih

end EquationalTheory

end Silmaril.Logic.Metatheory
