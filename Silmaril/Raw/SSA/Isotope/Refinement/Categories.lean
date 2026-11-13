module

public import Silmaril.Raw.SSA.Isotope.Refinement.Theory
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Quotient
public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.Category

@[expose] public section
noncomputable section

/-! # Contextual categories for the written theories

A designated context is a constructor expression in one typed hole.  The
constructor operations carry all quantity splits and fragment permissions;
contextual closure therefore cannot invent an inadmissible use of a resource.
The native closed-theory category additionally retains conditional uniformity.
-/

namespace Silmaril.Isotope.Refinement

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel CategoryTheory Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel

universe u v w
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

/-- Algebraic contexts made from the actual quantitatively legal operations. -/
inductive TypedContext (F : Fragment) : {i j : Models.TypingIndex τ} →
    (Models.Carrier Φ ε F i → Models.Carrier Φ ε F j) → Prop
  | hole {i : Models.TypingIndex τ} : TypedContext F (i := i) id
  | constant {i j : Models.TypingIndex τ} (a : Models.Carrier Φ ε F j) :
      TypedContext F (i := i) (fun _ => a)
  | operation {i j : Models.TypingIndex τ} (o : Models.Operation (Φ := Φ) F j)
      (args : (k : Fin o.arity) → Models.Carrier Φ ε F i → Models.Carrier Φ ε F (o.argSort k))
      (contexts : ∀ k, TypedContext F (args k)) :
      TypedContext F (fun a => Models.syntaxOp o (fun k => args k a))

/-- The quantitative context and result type remain part of every sort. -/
def typedSyntax (Φ : Type v) [HasTy Φ τ] (ε : Type w) [EffectSystem ε] [HasEff Φ ε]
    (F : Fragment) : IndexedSyntax where
  Index := Models.TypingIndex τ
  Term := Models.Carrier Φ ε F
  Context := TypedContext F

/-- Operation compatibility is sufficient for all designated contexts. -/
theorem TypedContext.compatible {F : Fragment}
    (R : CompatiblePreorder (Models.syntaxAlgebra (τ := τ) Φ ε F))
    {i j : Models.TypingIndex τ} {c : Models.Carrier Φ ε F i → Models.Carrier Φ ε F j}
    (hc : TypedContext F c) {a b : Models.Carrier Φ ε F i} (h : R.Rel a b) :
    R.Rel (c a) (c b) := by
  induction hc with
  | hole => exact h
  | constant a => exact R.refl a
  | operation o args _ ih => exact R.compatible o _ _ (fun k => ih k)

/-- A native closed theory determines a compatible preorder on typing data. -/
def Theory.precongruence {F : Fragment} (T : Theory (τ := τ) (Φ := Φ) (ε := ε) F) :
    CompatiblePreorder (Models.syntaxAlgebra (τ := τ) Φ ε F) where
  Rel {i} a b := T.rel i.context a.1 b.1 i.result
  refl a := T.closed (.refl ⟨a.2⟩)
  trans h k := T.closed (.trans (.base h (T.formed h).1 (T.formed h).2)
    (.base k (T.formed k).1 (T.formed k).2))
  compatible o a b h := T.closed ((Models.refinementPreorder F T.rel).compatible o a b
    (fun k => .base (h k) ⟨(a k).2⟩ ⟨(b k).2⟩))

/-- The fixed-syntax contextual refinement theory underlying a full written theory. -/
def Theory.toRefinementTheory {F : Fragment} (T : Theory (τ := τ) (Φ := Φ) (ε := ε) F) :
    RefinementTheory (typedSyntax (τ := τ) Φ ε F) where
  Rel := T.precongruence.Rel
  refl := T.precongruence.refl
  trans := T.precongruence.trans
  congr _ hc h := hc.compatible T.precongruence h

/-- Equations in a written theory mean mutual refinement. -/
def Theory.toEquationalTheory {F : Fragment} (T : Theory (τ := τ) (Φ := Φ) (ε := ε) F) :
    EquationalTheory (typedSyntax (τ := τ) Φ ε F) := T.toRefinementTheory.equationalCore

/-- Native theory inclusions are functorial contextual theory inclusions. -/
def Theory.refinementFunctor (F : Fragment) :
    Theory (τ := τ) (Φ := Φ) (ε := ε) F ⥤ RefinementTheory (typedSyntax (τ := τ) Φ ε F) where
  obj := Theory.toRefinementTheory
  map f := homOfLE (fun h => leOfHom f h)

/-- Taking mutual refinements is likewise functorial. -/
def Theory.equationalFunctor (F : Fragment) :
    Theory (τ := τ) (Φ := Φ) (ε := ε) F ⥤ EquationalTheory (typedSyntax (τ := τ) Φ ε F) where
  obj := Theory.toEquationalTheory
  map f := homOfLE (fun h => ⟨leOfHom f h.1, leOfHom f h.2⟩)

/-- The generated theory as an object of the ambient contextual category. -/
def refinementObject (F : Fragment) (R : Relation τ Φ) : RefinementTheories :=
  ⟨typedSyntax (τ := τ) Φ ε F, (Theory.generated F R).toRefinementTheory⟩

/-- Mutual refinement as an ambient equational theory object. -/
def equationalObject (F : Fragment) (R : Relation τ Φ) : EquationalTheories :=
  ⟨typedSyntax (τ := τ) Φ ε F, (Theory.generated F R).toEquationalTheory⟩

end Silmaril.Isotope.Refinement
