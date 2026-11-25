module

public import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulUniversal.Position
public import Silmaril.Proofs.Semantics.RuntimeWires.PureInclusion.Centrality

public section

namespace Silmaril.RuntimeWires.Proofs.EffectfulUniversal.Position

open CategoryTheory MonoidalCategory Presentation RuntimeCoherence
open scoped MonoidalCategory SameArrow RuntimeCoherence

universe u v

variable {G : EffectfulPolygraph.{u,v}}

local notation "V" => valueWord (G := G)
local notation "R" => runtime G
local notation "J" => pureInclusion G
local notation "P" => pureValues G

/-- The ambient arrow underlying a computation arrow, for comparison across
different associations of the same boundary. -/
@[expose] def underlying {A B : Computations G} (f : A ⟶ B) : A.boundary ⟶ B.boundary := f

theorem underlying_comp {A B D : Computations G} (f : A ⟶ B) (g : B ⟶ D) :
    underlying (f ≫ g) = underlying f ≫ underlying g := by rfl

theorem normalize_append_tensor {X Y : Position G} (f : X.ambient ⟶ Y.ambient)
    {A B : Pure G} (p : A ⟶ B)
    (r : (X.append A.word).ambient ⟶ (Y.append B.word).ambient)
    (h : r ≈ₐ f ⊗ₘ (P).map p) :
    underlying (normalize r) ≈ₐ underlying (normalize f ⊗ₘ (J).map p) := by
  let q : V A.word ⟶ V B.word := (P).map p
  have e := (append_split_hom X A.word).comp (h.comp (append_split_inv Y B.word))
  have ht : (X.split.hom ▷ V A.word) ≫ (f ⊗ₘ q) ≫ (Y.split.inv ▷ V B.word) =
      underlying (normalize f) ⊗ₘ q := by
    change _ = (X.split.hom ≫ f ≫ Y.split.inv) ⊗ₘ q
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have hs := (right_normal (normalize f) (pureObject A)).comp
    (PureInclusion.left_pure Y.computation p)
  change underlying (normalize r) ≈ₐ
    underlying ((normalize f ▷ pureObject A) ≫ (Y.computation ◁ (J).map p))
  rw [underlying_comp]
  exact e.trans ((SameArrow.of_eq (ht.trans (MonoidalCategory.tensorHom_def _ _))).trans hs.symm)

private theorem pure_right_split {A B : Pure G} (p : A ⟶ B) (X : Computations G) :
    underlying ((J).map p ▷ X) ≈ₐ
      ((pureObject A).splitLeft X).hom ≫ ((P).map p ▷ X.boundary) ≫
        ((pureObject B).splitLeft X).inv := by
  let q : V A.word ⟶ V B.word := (P).map p
  let s := crossingWord (G := G) A.word
  let t := crossingWord (G := G) B.word
  have hn : s.hom ≫ (q ▷ R) = R ◁ q ≫ t.hom := PureInclusion.pureValues_natural p
  have en : R ◁ q = s.hom ≫ (q ▷ R) ≫ t.inv := by
    rw [← Category.assoc, hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e := (SameArrow.of_eq en).whiskerRight (X := V X.word) rfl
  simp only [comp_whiskerRight] at e
  exact (right_normal ((J).map p) X).trans (e.trans
    ((splitLeft_hom (pureObject A) X).symm.comp
      ((whisker_right_right q R (V X.word)).comp (splitLeft_inv (pureObject B) X).symm)))

theorem normalize_prepend_tensor {X Y : Position G} (f : X.ambient ⟶ Y.ambient)
    {A B : Pure G} (p : A ⟶ B)
    (r : (X.prepend A.word).ambient ⟶ (Y.prepend B.word).ambient)
    (h : r ≈ₐ (P).map p ⊗ₘ f) :
    underlying (normalize r) ≈ₐ underlying ((J).map p ⊗ₘ normalize f) := by
  let q : V A.word ⟶ V B.word := (P).map p
  let a := ((⟨A.word⟩ : Computations G).splitLeft X.computation).hom
  let b := ((⟨B.word⟩ : Computations G).splitLeft Y.computation).inv
  let g := underlying (normalize f)
  have e := (prepend_split_hom A.word X).comp (h.comp (prepend_split_inv B.word Y))
  change (prepend A.word X).split.hom ≫ r ≫ (prepend B.word Y).split.inv ≈ₐ
    (SameArrow.join a (V A.word ◁ X.split.hom) rfl) ≫ (q ⊗ₘ f) ≫
      (SameArrow.join (V B.word ◁ Y.split.inv) b rfl) at e
  rw [SameArrow.join_eq (f := a) (k := V A.word ◁ X.split.hom) rfl,
    SameArrow.join_eq (f := V B.word ◁ Y.split.inv) (k := b) rfl] at e
  have et : (V A.word ◁ X.split.hom) ≫ (q ⊗ₘ f) ≫ (V B.word ◁ Y.split.inv) =
      q ⊗ₘ g := by
    change _ = q ⊗ₘ (X.split.hom ≫ f ≫ Y.split.inv)
    simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have ec : underlying (normalize r) ≈ₐ a ≫ (q ⊗ₘ g) ≫ b := by
    refine e.trans (.of_eq ?_)
    simpa only [Category.assoc] using congrArg (fun z => a ≫ z ≫ b) et
  change underlying (normalize r) ≈ₐ
    underlying (((J).map p ▷ X.computation) ≫ ((J).obj B ◁ normalize f))
  rw [underlying_comp]
  let m := ((⟨B.word⟩ : Computations G).splitLeft X.computation)
  have el : underlying ((J).obj B ◁ normalize f) = m.hom ≫ (V B.word ◁ g) ≫ b := by
    rfl
  have eq : (a ≫ (q ▷ X.computation.boundary) ≫ m.inv) ≫
      (m.hom ≫ (V B.word ◁ g) ≫ b) = a ≫ (q ⊗ₘ g) ≫ b := by
    rw [MonoidalCategory.tensorHom_def]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact ec.trans ((SameArrow.of_eq eq.symm).trans
    (((pure_right_split p X.computation).comp (SameArrow.of_eq el)).symm))

end Silmaril.RuntimeWires.Proofs.EffectfulUniversal.Position
