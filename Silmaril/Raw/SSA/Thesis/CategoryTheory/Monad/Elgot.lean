module

public import Silmaril.Semantics.Categories.Thms
public import Silmaril.Raw.SSA.Thesis.Elgot.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-! # Elgot structure on Kleisli categories of type monads

Thesis `Isotope.CategoryTheory.Monad.Elgot` (imbrem/thesis @69a8126, CC0) for the thesis Elgot
classes `Silmaril.Thesis.Elgot.{Iterate,LawfulElgotMonad}`. The generic Kleisli coproduct and
distributivity structure is not duplicated: it is the library's `CategoryTheory.Kleisli.Type.*`
(`Silmaril.Raw.Semantics.Categories.Monad.Elgot`, the same thesis file adapted to the current
Mathlib). The Elgot-specific declarations below are the library's adapted proofs with the Elgot
 class replaced by the thesis's (`kcomp f g` is definitionally `f >=> g`). -/

@[expose] public section

universe u

namespace Silmaril.Thesis.CategoryTheory

open _root_.CategoryTheory _root_.CategoryTheory.Kleisli.Type
open Category Limits
open scoped MonoidalCategory

namespace Kleisli.Type

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]

/-- The thesis name of `CategoryTheory.Kleisli.Type.comp_of_eq_kleisliRight`. -/
theorem comp_of_eq_kcomp {X Y Z : Kleisli (TM m)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ⇑(f ≫ g).of = Silmaril.Thesis.Elgot.kcomp (show _ → m _ from f.of) g.of :=
  comp_of_eq_kleisliRight m f g

noncomputable instance iteration [Silmaril.Thesis.Elgot.Iterate m] : Iteration (Kleisli (TM m)) where
  iterate f := Kleisli.Hom.mk
    (↾(Silmaril.Thesis.Elgot.iter (m := m) (f ≫ (coprodIsoSum m _ _).hom).of))

@[simp] theorem iterate_of [Silmaril.Thesis.Elgot.Iterate m]
    {X Y : Kleisli (TM m)} (f : X ⟶ Y ⨿ X) :
    ⇑(CategoryTheory.iterate f).of =
      Silmaril.Thesis.Elgot.iter (m := m) (f ≫ (coprodIsoSum m Y X).hom).of := rfl

theorem iterate_fixpoint [Silmaril.Thesis.Elgot.Iterate m] [Silmaril.Thesis.Elgot.LawfulElgotMonad m]
    {X Y : Kleisli (TM m)} (f : X ⟶ Y ⨿ X) :
    iterate f = f ≫ coprod.desc (𝟙 Y) (iterate f) := by
  rw [← coprodIsoSum_hom_sumElim m (𝟙 _) (iterate f), ← Category.assoc]
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  rw [iterate_of]
  change Silmaril.Thesis.Elgot.iter (m := m) _ =
    ((f ≫ (coprodIsoSum m Y X).hom) ≫
      Kleisli.Hom.mk (↾(Sum.elim ((𝟙 Y : Y ⟶ Y).of) (Silmaril.Thesis.Elgot.iter (m := m) _)))).of
  conv_rhs => rw [comp_of_eq_kleisliRight]
  change Silmaril.Thesis.Elgot.iter (m := m) _ =
    (_ >=> Sum.elim (fun x ↦ (pure x : m _)) (Silmaril.Thesis.Elgot.iter (m := m) _))
  exact Silmaril.Thesis.Elgot.LawfulElgotMonad.fixpoint (m := m) _

theorem iterate_naturality [Silmaril.Thesis.Elgot.Iterate m] [Silmaril.Thesis.Elgot.LawfulElgotMonad m]
    {X Y Z : Kleisli (TM m)} (f : X ⟶ Y ⨿ X) (g : Y ⟶ Z) :
    iterate f ≫ g = iterate (f ≫ coprod.map g (𝟙 X)) := by
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  rw [comp_of_eq_kleisliRight, iterate_of, iterate_of]
  have h : (f ≫ coprod.map g (𝟙 X)) ≫ (coprodIsoSum m Z X).hom =
      (f ≫ (coprodIsoSum m Y X).hom) ≫ Kleisli.Hom.mk
        (↾(Sum.elim
          (show _ → m _ from g.of >=>
            Silmaril.Thesis.Elgot.liftPure (Sum.inl : Z.of → Z.of ⊕ X.of))
          (Silmaril.Thesis.Elgot.liftPure (m := m) (Sum.inr : X.of → Z.of ⊕ X.of)))) := by
    simp only [Category.assoc, coprodMap_coprodIsoSum_hom]; rfl
  have hof := congrArg (fun f : Kleisli.Hom (T := TM m) _ _ ↦ ⇑f.of) h
  rw [hof]
  conv_rhs => rw [comp_of_eq_kleisliRight]
  change (show _ → m _ from Silmaril.Thesis.Elgot.iter _ >=> g.of) =
    Silmaril.Thesis.Elgot.iter (m := m) (Silmaril.Thesis.Elgot.mapReturn (m := m) _ g.of)
  exact Silmaril.Thesis.Elgot.LawfulElgotMonad.naturality (m := m) _ _

theorem iterate_codiagonal [Silmaril.Thesis.Elgot.Iterate m] [Silmaril.Thesis.Elgot.LawfulElgotMonad m]
    {X Y : Kleisli (TM m)} (f : X ⟶ (Y ⨿ X) ⨿ X) :
    iterate (iterate f) =
      iterate (f ≫ coprod.desc (𝟙 (Y ⨿ X)) (coprod.inr : X ⟶ Y ⨿ X)) := by
  let b := (coprodIsoSum m Y X).hom
  let S := Kleisli.mk (TM m) (Y.of ⊕ X.of)
  let t := f ≫ coprod.map b (𝟙 X)
  let r := ⇑(t ≫ (coprodIsoSum m S X).hom).of
  have hr : r = Silmaril.Thesis.Elgot.mapReturn (m := m)
      (f ≫ (coprodIsoSum m (Y ⨿ X) X).hom).of b.of := by
    change ⇑((f ≫ coprod.map (coprodIsoSum m Y X).hom (𝟙 X)) ≫
      (coprodIsoSum m (Kleisli.mk (TM m) (Y.of ⊕ X.of)) X).hom).of = _
    have h := congrArg (fun f : Kleisli.Hom (T := TM m) _ _ ↦ ⇑f.of)
      (show (f ≫ coprod.map (coprodIsoSum m Y X).hom (𝟙 X)) ≫
          (coprodIsoSum m (Kleisli.mk (TM m) (Y.of ⊕ X.of)) X).hom =
        (f ≫ (coprodIsoSum m (Y ⨿ X) X).hom) ≫ Kleisli.Hom.mk
          (↾(Sum.elim
            (show _ → m _ from (coprodIsoSum m Y X).hom.of >=>
              Silmaril.Thesis.Elgot.liftPure (Sum.inl : (Y.of ⊕ X.of) → (Y.of ⊕ X.of) ⊕ X.of))
            (Silmaril.Thesis.Elgot.liftPure (m := m) (Sum.inr : X.of → (Y.of ⊕ X.of) ⊕ X.of)))) by
          simp only [Category.assoc, coprodMap_coprodIsoSum_hom]; rfl)
    rw [h, comp_of_eq_kleisliRight]
    rfl
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  rw [iterate_of, iterate_of]
  have hn := Silmaril.Thesis.Elgot.LawfulElgotMonad.naturality (m := m)
    (f ≫ (coprodIsoSum m (Y ⨿ X) X).hom).of b.of
  rw [← hr] at hn
  have hc := Silmaril.Thesis.Elgot.LawfulElgotMonad.codiagonal (m := m) r
  have hp : ⇑(iterate f ≫ b).of = Silmaril.Thesis.Elgot.iter (m := m) r := by
    rw [comp_of_eq_kleisliRight, iterate_of]
    exact hn
  rw [hp, hc]
  have hcmp :
      (f ≫ coprod.desc (𝟙 (Y ⨿ X)) (coprod.inr : X ⟶ Y ⨿ X)) ≫ b =
        (t ≫ (coprodIsoSum m S X).hom) ≫
          Kleisli.Hom.mk (↾(Silmaril.Thesis.Elgot.liftPure (m := m)
            (Silmaril.Thesis.Elgot.flatten (A := X.of) (B := Y.of)))) := by
    dsimp [t, b, S]
    rw [Category.assoc, codiagonal_comparison]
    simp only [Category.assoc]
    rfl
  rw [congrArg (fun f : Kleisli.Hom (T := TM m) _ _ ↦ ⇑f.of) hcmp]
  rw [comp_of_eq_kleisliRight]
  rfl

noncomputable instance elgotCategory [Silmaril.Thesis.Elgot.Iterate m]
    [Silmaril.Thesis.Elgot.LawfulElgotMonad m] : ElgotCategory (Kleisli (TM m)) where
  fixpoint := iterate_fixpoint m
  naturality := iterate_naturality m
  codiagonal := iterate_codiagonal m

noncomputable instance elgotFreydCategory [Silmaril.Thesis.Elgot.Iterate m]
    [Silmaril.Thesis.Elgot.LawfulElgotMonad m] :
    ElgotFreydCategory (Kleisli.Adjunction.toKleisli (TM m)) where
  uniformity f g h comm := by
    apply Kleisli.hom_ext
    apply ConcreteCategory.coe_ext
    rw [iterate_of]
    conv_rhs => rw [comp_of_eq_kleisliRight, iterate_of]
    apply Silmaril.Thesis.Elgot.LawfulElgotMonad.uniformity (m := m)
    have hcat :
        (f ≫ (coprodIsoSum m _ _).hom) ≫
            (Kleisli.Adjunction.toKleisli (TM m)).map (↾(Sum.map id h)) =
          (Kleisli.Adjunction.toKleisli (TM m)).map h ≫
            (g ≫ (coprodIsoSum m _ _).hom) := by
      calc
        _ = (f ≫ coprod.map (𝟙 _)
              ((Kleisli.Adjunction.toKleisli (TM m)).map h)) ≫
              (coprodIsoSum m _ _).hom := by
                simpa only [Category.assoc, TypeCat.ofHom_eq, Kleisli.Adjunction.toKleisli] using congrArg (f ≫ ·)
                  (coprodMap_pureRight_comparison m h).symm
        _ = ((Kleisli.Adjunction.toKleisli (TM m)).map h ≫ g) ≫
              (coprodIsoSum m _ _).hom := by rw [comm]
        _ = _ := Category.assoc _ _ _
    have hc := congrArg (fun f : Kleisli.Hom (T := TM m) _ _ ↦ ⇑f.of) hcat
    conv_lhs at hc => rw [comp_of_eq_kleisliRight]
    conv_rhs at hc => rw [comp_of_eq_kleisliRight]
    change (_ >=> Silmaril.Thesis.Elgot.liftPure (Sum.map id h)) =
      (Silmaril.Thesis.Elgot.liftPure h >=> _) at hc
    exact hc

theorem iter_threaded [Silmaril.Thesis.Elgot.Iterate m] [Silmaril.Thesis.Elgot.LawfulElgotMonad m]
    {A B Z : Type u} (q : A → m (B ⊕ A)) (z : Z) (x : A) :
    Silmaril.Thesis.Elgot.iter (m := m) (fun p : Z × A ↦ q p.2 >>= Sum.elim
      (fun b ↦ (pure (Sum.inl (p.1, b)) : m _))
      (fun a ↦ (pure (Sum.inr (p.1, a)) : m _))) (z, x) =
      (Silmaril.Thesis.Elgot.iter q >=> Silmaril.Thesis.Elgot.liftPure (Prod.mk z)) x := by
  let F : Z × A → m ((Z × B) ⊕ (Z × A)) := fun p ↦ q p.2 >>= Sum.elim
    (fun b ↦ pure (Sum.inl (p.1, b))) (fun a ↦ pure (Sum.inr (p.1, a)))
  let g : A → m ((Z × B) ⊕ A) :=
    Silmaril.Thesis.Elgot.mapReturn (m := m) q
      (Silmaril.Thesis.Elgot.liftPure (m := m) (Prod.mk z))
  have comm : (g >=> Silmaril.Thesis.Elgot.liftPure (Sum.map id (Prod.mk z))) =
      (Silmaril.Thesis.Elgot.liftPure (Prod.mk z) >=> F) := by
    funext a
    simp [g, F, Silmaril.Thesis.Elgot.mapReturn, Bind.kleisliRight,
      Silmaril.Thesis.Elgot.liftPure, Function.comp_def]
    congr 1
    funext s
    cases s <;> simp
  have hu := Silmaril.Thesis.Elgot.LawfulElgotMonad.uniformity (m := m) g F (Prod.mk z) comm
  have hn := Silmaril.Thesis.Elgot.LawfulElgotMonad.naturality (m := m) q
    (Silmaril.Thesis.Elgot.liftPure (m := m) (Prod.mk z))
  change Silmaril.Thesis.Elgot.iter (m := m) F (z, x) = _
  calc
    _ = Silmaril.Thesis.Elgot.iter (m := m) g x := by
      have hx := congrFun hu x
      dsimp only [Silmaril.Thesis.Elgot.kcomp] at hx
      simpa [Silmaril.Thesis.Elgot.liftPure, Function.comp_def] using
        hx.symm
    _ = _ := congrFun hn.symm x

noncomputable instance strongElgotFreydCategory [Silmaril.Thesis.Elgot.Iterate m]
    [Silmaril.Thesis.Elgot.LawfulElgotMonad m] :
    StrongElgotFreydCategory (Kleisli.Adjunction.toKleisli (TM m)) where
  iterate_whiskerLeft Z f := by
    apply Kleisli.hom_ext
    apply ConcreteCategory.coe_ext
    funext p
    rw [iterate_of]
    have hb :
        ⇑(((Z ◁ f) ≫ DistributivePremonoidalCategory.leftInv Z _ _) ≫
          (coprodIsoSum m (Z ⊗ _) (Z ⊗ _)).hom).of =
        fun p : Z.of × _ ↦ ((show _ → m _ from (f ≫ (coprodIsoSum m _ _).hom).of) >=> Sum.elim
            (fun y ↦ (pure (Sum.inl (p.1, y)) : m _))
            (fun x ↦ (pure (Sum.inr (p.1, x)) : m _))) p.2 := by
      funext p
      exact threadedBody_of m f p.1 p.2
    rw [hb]
    rcases p with ⟨z, x⟩
    change Silmaril.Thesis.Elgot.iter (m := m) (fun p ↦
      (f ≫ (coprodIsoSum m _ _).hom).of p.2 >>= Sum.elim
        (fun y ↦ (pure (Sum.inl (p.1, y)) : m _))
        (fun x ↦ (pure (Sum.inr (p.1, x)) : m _))) (z, x) = _
    erw [iter_threaded m]
    simp [Kleisli.whiskerLeft_of, Monad.Strong.strength, Bind.kleisliRight,
      Silmaril.Thesis.Elgot.liftPure, Function.comp_def]
    rfl

end Kleisli.Type

end Silmaril.Thesis.CategoryTheory
