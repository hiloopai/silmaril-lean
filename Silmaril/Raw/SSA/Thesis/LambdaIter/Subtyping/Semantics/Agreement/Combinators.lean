module

public import Silmaril.Raw.SSA.Thesis.LambdaIter.Subtyping.Semantics.Agreement.Iteration


@[expose] public section

-- Source lakefile: autoImplicit (Lean default) on, relaxedAutoImplicit off.
set_option autoImplicit true
set_option relaxedAutoImplicit false
namespace Silmaril.Thesis.LambdaIter.Subtyping.Semantics

open _root_.CategoryTheory _root_.CategoryTheory.Limits Silmaril.Thesis.Elgot

universe v

namespace Categorical

variable {m : Type v → Type v} [Monad m] [LawfulMonad m]

abbrev J := Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m)

@[simp] private theorem types_fst_apply {X Y : Type v} (p : X × Y) :
    CartesianMonoidalCategory.fst X Y p = p.1 := by rfl

@[simp] private theorem types_snd_apply {X Y : Type v} (p : X × Y) :
    CartesianMonoidalCategory.snd X Y p = p.2 := by rfl

@[simp] theorem typeJ_tensorIso_hom_of (X Y : Type v) (p : X × Y) :
    (Functor.StrongPremonoidal.tensorIso (J := J (m := m)) X Y).hom.of p =
      (pure p : m _) := rfl

@[simp] theorem typeJ_tensorIso_inv_of (X Y : Type v) (p : X × Y) :
    (Functor.StrongPremonoidal.tensorIso (J := J (m := m)) X Y).inv.of p =
      (pure p : m _) := rfl

theorem bind_of {R A B : Type v}
    (f : (J (m := m)).obj R ⟶ (J (m := m)).obj A)
    (g : (J (m := m)).obj (R × A) ⟶ (J (m := m)).obj B) (r : R) :
    (Categorical.bind (J (m := m)) f g).of r =
      Silmaril.Thesis.Elgot.kcomp (m := m) f.of (fun a => g.of (r, a)) r := by
  have he : Categorical.extend (J (m := m)) f =
      (J (m := m)).map (Categorical.duplicate R) ≫ retainLeft (J (m := m)) f := rfl
  unfold Categorical.bind
  rw [he]
  refine (kleisli_comp_of _ _ _).trans ?_
  refine (congrArg (fun u => Bind.bind (m := m) u _)
    ((kleisli_comp_of _ _ _).trans ((pure_bind (m := m) _ _).trans (retainLeft_of f r r)))).trans ?_
  refine (bind_assoc (m := m) _ _ _).trans ?_
  exact bind_congr fun a => pure_bind _ _

theorem pair_of {R A B : Type v}
    (f : (J (m := m)).obj R ⟶ (J (m := m)).obj A)
    (g : (J (m := m)).obj R ⟶ (J (m := m)).obj B) (r : R) :
    (Categorical.pair (J (m := m)) f g).of r =
      Silmaril.Thesis.Elgot.kcomp (m := m) f.of (fun a =>
        Silmaril.Thesis.Elgot.kcomp (m := m) g.of (fun b => pure (a, b)) r) r := by
  unfold Categorical.pair
  refine (bind_of _ _ r).trans ?_
  refine bind_congr fun a => ?_
  refine (bind_of _ _ (r, a)).trans ?_
  refine (congrArg (fun u => Bind.bind (m := m) u _)
    ((kleisli_comp_of _ _ _).trans (pure_bind (m := m) _ _))).trans ?_
  rfl

theorem comp_map_of {R A B : Type v}
    (f : (J (m := m)).obj R ⟶ (J (m := m)).obj A) (g : A ⟶ B) (r : R) :
    (f ≫ (J (m := m)).map g).of r =
      Silmaril.Thesis.Elgot.kcomp (m := m) f.of (Silmaril.Thesis.Elgot.liftPure (m := m) g) r :=
  kleisli_comp_of _ _ _

theorem map_of {A B : Type v} (f : A ⟶ B) (a : A) :
    ((J (m := m)).map f).of a = (pure (f a) : m B) := rfl

theorem caseWithContext_of {R A B D : Type v}
    (scrutinee : (J (m := m)).obj R ⟶ (J (m := m)).obj (A ⨿ B : Type v))
    (left : (J (m := m)).obj (R × A) ⟶ (J (m := m)).obj D)
    (right : (J (m := m)).obj (R × B) ⟶ (J (m := m)).obj D) (r : R) :
    (Categorical.caseWithContext (J (m := m)) scrutinee left right).of r =
      Silmaril.Thesis.Elgot.kcomp (m := m) scrutinee.of (fun s =>
        match (Types.binaryCoproductIso A B).hom s with
        | .inl a => left.of (r, a)
        | .inr b => right.of (r, b)) r := by
  unfold Categorical.caseWithContext
  refine (bind_of _ _ r).trans ?_
  refine bind_congr fun s => ?_
  have harrow :
      (J (m := m)).map (DistributiveTensor.leftIso R A B).inv ≫
          Categorical.splitMapCoprod (J (m := m)) (R × A) (R × B) ≫
            coprod.desc left right =
        (J (m := m)).map
            ((DistributiveTensor.leftIso R A B).inv ≫
              (Types.binaryCoproductIso (R × A) (R × B)).hom) ≫
          Kleisli.Hom.mk (TypeCat.ofHom (Sum.elim left.of right.of)) := by
    rw [← CategoryTheory.Kleisli.Type.coprodIsoSum_hom_sumElim (m := m)]
    rw [← routeContext_hom]
    simp only [Category.assoc]
  refine (congrArg (fun k => k.of (r, s)) harrow).trans ?_
  refine (kleisli_comp_of _ _ _).trans ?_
  refine (pure_bind _ _).trans ?_
  change Sum.elim (⇑left.of) (⇑right.of)
      (((DistributiveTensor.leftIso R A B).inv ≫
        (Types.binaryCoproductIso (R × A) (R × B)).hom) (r, s)) = _
  rw [routeContext_apply]
  cases (Types.binaryCoproductIso A B).hom s <;> rfl

theorem abort_of {R E A : Type v} (emptyEquiv : E ≃ Empty)
    (f : (J (m := m)).obj R ⟶ (J (m := m)).obj E) (r : R) :
    (f ≫ (J (m := m)).map (TypeCat.ofHom fun z => Empty.elim (emptyEquiv z))).of r =
      Silmaril.Thesis.Elgot.kcomp (m := m) f.of
        (fun z => (pure (Empty.elim (emptyEquiv z)) : m A)) r :=
  kleisli_comp_of _ _ _

end Categorical

end Silmaril.Thesis.LambdaIter.Subtyping.Semantics
