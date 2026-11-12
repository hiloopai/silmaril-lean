module

public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.Semantics.Agreement.Iteration

@[expose] public section

open Silmaril.Isotope.LetIter.LocallyNameless (Tm Pure TypedRenaming)

-- Preserve definitional object conversions across the Kleisli embedding.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Silmaril.Isotope.LetIter.ProofRelevant.Semantics

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot

universe v

namespace Categorical

variable {m : Type v → Type v} [Monad m] [LawfulMonad m]

attribute [local simp] ofTypeMonad ofTypeFunctor

@[simp] private theorem types_fst_apply {X Y : Type v} (p : X × Y) :
    CartesianMonoidalCategory.fst X Y p = p.1 := by rfl

@[simp] private theorem types_snd_apply {X Y : Type v} (p : X × Y) :
    CartesianMonoidalCategory.snd X Y p = p.2 := by rfl

@[simp] theorem typeJ_tensorIso_hom_of (X Y : Type v) (p : X × Y) :
    (Functor.StrongPremonoidal.tensorIso (J := typeJ (m := m)) X Y).hom.of p =
      (pure p : m _) := rfl

@[simp] theorem typeJ_tensorIso_inv_of (X Y : Type v) (p : X × Y) :
    (Functor.StrongPremonoidal.tensorIso (J := typeJ (m := m)) X Y).inv.of p =
      (pure p : m _) := rfl

theorem bind_of {R A B : Type v}
    (f : (typeJ (m := m)).obj R ⟶ (typeJ (m := m)).obj A)
    (g : (typeJ (m := m)).obj (R × A) ⟶ (typeJ (m := m)).obj B) (r : R) :
    (Categorical.bind (typeJ (m := m)) f g).of r =
      ((show _ → m _ from f.of) >=> fun a => g.of (r, a)) r := by
  simp [Categorical.bind, Categorical.extend, Categorical.duplicate,
    PremonoidalCategory.leftTensor, typeJ, Kleisli.Adjunction.toKleisli,
    Kleisli.whiskerLeft_of, typeMonadStrength, Monad.Strong.strength,
    Functor.StrongPremonoidal.tensorIso, Bind.kleisliRight, joinM]
  rfl

theorem pair_of {R A B : Type v}
    (f : (typeJ (m := m)).obj R ⟶ (typeJ (m := m)).obj A)
    (g : (typeJ (m := m)).obj R ⟶ (typeJ (m := m)).obj B) (r : R) :
    (Categorical.pair (typeJ (m := m)) f g).of r =
      ((show _ → m _ from f.of) >=> fun a => ((show _ → m _ from g.of) >=> fun b => pure (a, b)) r) r := by
  unfold Categorical.pair
  rw [bind_of]
  apply congrArg (fun k => ((show _ → m _ from f.of) >=> k) r)
  funext a
  change A at a
  refine (bind_of (R := R × A) (A := B) (B := A × B) _ _ (r, a)).trans ?_
  simp [Categorical.retainedContext, Bind.kleisliRight, joinM]
  rfl

theorem comp_map_of {R A B : Type v}
    (f : (typeJ (m := m)).obj R ⟶ (typeJ (m := m)).obj A) (g : A → B) (r : R) :
    (f ≫ (typeJ (m := m)).map (TypeCat.ofHom g)).of r =
      ((show _ → m _ from f.of) >=> Silmaril.Elgot.liftPure g) r := by
  rw [CategoryTheory.Kleisli.Type.comp_of_eq_kleisliRight]
  rfl

theorem map_of {A B : Type v} (f : A → B) (a : A) :
    ((typeJ (m := m)).map (TypeCat.ofHom f)).of a = (pure (f a) : m B) := rfl

theorem caseWithContext_of {R A B D : Type v}
    (scrutinee : (typeJ (m := m)).obj R ⟶ (typeJ (m := m)).obj (A ⨿ B : Type v))
    (left : (typeJ (m := m)).obj (R × A) ⟶ (typeJ (m := m)).obj D)
    (right : (typeJ (m := m)).obj (R × B) ⟶ (typeJ (m := m)).obj D) (r : R) :
    (Categorical.caseWithContext (typeJ (m := m)) scrutinee left right).of r =
      ((show _ → m _ from scrutinee.of) >=> fun s =>
        match (Types.binaryCoproductIso A B).hom s with
        | .inl a => left.of (r, a)
        | .inr b => right.of (r, b)) r := by
  unfold Categorical.caseWithContext
  rw [bind_of]
  apply congrArg (fun k => ((show _ → m _ from scrutinee.of) >=> k) r)
  funext s
  have harrow :
      (typeJ (m := m)).map (DistributiveTensor.leftIso R A B).inv ≫
          Categorical.splitMapCoprod (typeJ (m := m)) (R × A) (R × B) ≫
            coprod.desc left right =
        (typeJ (m := m)).map
            ((DistributiveTensor.leftIso R A B).inv ≫
              (Types.binaryCoproductIso (R × A) (R × B)).hom) ≫
          Kleisli.Hom.mk (TypeCat.ofHom (Sum.elim left.of right.of)) := by
    calc
      _ = (typeJ (m := m)).map (DistributiveTensor.leftIso R A B).inv ≫
          Categorical.splitMapCoprod (typeJ (m := m)) (R × A) (R × B) ≫
            ((Kleisli.Type.coprodIsoSum m _ _).hom ≫
              Kleisli.Hom.mk (TypeCat.ofHom (Sum.elim left.of right.of))) := by
            rw [CategoryTheory.Kleisli.Type.coprodIsoSum_hom_sumElim (m := m)]
      _ = ((typeJ (m := m)).map (DistributiveTensor.leftIso R A B).inv ≫
          Categorical.splitMapCoprod (typeJ (m := m)) (R × A) (R × B) ≫
            (Kleisli.Type.coprodIsoSum m _ _).hom) ≫
              Kleisli.Hom.mk (TypeCat.ofHom (Sum.elim left.of right.of)) := by simp only [Category.assoc]
      _ = _ := by rw [routeContext_hom]
  change ((typeJ (m := m)).map (DistributiveTensor.leftIso R A B).inv ≫
      Categorical.splitMapCoprod (typeJ (m := m)) (R × A) (R × B) ≫
        coprod.desc left right).of (r, s) = _
  rw [harrow]
  rw [CategoryTheory.Kleisli.Type.comp_of_eq_kleisliRight]
  simp [Bind.kleisliRight, joinM]
  change Sum.elim left.of right.of
      (((DistributiveTensor.leftIso R A B).inv ≫
        (Types.binaryCoproductIso (R × A) (R × B)).hom) (r, s)) = _
  rw [routeContext_apply]
  cases (Types.binaryCoproductIso A B).hom s <;> rfl

theorem abort_of {R E A : Type v} (emptyEquiv : E ≃ Empty)
    (f : (typeJ (m := m)).obj R ⟶ (typeJ (m := m)).obj E) (r : R) :
    (f ≫ (typeJ (m := m)).map (TypeCat.ofHom (fun z => Empty.elim (emptyEquiv z)))).of r =
      ((show _ → m _ from f.of) >=> fun z => (pure (Empty.elim (emptyEquiv z)) : m A)) r := by
  exact comp_map_of f (fun z => Empty.elim (emptyEquiv z)) r

end Categorical

end Silmaril.Isotope.LetIter.ProofRelevant.Semantics
