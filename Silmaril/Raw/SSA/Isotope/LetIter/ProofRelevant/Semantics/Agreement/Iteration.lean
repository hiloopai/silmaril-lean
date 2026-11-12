module

public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.Semantics.Agreement

@[expose] public section

open Silmaril.Isotope.LetIter.LocallyNameless (Tm Pure TypedRenaming)

-- Preserve definitional object conversions across the Kleisli embedding.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v

namespace Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits

variable {m : Type v → Type v} [Monad m] [LawfulMonad m]

attribute [local simp] ofTypeMonad ofTypeFunctor

abbrev typeJ := Kleisli.Adjunction.toKleisli (ofTypeMonad m)

theorem splitMapCoprod_coprodIsoSum (X Y : Type v) :
    splitMapCoprod (typeJ (m := m)) X Y ≫
        (Kleisli.Type.coprodIsoSum m ((typeJ (m := m)).obj X)
          ((typeJ (m := m)).obj Y)).hom =
      (typeJ (m := m)).map (Types.binaryCoproductIso X Y).hom := by
  rw [← cancel_epi (coprodComparison (typeJ (m := m)) X Y)]
  apply coprod.hom_ext
  · simp only [inl_coprodComparison_assoc, splitMapCoprod,
      map_inl_inv_coprodComparison_assoc]
    rw [Kleisli.Type.inl_coprodIsoSum_hom]
    apply Kleisli.hom_ext
    ext x
    simp [Kleisli.Type.binaryCofan, Kleisli.Adjunction.toKleisli]
  · simp only [inr_coprodComparison_assoc, splitMapCoprod,
      map_inr_inv_coprodComparison_assoc]
    rw [Kleisli.Type.inr_coprodIsoSum_hom]
    apply Kleisli.hom_ext
    ext y
    simp [Kleisli.Type.binaryCofan, Kleisli.Adjunction.toKleisli]

theorem routeContext_hom (R B A : Type v) :
    (typeJ (m := m)).map (DistributiveTensor.leftIso R B A).inv ≫
        splitMapCoprod (typeJ (m := m)) (R × B) (R × A) ≫
          (Kleisli.Type.coprodIsoSum m ((typeJ (m := m)).obj (R × B))
            ((typeJ (m := m)).obj (R × A))).hom =
      (typeJ (m := m)).map
        ((DistributiveTensor.leftIso R B A).inv ≫
          (Types.binaryCoproductIso (R × B) (R × A)).hom) := by
  rw [splitMapCoprod_coprodIsoSum]
  exact ((typeJ (m := m)).map_comp _ _).symm

theorem routeContext_apply (R B A : Type v) (r : R) (s : B ⨿ A) :
    (((DistributiveTensor.leftIso R B A).inv ≫
      (Types.binaryCoproductIso (R × B) (R × A)).hom) (r, s)) =
      match (Types.binaryCoproductIso B A).hom s with
      | .inl b => .inl (r, b)
      | .inr a => .inr (r, a) := by
  cases h : (Types.binaryCoproductIso B A).hom s with
  | inl b =>
      have hs : s = (Types.binaryCoproductIso B A).inv (.inl b) := by
        calc
          s = (Types.binaryCoproductIso B A).inv
              ((Types.binaryCoproductIso B A).hom s) := by simp
          _ = _ := by rw [h]
      subst s
      have hi := ConcreteCategory.congr_hom (Types.binaryCoproductIso_inl_comp_inv B A) b
      change (Types.binaryCoproductIso B A).inv (.inl b) = _ at hi
      rw [hi]
      have hd' : (DistributiveTensor.leftIso R B A).hom
          ((Types.binaryCoproductIso (R × B) (R × A)).inv (.inl (r, b))) =
          (r, ((coprod.inl : B ⟶ (B ⨿ A : Type v)) : B → _) b) := by
        change (DistributiveTensor.leftHom R B A)
          ((Types.binaryCoproductIso (R × B) (R × A)).inv (.inl (r, b))) = _
        have hi' := ConcreteCategory.congr_hom (FC := TypeCat.Fun) (CC := fun X => X)
          (Types.binaryCoproductIso_inl_comp_inv (R × B) (R × A)) (r, b)
        simp only [types_comp_apply, TypeCat.ofHom_apply] at hi'
        rw [hi']
        exact congrArg (fun f : (R × B) ⟶ R × (B ⨿ A) => f (r, b))
          (DistributiveTensor.inl_leftHom R B A)
      rw [← hd']
      simp
      exact ConcreteCategory.congr_hom (FC := TypeCat.Fun) (CC := fun X => X)
        (Types.binaryCoproductIso_inl_comp_hom (R × B) (R × A)) (r, b)
  | inr a =>
      have hs : s = (Types.binaryCoproductIso B A).inv (.inr a) := by
        calc
          s = (Types.binaryCoproductIso B A).inv
              ((Types.binaryCoproductIso B A).hom s) := by simp
          _ = _ := by rw [h]
      subst s
      have hi := ConcreteCategory.congr_hom (Types.binaryCoproductIso_inr_comp_inv B A) a
      change (Types.binaryCoproductIso B A).inv (.inr a) = _ at hi
      rw [hi]
      have hd' : (DistributiveTensor.leftIso R B A).hom
          ((Types.binaryCoproductIso (R × B) (R × A)).inv (.inr (r, a))) =
          (r, ((coprod.inr : A ⟶ (B ⨿ A : Type v)) : A → _) a) := by
        change (DistributiveTensor.leftHom R B A)
          ((Types.binaryCoproductIso (R × B) (R × A)).inv (.inr (r, a))) = _
        have hi' := ConcreteCategory.congr_hom (FC := TypeCat.Fun) (CC := fun X => X)
          (Types.binaryCoproductIso_inr_comp_inv (R × B) (R × A)) (r, a)
        simp only [types_comp_apply, TypeCat.ofHom_apply] at hi'
        rw [hi']
        exact congrArg (fun f : (R × A) ⟶ R × (B ⨿ A) => f (r, a))
          (DistributiveTensor.inr_leftHom R B A)
      rw [← hd']
      simp
      exact ConcreteCategory.congr_hom (FC := TypeCat.Fun) (CC := fun X => X)
        (Types.binaryCoproductIso_inr_comp_hom (R × B) (R × A)) (r, a)

@[simp] private theorem types_fst_apply {X Y : Type v} (p : X × Y) :
    CartesianMonoidalCategory.fst X Y p = p.1 := by rfl

@[simp] private theorem typeJ_tensorIso_hom_of (X Y : Type v) (p : X × Y) :
    (Functor.StrongPremonoidal.tensorIso (J := typeJ (m := m)) X Y).hom.of p =
      (pure p : m _) := rfl

@[simp] private theorem typeJ_tensorIso_inv_of (X Y : Type v) (p : X × Y) :
    (Functor.StrongPremonoidal.tensorIso (J := typeJ (m := m)) X Y).inv.of p =
      (pure p : m _) := rfl

theorem contextualBody_of {R A B : Type v}
    (body : (typeJ (m := m)).obj (R × A) ⟶
      (typeJ (m := m)).obj (B ⨿ A : Type v)) (r : R) (a : A) :
    ((typeJ (m := m)).map (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst R A) (𝟙 (R × A))) ≫
        retainLeft (typeJ (m := m)) body ≫
        (typeJ (m := m)).map (DistributiveTensor.leftIso R B A).inv ≫
        splitMapCoprod (typeJ (m := m)) (R × B) (R × A) ≫
        (Kleisli.Type.coprodIsoSum m ((typeJ (m := m)).obj (R × B))
          ((typeJ (m := m)).obj (R × A))).hom).of (r, a) =
      ((show _ → m _ from body.of) >=> fun s =>
        (pure (match (Types.binaryCoproductIso B A).hom s with
          | .inl b => Sum.inl (r, b)
          | .inr a' => Sum.inr (r, a')) : m ((R × B) ⊕ (R × A)))) (r, a) := by
  rw [routeContext_hom]
  simp [retainLeft, PremonoidalCategory.leftTensor, typeJ,
    Functor.StrongPremonoidal.tensorIso, Kleisli.Adjunction.toKleisli,
    Kleisli.whiskerLeft_of, typeMonadStrength, Monad.Strong.strength,
    Bind.kleisliRight, joinM]
  congr 1
  funext s
  change (((DistributiveTensor.leftIso R B A).inv ≫
    (Types.binaryCoproductIso (R × B) (R × A)).hom) (r, s)) = _
  rw [routeContext_apply R B A r s]
  cases (Types.binaryCoproductIso B A).hom s <;> rfl

theorem contextualLoop_of [Silmaril.Elgot.Iterate m] [Silmaril.Elgot.LawfulElgotMonad m]
    {R A B : Type v}
    (body : (typeJ (m := m)).obj (R × A) ⟶
      (typeJ (m := m)).obj (B ⨿ A : Type v)) (r : R) (a : A) :
    (contextualLoop (typeJ (m := m)) body).of (r, a) =
      Silmaril.Elgot.iter (m := m) (fun a =>
        ((show _ → m _ from body.of) >=> fun s =>
          (pure ((Types.binaryCoproductIso B A).hom s) : m (B ⊕ A))) (r, a)) a := by
  unfold contextualLoop
  rw [Kleisli.Type.comp_of_eq_kleisliRight, Kleisli.Type.iterate_of]
  let q : A → m (B ⊕ A) := fun x =>
    ((show _ → m _ from body.of) >=> fun s =>
      (pure ((Types.binaryCoproductIso B A).hom s) : m (B ⊕ A))) (r, x)
  let F : R × A → m ((R × B) ⊕ (R × A)) :=
      (((typeJ (m := m)).map (CartesianMonoidalCategory.lift
            (CartesianMonoidalCategory.fst R A) (𝟙 (R × A))) ≫
          retainLeft (typeJ (m := m)) body ≫
          (typeJ (m := m)).map (DistributiveTensor.leftIso R B A).inv ≫
          splitMapCoprod (typeJ (m := m)) (R × B) (R × A)) ≫
        (Kleisli.Type.coprodIsoSum m ((typeJ (m := m)).obj (R × B))
          ((typeJ (m := m)).obj (R × A))).hom).of
  have hb (x : A) : F (r, x) = q x >>= Sum.elim
      (fun b => (pure (Sum.inl (r, b)) : m _))
      (fun a' => (pure (Sum.inr (r, a')) : m _)) := by
    calc
      _ = ((show _ → m _ from body.of) >=> fun s =>
          (pure (match (Types.binaryCoproductIso B A).hom s with
            | .inl b => Sum.inl (r, b)
            | .inr a' => Sum.inr (r, a')) : m _)) (r, x) := by
        simpa only [F, Category.assoc] using contextualBody_of body r x
      _ = _ := by
        simp [q, Bind.kleisliRight]
        rw [← bind_pure_comp]
        congr 1
        funext s
        cases (Types.binaryCoproductIso B A).hom s <;> rfl
  let g : A → m ((R × B) ⊕ A) :=
    Silmaril.Elgot.mapReturn (m := m) q
      (Silmaril.Elgot.liftPure (m := m) (Prod.mk r))
  have comm : (g >=> Silmaril.Elgot.liftPure (Sum.map id (Prod.mk r))) =
      (Silmaril.Elgot.liftPure (Prod.mk r) >=> F) := by
    funext x
    simp only [Bind.kleisliRight, Silmaril.Elgot.liftPure,
      Function.comp_apply, pure_bind]
    rw [hb]
    simp [g, Silmaril.Elgot.mapReturn, Silmaril.Elgot.liftPure]
    congr 1
    funext s
    cases s <;> simp
  have hu : Silmaril.Elgot.iter g =
      (Silmaril.Elgot.liftPure (Prod.mk r) >=> Silmaril.Elgot.iter F) :=
    Silmaril.Elgot.LawfulElgotMonad.uniformity (m := m) g F (Prod.mk r) comm
  have hn : (Silmaril.Elgot.iter q >=> Silmaril.Elgot.liftPure (Prod.mk r)) =
      Silmaril.Elgot.iter g :=
    Silmaril.Elgot.LawfulElgotMonad.naturality (m := m) q
      (Silmaril.Elgot.liftPure (m := m) (Prod.mk r))
  change (Silmaril.Elgot.iter F >=> Silmaril.Elgot.liftPure Prod.snd) (r, a) = _
  calc
    _ = (Silmaril.Elgot.iter g >=> Silmaril.Elgot.liftPure Prod.snd) a := by
      rw [hu]
      simp [Bind.kleisliRight, Silmaril.Elgot.liftPure, Function.comp_def]
    _ = ((Silmaril.Elgot.iter q >=> Silmaril.Elgot.liftPure (Prod.mk r)) >=>
        Silmaril.Elgot.liftPure Prod.snd) a := by rw [hn]
    _ = Silmaril.Elgot.iter (m := m) q a := by
      simp [Bind.kleisliRight, Silmaril.Elgot.liftPure, Function.comp_def]
    _ = _ := rfl

end Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
