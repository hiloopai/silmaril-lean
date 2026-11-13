module

public import Silmaril.Raw.SSA.Thesis.LambdaIter.Subtyping.Semantics.Agreement


@[expose] public section

-- Source lakefile: autoImplicit (Lean default) on, relaxedAutoImplicit off.
set_option autoImplicit true
set_option relaxedAutoImplicit false
universe v

namespace Silmaril.Thesis.LambdaIter.Subtyping.Semantics.Categorical

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped MonoidalCategory

variable {m : Type v → Type v} [Monad m] [LawfulMonad m]

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
    apply ConcreteCategory.coe_ext
    funext x
    have hx : (Types.binaryCoproductIso X Y).hom ((coprod.inl : _ ⟶ X ⨿ Y) x) = Sum.inl x :=
      types_congr_hom (Types.binaryCoproductIso_inl_comp_hom X Y) x
    change (pure (Sum.inl x) : m _) =
      joinM ((fun z => (pure ((Types.binaryCoproductIso X Y).hom z) : m _)) <$>
        (pure ((coprod.inl : _ ⟶ X ⨿ Y) x) : m _))
    rw [map_pure]
    change _ = (pure _ : m _) >>= id
    rw [pure_bind]
    exact congrArg pure hx.symm
  · simp only [inr_coprodComparison_assoc, splitMapCoprod,
      map_inr_inv_coprodComparison_assoc]
    rw [Kleisli.Type.inr_coprodIsoSum_hom]
    apply Kleisli.hom_ext
    apply ConcreteCategory.coe_ext
    funext y
    have hy : (Types.binaryCoproductIso X Y).hom ((coprod.inr : _ ⟶ X ⨿ Y) y) = Sum.inr y :=
      types_congr_hom (Types.binaryCoproductIso_inr_comp_hom X Y) y
    change (pure (Sum.inr y) : m _) =
      joinM ((fun z => (pure ((Types.binaryCoproductIso X Y).hom z) : m _)) <$>
        (pure ((coprod.inr : _ ⟶ X ⨿ Y) y) : m _))
    rw [map_pure]
    change _ = (pure _ : m _) >>= id
    rw [pure_bind]
    exact congrArg pure hy.symm

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
      have hi := types_congr_hom (Types.binaryCoproductIso_inl_comp_inv B A) b
      change (Types.binaryCoproductIso B A).inv (.inl b) = _ at hi
      rw [hi]
      have hd' : (DistributiveTensor.leftIso R B A).hom
          ((Types.binaryCoproductIso (R × B) (R × A)).inv (.inl (r, b))) =
          (r, ((coprod.inl : B ⟶ (B ⨿ A : Type v)) : B → _) b) := by
        have h1 : (Types.binaryCoproductIso (R × B) (R × A)).inv (.inl (r, b)) =
            (coprod.inl : R × B ⟶ (R × B) ⨿ (R × A)) (r, b) :=
          types_congr_hom (Types.binaryCoproductIso_inl_comp_inv _ _) (r, b)
        rw [h1]
        exact types_congr_hom (DistributiveTensor.inl_leftHom R B A) (r, b)
      rw [← hd']
      simp
  | inr a =>
      have hs : s = (Types.binaryCoproductIso B A).inv (.inr a) := by
        calc
          s = (Types.binaryCoproductIso B A).inv
              ((Types.binaryCoproductIso B A).hom s) := by simp
          _ = _ := by rw [h]
      subst s
      have hi := types_congr_hom (Types.binaryCoproductIso_inr_comp_inv B A) a
      change (Types.binaryCoproductIso B A).inv (.inr a) = _ at hi
      rw [hi]
      have hd' : (DistributiveTensor.leftIso R B A).hom
          ((Types.binaryCoproductIso (R × B) (R × A)).inv (.inr (r, a))) =
          (r, ((coprod.inr : A ⟶ (B ⨿ A : Type v)) : A → _) a) := by
        have h1 : (Types.binaryCoproductIso (R × B) (R × A)).inv (.inr (r, a)) =
            (coprod.inr : R × A ⟶ (R × B) ⨿ (R × A)) (r, a) :=
          types_congr_hom (Types.binaryCoproductIso_inr_comp_inv _ _) (r, a)
        rw [h1]
        exact types_congr_hom (DistributiveTensor.inr_leftHom R B A) (r, a)
      rw [← hd']
      simp

@[simp] private theorem types_fst_apply {X Y : Type v} (p : X × Y) :
    CartesianMonoidalCategory.fst X Y p = p.1 := by rfl

@[simp] private theorem typeJ_tensorIso_hom_of (X Y : Type v) (p : X × Y) :
    (Functor.StrongPremonoidal.tensorIso (J := typeJ (m := m)) X Y).hom.of p =
      (pure p : m _) := rfl

@[simp] private theorem typeJ_tensorIso_inv_of (X Y : Type v) (p : X × Y) :
    (Functor.StrongPremonoidal.tensorIso (J := typeJ (m := m)) X Y).inv.of p =
      (pure p : m _) := rfl

/-! port note: elementwise evaluation of Kleisli composites.  Under the current
Mathlib, morphisms of `Type` are bundled (`TypeCat.Hom`), so the thesis' `simp`
normalisation of `.of` no longer fires; these lemmas replace it. -/

theorem kleisli_comp_of {X Y Z : Kleisli (ofTypeMonad m)} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X.of) : (f ≫ g).of x = Bind.bind (m := m) (f.of x) g.of := by
  change joinM (m := m) (g.of <$> f.of x) = _
  exact bind_map_left (m := m) _ _ _

theorem typeJ_map_of {X Y : Type v} (f : X ⟶ Y) (x : X) :
    ((typeJ (m := m)).map f).of x = (pure (f x) : m Y) := rfl

theorem typeJ_whiskerLeft_of {X Y Z : Type v}
    (f : (typeJ (m := m)).obj Y ⟶ (typeJ (m := m)).obj Z) (x : X) (y : Y) :
    ((typeJ (m := m)).obj X ◁ f).of (x, y) =
      (fun z => (x, z)) <$> (show m Z from f.of y) := rfl

theorem retainLeft_eq {R X Y : Type v}
    (body : (typeJ (m := m)).obj X ⟶ (typeJ (m := m)).obj Y) :
    retainLeft (typeJ (m := m)) (R := R) body = (typeJ (m := m)).obj R ◁ body := by
  unfold retainLeft PremonoidalCategory.leftTensor
  rw [Kleisli.id_whiskerRight]
  simp only [Functor.StrongPremonoidal.tensorIso, Iso.refl_inv, Iso.refl_hom,
    Category.comp_id]
  exact (Category.id_comp _).trans (Category.id_comp ((typeJ (m := m)).obj R ◁ body))

theorem retainLeft_of {R X Y : Type v}
    (body : (typeJ (m := m)).obj X ⟶ (typeJ (m := m)).obj Y) (r : R) (x : X) :
    (retainLeft (typeJ (m := m)) (R := R) body).of (r, x) =
      Bind.bind (m := m) (body.of x) fun y => (pure (r, y) : m (R × Y)) := by
  rw [retainLeft_eq, typeJ_whiskerLeft_of]
  exact map_eq_bind_pure_comp (m := m) _ _

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
      Silmaril.Thesis.Elgot.kcomp (m := m) body.of (fun s =>
        (pure (match (Types.binaryCoproductIso B A).hom s with
          | .inl b => Sum.inl (r, b)
          | .inr a' => Sum.inr (r, a')) : m ((R × B) ⊕ (R × A)))) (r, a) := by
  rw [routeContext_hom]
  refine (kleisli_comp_of _ _ _).trans ?_
  refine (pure_bind (m := m) _ _).trans ?_
  refine (kleisli_comp_of _ _ _).trans ?_
  refine (congrArg (fun u => Bind.bind (m := m) u _) (retainLeft_of body r (r, a))).trans ?_
  refine (bind_assoc (m := m) _ _ _).trans ?_
  refine bind_congr fun s => ?_
  refine (pure_bind _ _).trans ?_
  have hr := routeContext_apply R B A r s
  change (pure (((DistributiveTensor.leftIso R B A).inv ≫
    (Types.binaryCoproductIso (R × B) (R × A)).hom) (r, s)) : m ((R × B) ⊕ (R × A))) = _
  rw [hr]
  cases (Types.binaryCoproductIso B A).hom s <;> rfl

theorem contextualLoop_of [Silmaril.Thesis.Elgot.Iterate m] [Silmaril.Thesis.Elgot.LawfulElgotMonad m]
    {R A B : Type v}
    (body : (typeJ (m := m)).obj (R × A) ⟶
      (typeJ (m := m)).obj (B ⨿ A : Type v)) (r : R) (a : A) :
    (contextualLoop (typeJ (m := m)) body).of (r, a) =
      Silmaril.Thesis.Elgot.iter (m := m) (fun a =>
        Silmaril.Thesis.Elgot.kcomp (m := m) body.of (fun s =>
          (pure ((Types.binaryCoproductIso B A).hom s) : m (B ⊕ A))) (r, a)) a := by
  unfold contextualLoop
  rw [Silmaril.Thesis.CategoryTheory.Kleisli.Type.comp_of_eq_kcomp, Silmaril.Thesis.CategoryTheory.Kleisli.Type.iterate_of]
  let q : A → m (B ⊕ A) := fun x =>
    Silmaril.Thesis.Elgot.kcomp (m := m) body.of (fun s =>
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
      _ = Silmaril.Thesis.Elgot.kcomp (m := m) body.of (fun s =>
          (pure (match (Types.binaryCoproductIso B A).hom s with
            | .inl b => Sum.inl (r, b)
            | .inr a' => Sum.inr (r, a')) : m _)) (r, x) := by
        simp only [F, Category.assoc]
        exact contextualBody_of body r x
      _ = _ := by
        simp only [q, Silmaril.Thesis.Elgot.kcomp]
        refine Eq.trans ?_ (bind_assoc (m := m) _ _ _).symm
        refine bind_congr fun s => ?_
        refine Eq.trans ?_ (pure_bind _ _).symm
        cases (Types.binaryCoproductIso B A).hom s <;> rfl
  let g : A → m ((R × B) ⊕ A) :=
    Silmaril.Thesis.Elgot.mapReturn (m := m) q
      (Silmaril.Thesis.Elgot.liftPure (m := m) (Prod.mk r))
  have comm : Silmaril.Thesis.Elgot.kcomp (m := m) g
        (Silmaril.Thesis.Elgot.liftPure (m := m) (Sum.map id (Prod.mk r))) =
      Silmaril.Thesis.Elgot.kcomp (m := m)
        (Silmaril.Thesis.Elgot.liftPure (m := m) (Prod.mk r)) F := by
    funext x
    simp only [Silmaril.Thesis.Elgot.kcomp, Silmaril.Thesis.Elgot.liftPure,
      Function.comp_apply, pure_bind]
    rw [hb]
    simp [g, Silmaril.Thesis.Elgot.mapReturn, Silmaril.Thesis.Elgot.liftPure]
    congr 1
    funext s
    cases s <;> simp
  have hu := Silmaril.Thesis.Elgot.LawfulElgotMonad.uniformity (m := m)
    g F (Prod.mk r) comm
  have hn := Silmaril.Thesis.Elgot.LawfulElgotMonad.naturality (m := m) q
    (Silmaril.Thesis.Elgot.liftPure (m := m) (Prod.mk r))
  change Silmaril.Thesis.Elgot.kcomp (m := m) (Silmaril.Thesis.Elgot.iter (m := m) F)
      (Silmaril.Thesis.Elgot.liftPure (m := m) Prod.snd) (r, a) = _
  calc
    _ = Silmaril.Thesis.Elgot.kcomp (m := m) (Silmaril.Thesis.Elgot.iter (m := m) g)
        (Silmaril.Thesis.Elgot.liftPure (m := m) Prod.snd) a := by
      rw [hu]
      simp [Silmaril.Thesis.Elgot.kcomp, Silmaril.Thesis.Elgot.liftPure, Function.comp_def]
    _ = Silmaril.Thesis.Elgot.kcomp (m := m)
        (Silmaril.Thesis.Elgot.kcomp (m := m) (Silmaril.Thesis.Elgot.iter (m := m) q)
          (Silmaril.Thesis.Elgot.liftPure (m := m) (Prod.mk r)))
        (Silmaril.Thesis.Elgot.liftPure (m := m) Prod.snd) a := by rw [hn]
    _ = Silmaril.Thesis.Elgot.iter (m := m) q a := by
      simp [Silmaril.Thesis.Elgot.kcomp, Silmaril.Thesis.Elgot.liftPure, Function.comp_def]
    _ = _ := rfl

end Silmaril.Thesis.LambdaIter.Subtyping.Semantics.Categorical
