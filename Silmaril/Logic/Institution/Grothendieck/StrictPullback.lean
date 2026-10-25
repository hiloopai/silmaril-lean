module

public import Silmaril.Logic.Institution.Grothendieck.Amalgamation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section

/-!
# Pullbacks in `Cat` and semi-exactness from one pushout per span

A commuting square of categories is a pullback in `Cat` exactly when objects and morphisms that
agree on the common part amalgamate uniquely: `StrictPullback.isPullback` proves the sufficiency
half of this, which is the form in which semi-exactness of a concrete institution is checked.

Semi-exactness asks every pushout square of signatures to amalgamate. Since pushouts are unique up
to isomorphism and model functors send isomorphisms to isomorphisms, it suffices to exhibit, for
every span, one pushout square that amalgamates (`StrictPullback.semiExact_of_exists`). This is
how the semi-exactness of concrete institutions is proved, with an explicit pushout construction.
-/

namespace Silmaril.Logic.Institution.StrictPullback

open CategoryTheory Limits

universe u₀ v₀ u v w m₁ m₂

section Heq

variable {C : Type u} [Category.{v} C]

theorem comp_heq {a b c a' b' c' : C} (ha : a = a') (hb : b = b') (hc : c = c')
    {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'} {g' : b' ⟶ c'} (hf : f ≍ f') (hg : g ≍ g') :
    f ≫ g ≍ f' ≫ g' := by
  subst ha hb hc
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  rfl

theorem id_heq {a a' : C} (h : a = a') : 𝟙 a ≍ 𝟙 a' := by
  subst h
  rfl

theorem map_heq_of_eq {D : Type u₀} [Category.{v₀} D] {F G : C ⥤ D} (h : F = G) {a b : C}
    (f : a ⟶ b) : F.map f ≍ G.map f := by
  subst h
  rfl

end Heq

variable {P X Y Z : Cat.{v, u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- A strictly commuting square of categories is a pullback in `Cat` when objects and morphisms
that agree on the common part amalgamate uniquely.

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §2.2,
Definition 5 (printed page 6, PDF page 7: semi-exactness as preservation of pullbacks by the model
functor into `Cat`); `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`,
§3 (PDF page 5: amalgamable squares as pullbacks, with unique amalgamation of models). -/
theorem isPullback (w : fst ≫ f = snd ≫ g)
    (obj_ex : ∀ (x : X) (y : Y), f.toFunctor.obj x = g.toFunctor.obj y →
      ∃ p : P, fst.toFunctor.obj p = x ∧ snd.toFunctor.obj p = y)
    (obj_uniq : ∀ p p' : P, fst.toFunctor.obj p = fst.toFunctor.obj p' →
      snd.toFunctor.obj p = snd.toFunctor.obj p' → p = p')
    (map_ex : ∀ {p q : P} (u : fst.toFunctor.obj p ⟶ fst.toFunctor.obj q)
      (v : snd.toFunctor.obj p ⟶ snd.toFunctor.obj q), f.toFunctor.map u ≍ g.toFunctor.map v →
      ∃ m : p ⟶ q, fst.toFunctor.map m = u ∧ snd.toFunctor.map m = v)
    (map_uniq : ∀ {p q : P} (m m' : p ⟶ q), fst.toFunctor.map m = fst.toFunctor.map m' →
      snd.toFunctor.map m = snd.toFunctor.map m' → m = m') :
    IsPullback fst snd f g := by
  classical
  -- Flexible forms of the morphism conditions, with endpoints only propositionally equal.
  have map_ex' : ∀ {p q : P} {x x' : X} {y y' : Y} (u : x ⟶ x') (v : y ⟶ y'),
      fst.toFunctor.obj p = x → fst.toFunctor.obj q = x' → snd.toFunctor.obj p = y →
      snd.toFunctor.obj q = y' → f.toFunctor.map u ≍ g.toFunctor.map v →
      ∃ m : p ⟶ q, fst.toFunctor.map m ≍ u ∧ snd.toFunctor.map m ≍ v := by
    intro p q x x' y y' u v hp₁ hq₁ hp₂ hq₂ huv
    subst hp₁ hq₁ hp₂ hq₂
    obtain ⟨m, h₁, h₂⟩ := map_ex u v huv
    exact ⟨m, heq_of_eq h₁, heq_of_eq h₂⟩
  have map_uniq' : ∀ {p q p' q' : P} (m : p ⟶ q) (m' : p' ⟶ q'), p = p' → q = q' →
      fst.toFunctor.map m ≍ fst.toFunctor.map m' → snd.toFunctor.map m ≍ snd.toFunctor.map m' →
      m ≍ m' := by
    intro p q p' q' m m' hp hq h₁ h₂
    subst hp hq
    exact heq_of_eq (map_uniq m m' (eq_of_heq h₁) (eq_of_heq h₂))
  have hw : ∀ (s : PullbackCone f g) (x : s.pt),
      f.toFunctor.obj (s.fst.toFunctor.obj x) = g.toFunctor.obj (s.snd.toFunctor.obj x) :=
    fun s x => Functor.congr_obj (congrArg Cat.Hom.toFunctor s.condition) x
  let L : ∀ s : PullbackCone f g, s.pt → P := fun s x => (obj_ex _ _ (hw s x)).choose
  have hL : ∀ (s : PullbackCone f g) (x : s.pt), fst.toFunctor.obj (L s x) = s.fst.toFunctor.obj x ∧
      snd.toFunctor.obj (L s x) = s.snd.toFunctor.obj x :=
    fun s x => (obj_ex _ _ (hw s x)).choose_spec
  have hm : ∀ (s : PullbackCone f g) (x x' : s.pt) (φ : x ⟶ x'), ∃ m : L s x ⟶ L s x',
      fst.toFunctor.map m ≍ s.fst.toFunctor.map φ ∧ snd.toFunctor.map m ≍ s.snd.toFunctor.map φ :=
    fun s x x' φ => map_ex' (s.fst.toFunctor.map φ) (s.snd.toFunctor.map φ) (hL s x).1 (hL s x').1 (hL s x).2 (hL s x').2
      (map_heq_of_eq (congrArg Cat.Hom.toFunctor s.condition) φ)
  let M : ∀ (s : PullbackCone f g) (x x' : s.pt) (φ : x ⟶ x'), L s x ⟶ L s x' :=
    fun s x x' φ => (hm s x x' φ).choose
  have hM : ∀ (s : PullbackCone f g) (x x' : s.pt) (φ : x ⟶ x'),
      fst.toFunctor.map (M s x x' φ) ≍ s.fst.toFunctor.map φ ∧
        snd.toFunctor.map (M s x x' φ) ≍ s.snd.toFunctor.map φ :=
    fun s x x' φ => (hm s x x' φ).choose_spec
  let lift : ∀ s : PullbackCone f g, s.pt ⟶ P := fun s => Cat.Hom.ofFunctor
    { obj := L s
      map := fun {x x'} φ => M s x x' φ
      map_id := fun x => eq_of_heq <| map_uniq' (M s x x (𝟙 x)) (𝟙 (L s x)) rfl rfl
        ((hM s x x (𝟙 x)).1.trans ((heq_of_eq (s.fst.toFunctor.map_id x)).trans
          ((id_heq (hL s x).1.symm).trans (heq_of_eq (fst.toFunctor.map_id (L s x)).symm))))
        ((hM s x x (𝟙 x)).2.trans ((heq_of_eq (s.snd.toFunctor.map_id x)).trans
          ((id_heq (hL s x).2.symm).trans (heq_of_eq (snd.toFunctor.map_id (L s x)).symm))))
      map_comp := fun {x x' x''} φ ψ => eq_of_heq <|
        map_uniq' (M s x x'' (φ ≫ ψ)) (M s x x' φ ≫ M s x' x'' ψ) rfl rfl
        ((hM s x x'' (φ ≫ ψ)).1.trans ((heq_of_eq (s.fst.toFunctor.map_comp φ ψ)).trans
          ((comp_heq (hL s x).1.symm (hL s x').1.symm (hL s x'').1.symm
            (hM s x x' φ).1.symm (hM s x' x'' ψ).1.symm).trans
            (heq_of_eq (fst.toFunctor.map_comp (M s x x' φ) (M s x' x'' ψ)).symm))))
        ((hM s x x'' (φ ≫ ψ)).2.trans ((heq_of_eq (s.snd.toFunctor.map_comp φ ψ)).trans
          ((comp_heq (hL s x).2.symm (hL s x').2.symm (hL s x'').2.symm
            (hM s x x' φ).2.symm (hM s x' x'' ψ).2.symm).trans
            (heq_of_eq (snd.toFunctor.map_comp (M s x x' φ) (M s x' x'' ψ)).symm)))) }
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w lift ?_ ?_ ?_)
  · intro s
    exact Cat.Hom.ext (Functor.hext (fun x => (hL s x).1) (fun x x' φ => (hM s x x' φ).1))
  · intro s
    exact Cat.Hom.ext (Functor.hext (fun x => (hL s x).2) (fun x x' φ => (hM s x x' φ).2))
  · intro s m hm₁ hm₂
    have e₁ := congrArg Cat.Hom.toFunctor hm₁
    have e₂ := congrArg Cat.Hom.toFunctor hm₂
    have hobj : ∀ x, m.toFunctor.obj x = L s x := fun x =>
      obj_uniq _ _ ((Functor.congr_obj e₁ x).trans (hL s x).1.symm)
        ((Functor.congr_obj e₂ x).trans (hL s x).2.symm)
    refine Cat.Hom.ext (Functor.hext hobj (fun x x' φ => ?_))
    exact map_uniq' _ _ (hobj x) (hobj x')
      ((map_heq_of_eq e₁ φ).trans (hM s x x' φ).1.symm)
      ((map_heq_of_eq e₂ φ).trans (hM s x x' φ).2.symm)

section SemiExact

variable {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{w, m₁, m₂})

/-- Model reducts compose contravariantly. -/
theorem modHom_comp {A B C : Sign} (a : A ⟶ B) (b : B ⟶ C) :
    modHom I (a ≫ b) = modHom I b ≫ modHom I a := by
  unfold modHom
  rw [I.map_comp]
  rfl

/-- Semi-exactness from one amalgamating pushout square per span: every other pushout of the
same span is isomorphic to it, and the model functor turns the isomorphism into an isomorphism of
model categories.

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §2.2,
Definition 5 (printed page 6, PDF page 7); pushouts are unique up to isomorphism. -/
theorem semiExact_of_exists
    (h : ∀ ⦃S S₁ S₂ : Sign⦄ (f₁ : S ⟶ S₁) (f₂ : S ⟶ S₂), ∃ (P : Sign) (g₁ : S₁ ⟶ P)
      (g₂ : S₂ ⟶ P), IsPushout f₁ f₂ g₁ g₂ ∧ Amalgamates I f₁ f₂ g₁ g₂) :
    SemiExact I := by
  intro S S₁ S₂ S' f₁ f₂ g₁ g₂ hpo
  obtain ⟨P, c₁, c₂, hc, ha⟩ := h f₁ f₂
  let e : P ≅ S' := IsPushout.isoIsPushout (h := hc) (h' := hpo)
  have he₁ : c₁ ≫ e.hom = g₁ := IsPushout.inl_isoIsPushout_hom (h := hc) (h' := hpo)
  have he₂ : c₂ ≫ e.hom = g₂ := IsPushout.inr_isoIsPushout_hom (h := hc) (h' := hpo)
  let E : (I.obj P).Mod ≅ (I.obj S').Mod :=
    { hom := modHom I e.inv
      inv := modHom I e.hom
      hom_inv_id := by
        rw [← modHom_comp, e.hom_inv_id]
        unfold modHom
        rw [I.map_id]
        rfl
      inv_hom_id := by
        rw [← modHom_comp, e.inv_hom_id]
        unfold modHom
        rw [I.map_id]
        rfl }
  refine IsPullback.of_iso ha E (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change modHom I c₁ ≫ 𝟙 _ = modHom I e.inv ≫ modHom I g₁
    rw [Category.comp_id, ← modHom_comp, ← he₁, Category.assoc, e.hom_inv_id, Category.comp_id]
  · change modHom I c₂ ≫ 𝟙 _ = modHom I e.inv ≫ modHom I g₂
    rw [Category.comp_id, ← modHom_comp, ← he₂, Category.assoc, e.hom_inv_id, Category.comp_id]
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

end SemiExact

end Silmaril.Logic.Institution.StrictPullback
