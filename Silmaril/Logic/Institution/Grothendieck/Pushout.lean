module

public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

@[expose] public section

/-!
# Pushouts in the Grothendieck construction

For a functor `G : C ⥤ Cat`, write `vert σ = (𝟙, σ) : (i, Σ) ⟶ (i, Σ')` for the fiber morphisms
(Mathlib's `Grothendieck.ι`) and `cart d Σ = (d, 𝟙) : (i, Σ) ⟶ (j, Gᵈ Σ)` for the cocartesian
lifts (the components of Mathlib's `Grothendieck.ιNatTrans`) of Mathlib's Grothendieck
construction `Grothendieck G`. Three kinds of commuting squares are pushouts:

* `isPushout_cart`, `isPushout_cocart`: the naturality square of a cocartesian lift along a
  fiber morphism `σ : Σ ⟶ Σ₁` (in the second form with the corner `Gᵈ Σ` renamed to an equal
  object `T`);
* `isPushout_index`: the square of cocartesian lifts at `Σ` over a pushout square of indices;
* `isPushout_vert`: the image of a pushout square of a fiber, when every reindexing functor
  preserves pushouts.

Every square of the Grothendieck construction whose span has a pushout of indices and of the
transported fibers is pasted from these, since every morphism is a cocartesian lift followed by
a fiber morphism (`eq_cart_comp_vert`). This is the canonical construction of pushouts of
Grothendieck signatures.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3,
Proposition 3.4 (PDF page 5); the four-square decomposition of
`diaconescu-2002-grothendieck-institutions` in `references.bib`, §4.3, proof
of Theorem 5 (printed page 14, PDF page 15).
-/

namespace Silmaril.Logic.Institution.GrothendieckPushout

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂ v u

/-- A commuting square is a pushout as soon as every cocone factors through it uniquely. -/
theorem isPushout_of_forall {D : Type u} [Category.{v} D] {Z X Y P : D} {f : Z ⟶ X}
    {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} (w : f ≫ inl = g ≫ inr)
    (hex : ∀ {W : D} (a : X ⟶ W) (b : Y ⟶ W), f ≫ a = g ≫ b →
      ∃ m : P ⟶ W, inl ≫ m = a ∧ inr ≫ m = b)
    (huniq : ∀ {W : D} (m m' : P ⟶ W), inl ≫ m = inl ≫ m' → inr ≫ m = inr ≫ m' → m = m') :
    IsPushout f g inl inr :=
  IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s => (hex s.inl s.inr s.condition).choose)
    (fun s => (hex s.inl s.inr s.condition).choose_spec.1)
    (fun s => (hex s.inl s.inr s.condition).choose_spec.2)
    (fun s m h₁ h₂ => huniq m _ (h₁.trans (hex s.inl s.inr s.condition).choose_spec.1.symm)
      (h₂.trans (hex s.inl s.inr s.condition).choose_spec.2.symm)))

variable {C : Type u₁} [Category.{v₁} C] {G : C ⥤ Cat.{v₂, u₂}}

/-- The fiber morphism `(𝟙, σ) : (i, Σ) ⟶ (i, Σ')`; it is `(Grothendieck.ι G i).map σ`. -/
def vert {i : C} {S S' : G.obj i} (σ : S ⟶ S') : (⟨i, S⟩ : Grothendieck G) ⟶ ⟨i, S'⟩ :=
  ⟨𝟙 i, eqToHom (by simp) ≫ σ⟩

/-- The cocartesian lift `(d, 𝟙) : (i, Σ) ⟶ (j, Gᵈ Σ)`; it is
`(Grothendieck.ιNatTrans d).app Σ`. -/
def cart {i j : C} (d : i ⟶ j) (S : G.obj i) :
    (⟨i, S⟩ : Grothendieck G) ⟶ ⟨j, (G.map d).toFunctor.obj S⟩ :=
  ⟨d, 𝟙 _⟩

@[simp] theorem vert_base {i : C} {S S' : G.obj i} (σ : S ⟶ S') : (vert σ).base = 𝟙 i := rfl

@[simp] theorem vert_fiber {i : C} {S S' : G.obj i} (σ : S ⟶ S') :
    (vert σ).fiber = eqToHom (by simp) ≫ σ := rfl

@[simp] theorem cart_base {i j : C} (d : i ⟶ j) (S : G.obj i) : (cart d S).base = d := rfl

@[simp] theorem cart_fiber {i j : C} (d : i ⟶ j) (S : G.obj i) :
    (cart (G := G) d S).fiber = 𝟙 _ := rfl

theorem ι_map_eq_vert {i : C} {S S' : G.obj i} (σ : S ⟶ S') :
    (Grothendieck.ι G i).map σ = vert σ := rfl

theorem ιNatTrans_app_eq_cart {i j : C} (d : i ⟶ j) (S : G.obj i) :
    (Grothendieck.ιNatTrans d).app S = cart d S := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Morphisms out of the codomain of a morphism with invertible fiber component are determined by
their base and their composite with it. -/
theorem hom_ext_of_isIso_fiber {X Y W : Grothendieck G} (k : X ⟶ Y) (hk : IsIso k.fiber)
    {m m' : Y ⟶ W} (hb : m.base = m'.base) (h : k ≫ m = k ≫ m') : m = m' := by
  have := hk
  rcases m with ⟨m₀, m₁⟩
  rcases m' with ⟨m₀', m₁'⟩
  change m₀ = m₀' at hb
  subst hb
  have hf := Grothendieck.congr h
  simp only [Grothendieck.comp_fiber, eqToHom_trans_assoc, cancel_epi] at hf
  subst hf
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every morphism of the Grothendieck construction is a cocartesian lift followed by a fiber
morphism. -/
theorem eq_cart_comp_vert {X Y : Grothendieck G} (f : X ⟶ Y) :
    f = cart f.base X.fiber ≫ vert f.fiber := by
  fapply Grothendieck.ext
  · simp
  · apply eq_of_heq
    simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The naturality square of a cocartesian lift along a fiber morphism is a pushout. -/
theorem isPushout_cart {i j : C} (d : i ⟶ j) {S S₁ : G.obj i} (σ : S ⟶ S₁) :
    IsPushout (vert σ) (cart d S) (cart d S₁) (vert ((G.map d).toFunctor.map σ)) := by
  have nat : vert σ ≫ cart d S₁ = cart d S ≫ vert ((G.map d).toFunctor.map σ) :=
    (Grothendieck.ιNatTrans d).naturality σ
  refine isPushout_of_forall nat ?_ ?_
  · intro W a b hab
    rcases a with ⟨a₀, a₁⟩
    rcases b with ⟨b₀, b₁⟩
    have hb : a₀ = d ≫ b₀ := by simpa using congrArg Grothendieck.Hom.base hab
    subst hb
    have hobj : (G.map b₀).toFunctor.obj ((G.map d).toFunctor.obj S₁) =
        (G.map (d ≫ b₀)).toFunctor.obj S₁ := by
      simp only [Functor.map_comp, Cat.Hom.comp_obj]
    have fac₁ : cart d S₁ ≫
        (⟨b₀, eqToHom hobj ≫ a₁⟩ : (⟨j, (G.map d).toFunctor.obj S₁⟩ : Grothendieck G) ⟶ W) =
        ⟨d ≫ b₀, a₁⟩ := by
      fapply Grothendieck.ext
      · simp
      · apply eq_of_heq
        simp
    refine ⟨⟨b₀, eqToHom hobj ≫ a₁⟩, fac₁, ?_⟩
    refine hom_ext_of_isIso_fiber (cart d S) (IsIso.id _) ?_ ?_
    · simp
    · rw [← Category.assoc, ← nat, Category.assoc, fac₁, hab]
  · intro W m m' h₁ h₂
    refine hom_ext_of_isIso_fiber (cart d S₁) (IsIso.id _) ?_ h₁
    simpa using congrArg Grothendieck.Hom.base h₂

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The naturality square of a cocartesian lift along a fiber morphism, with its corner `Gᵈ Σ`
renamed to an equal object `T`, is a pushout. -/
theorem isPushout_cocart {i j : C} (d : i ⟶ j) {S S₁ : G.obj i} (σ : S ⟶ S₁) {T : G.obj j}
    (p : (G.map d).toFunctor.obj S = T) :
    IsPushout (vert σ) (⟨d, eqToHom p⟩ : (⟨i, S⟩ : Grothendieck G) ⟶ ⟨j, T⟩) (cart d S₁)
      (vert (eqToHom p.symm ≫ (G.map d).toFunctor.map σ)) := by
  subst p
  simp only [eqToHom_refl, Category.id_comp]
  exact isPushout_cart d σ

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Over a pushout square of indices, the square of cocartesian lifts of a fiber object is a
pushout. -/
theorem isPushout_index {i i₁ i₂ j : C} {d₁ : i ⟶ i₁} {d₂ : i ⟶ i₂} {e₁ : i₁ ⟶ j}
    {e₂ : i₂ ⟶ j} (hI : IsPushout d₁ d₂ e₁ e₂) (S : G.obj i) {T : G.obj j}
    (p₁ : (G.map e₁).toFunctor.obj ((G.map d₁).toFunctor.obj S) = T)
    (p₂ : (G.map e₂).toFunctor.obj ((G.map d₂).toFunctor.obj S) = T) :
    IsPushout (cart d₁ S) (cart d₂ S)
      (⟨e₁, eqToHom p₁⟩ : (⟨i₁, (G.map d₁).toFunctor.obj S⟩ : Grothendieck G) ⟶ ⟨j, T⟩)
      (⟨e₂, eqToHom p₂⟩ : (⟨i₂, (G.map d₂).toFunctor.obj S⟩ : Grothendieck G) ⟶ ⟨j, T⟩) := by
  have w : cart d₁ S ≫
      (⟨e₁, eqToHom p₁⟩ : (⟨i₁, (G.map d₁).toFunctor.obj S⟩ : Grothendieck G) ⟶ ⟨j, T⟩) =
      cart d₂ S ≫
      (⟨e₂, eqToHom p₂⟩ : (⟨i₂, (G.map d₂).toFunctor.obj S⟩ : Grothendieck G) ⟶ ⟨j, T⟩) := by
    fapply Grothendieck.ext
    · simpa using hI.w
    · apply eq_of_heq
      simp
  refine isPushout_of_forall w ?_ ?_
  · intro W a b hab
    rcases a with ⟨a₀, a₁⟩
    rcases b with ⟨b₀, b₁⟩
    have hb : d₁ ≫ a₀ = d₂ ≫ b₀ := by simpa using congrArg Grothendieck.Hom.base hab
    have hobj : (G.map (hI.desc a₀ b₀ hb)).toFunctor.obj T =
        (G.map a₀).toFunctor.obj ((G.map d₁).toFunctor.obj S) :=
      calc (G.map (hI.desc a₀ b₀ hb)).toFunctor.obj T
          = (G.map (hI.desc a₀ b₀ hb)).toFunctor.obj
              ((G.map e₁).toFunctor.obj ((G.map d₁).toFunctor.obj S)) := by rw [p₁]
        _ = (G.map (e₁ ≫ hI.desc a₀ b₀ hb)).toFunctor.obj ((G.map d₁).toFunctor.obj S) := by
              rw [Functor.map_comp, Cat.Hom.comp_obj]
        _ = (G.map a₀).toFunctor.obj ((G.map d₁).toFunctor.obj S) := by rw [hI.inl_desc]
    have fac₁ : @Eq ((⟨i₁, (G.map d₁).toFunctor.obj S⟩ : Grothendieck G) ⟶ W)
        ((⟨e₁, eqToHom p₁⟩ :
          (⟨i₁, (G.map d₁).toFunctor.obj S⟩ : Grothendieck G) ⟶ ⟨j, T⟩) ≫
        (⟨hI.desc a₀ b₀ hb, eqToHom hobj ≫ a₁⟩ : (⟨j, T⟩ : Grothendieck G) ⟶ W)) ⟨a₀, a₁⟩ := by
      fapply Grothendieck.ext
      · simp
      · apply eq_of_heq
        simp [eqToHom_map]
    refine ⟨⟨hI.desc a₀ b₀ hb, eqToHom hobj ≫ a₁⟩, fac₁, ?_⟩
    refine hom_ext_of_isIso_fiber (cart d₂ S) (IsIso.id _) ?_ ?_
    · simp
    · rw [← Category.assoc, ← w, Category.assoc, fac₁, hab]
  · intro W m m' h₁ h₂
    refine hom_ext_of_isIso_fiber
      (⟨e₁, eqToHom p₁⟩ : (⟨i₁, (G.map d₁).toFunctor.obj S⟩ : Grothendieck G) ⟶ ⟨j, T⟩)
      (eqToIso p₁).isIso_hom ?_ h₁
    exact hI.hom_ext (by simpa using congrArg Grothendieck.Hom.base h₁)
      (by simpa using congrArg Grothendieck.Hom.base h₂)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- If every reindexing functor out of `G i` preserves pushouts, the fiber inclusion
`G i ⥤ Grothendieck G` preserves pushout squares. -/
theorem isPushout_vert {i : C} {S S₁ S₂ S' : G.obj i} {f₁ : S ⟶ S₁} {f₂ : S ⟶ S₂}
    {g₁ : S₁ ⟶ S'} {g₂ : S₂ ⟶ S'} (hP : IsPushout f₁ f₂ g₁ g₂)
    (hG : ∀ {j : C} (u : i ⟶ j), PreservesColimitsOfShape WalkingSpan (G.map u).toFunctor) :
    IsPushout (vert f₁) (vert f₂) (vert g₁) (vert g₂) := by
  have w : vert f₁ ≫ vert g₁ = vert f₂ ≫ vert g₂ :=
    calc vert f₁ ≫ vert g₁ = (Grothendieck.ι G i).map (f₁ ≫ g₁) :=
          ((Grothendieck.ι G i).map_comp f₁ g₁).symm
      _ = (Grothendieck.ι G i).map (f₂ ≫ g₂) := by rw [hP.w]
      _ = vert f₂ ≫ vert g₂ := (Grothendieck.ι G i).map_comp f₂ g₂
  refine isPushout_of_forall w ?_ ?_
  · intro W a b hab
    rcases a with ⟨a₀, a₁⟩
    rcases b with ⟨b₀, b₁⟩
    have hb : a₀ = b₀ := by simpa using congrArg Grothendieck.Hom.base hab
    subst hb
    have hf := Grothendieck.congr hab
    simp only [Grothendieck.comp_fiber, vert_fiber, vert_base, Functor.map_comp, eqToHom_map,
      Category.assoc, eqToHom_trans_assoc, cancel_epi] at hf
    have := hG (a₀ : i ⟶ W.base)
    have hP' := hP.map (G.map (a₀ : i ⟶ W.base)).toFunctor
    refine ⟨⟨a₀, hP'.desc a₁ b₁ hf⟩, ?_, ?_⟩
    · fapply Grothendieck.ext
      · simp
      · apply eq_of_heq
        simp [eqToHom_map]
    · fapply Grothendieck.ext
      · simp
      · apply eq_of_heq
        simp [eqToHom_map]
  · intro W m m' h₁ h₂
    rcases m with ⟨m₀, m₁⟩
    rcases m' with ⟨m₀', m₁'⟩
    have hb : m₀ = m₀' := by simpa using congrArg Grothendieck.Hom.base h₁
    subst hb
    have hf₁ := Grothendieck.congr h₁
    have hf₂ := Grothendieck.congr h₂
    simp only [Grothendieck.comp_fiber, vert_fiber, vert_base, Functor.map_comp, eqToHom_map,
      Category.assoc, eqToHom_trans_assoc, cancel_epi] at hf₁ hf₂
    have := hG (m₀ : i ⟶ W.base)
    have hm : m₁ = m₁' := (hP.map (G.map (m₀ : i ⟶ W.base)).toFunctor).hom_ext hf₁ hf₂
    subst hm
    rfl

end Silmaril.Logic.Institution.GrothendieckPushout
