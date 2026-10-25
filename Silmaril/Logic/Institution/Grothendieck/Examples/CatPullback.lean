module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

/-!
# Strict pullbacks in `Cat`

A commuting square of functors

```
P --G₁--> X₁
|         |
G₂        F₁
v         v
X₂ --F₂--> X
```

is a pullback in `Cat` (a *strict* pullback of categories) as soon as objects and morphisms
amalgamate uniquely: any `x₁`, `x₂` with `F₁ x₁ = F₂ x₂` come from exactly one object of `P`, and
any two morphisms `u₁`, `u₂` between the images of `p, p'` whose images under `F₁` and `F₂` agree
come from exactly one morphism `p ⟶ p'`. This is the form in which model amalgamation is proved
for concrete institutions (`Silmaril.Logic.Institution.Grothendieck.Examples.PLEQ`).

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §3, Definition 3.10
(semi-exactness asks the model functor to take pushouts to pullbacks in `Cat`).
-/

namespace Silmaril.Logic.Institution.CatPullback

open CategoryTheory Limits

universe v u

section Functors

/-- Conjugating by `eqToHom`s does not change a morphism up to `HEq`. -/
theorem conj_eqToHom_heq {C : Type u} [Category.{v} C] {W X W' X' : C} (f : W ⟶ X) (h : W' = W)
    (h' : X = X') : eqToHom h ≫ f ≫ eqToHom h' ≍ f := by
  subst h h'
  simp

variable {P X₁ X₂ X : Type u} [Category.{v} P] [Category.{v} X₁] [Category.{v} X₂]
  [Category.{v} X] {G₁ : P ⥤ X₁} {G₂ : P ⥤ X₂} {F₁ : X₁ ⥤ X} {F₂ : X₂ ⥤ X}

/-- Unique amalgamation of objects. -/
def ObjAmalgamation (G₁ : P ⥤ X₁) (G₂ : P ⥤ X₂) (F₁ : X₁ ⥤ X) (F₂ : X₂ ⥤ X) : Prop :=
  ∀ (x₁ : X₁) (x₂ : X₂), F₁.obj x₁ = F₂.obj x₂ → ∃! p : P, G₁.obj p = x₁ ∧ G₂.obj p = x₂

/-- Unique amalgamation of morphisms. -/
def MapAmalgamation (G₁ : P ⥤ X₁) (G₂ : P ⥤ X₂) (F₁ : X₁ ⥤ X) (F₂ : X₂ ⥤ X) : Prop :=
  ∀ {p p' : P} (u₁ : G₁.obj p ⟶ G₁.obj p') (u₂ : G₂.obj p ⟶ G₂.obj p'),
    F₁.map u₁ ≍ F₂.map u₂ → ∃! u : p ⟶ p', G₁.map u = u₁ ∧ G₂.map u = u₂

variable (w : G₁ ⋙ F₁ = G₂ ⋙ F₂) (hobj : ObjAmalgamation G₁ G₂ F₁ F₂)
  (hmap : MapAmalgamation G₁ G₂ F₁ F₂)

include w hobj hmap in
/-- Functors into `P` are determined by their composites with `G₁` and `G₂`. -/
theorem functor_ext {C : Type u} [Category.{v} C] {L L' : C ⥤ P} (h₁ : L ⋙ G₁ = L' ⋙ G₁)
    (h₂ : L ⋙ G₂ = L' ⋙ G₂) : L = L' := by
  have hobj' : ∀ c, L.obj c = L'.obj c := fun c =>
    (hobj (G₁.obj (L.obj c)) (G₂.obj (L.obj c)) (Functor.congr_obj w (L.obj c))).unique
      ⟨rfl, rfl⟩ ⟨(Functor.congr_obj h₁ c).symm, (Functor.congr_obj h₂ c).symm⟩
  refine CategoryTheory.Functor.ext hobj' fun c c' u => ?_
  have hu := hmap (G₁.map (L.map u)) (G₂.map (L.map u)) (Functor.hcongr_hom w (L.map u))
  refine hu.unique (y₁ := L.map u) ⟨rfl, rfl⟩ ⟨?_, ?_⟩
  · have := Functor.congr_hom h₁ u
    simp only [Functor.comp_map] at this
    simp [this, eqToHom_map]
  · have := Functor.congr_hom h₂ u
    simp only [Functor.comp_map] at this
    simp [this, eqToHom_map]

variable {C : Type u} [Category.{v} C] (H₁ : C ⥤ X₁) (H₂ : C ⥤ X₂) (h : H₁ ⋙ F₁ = H₂ ⋙ F₂)

include hobj hmap h in
/-- Existence of the lift of a commuting square of functors. -/
theorem exists_lift : ∃ L : C ⥤ P, L ⋙ G₁ = H₁ ∧ L ⋙ G₂ = H₂ := by
  have ho : ∀ c, ∃! p : P, G₁.obj p = H₁.obj c ∧ G₂.obj p = H₂.obj c := fun c =>
    hobj _ _ (Functor.congr_obj h c)
  choose L e using fun c => (ho c).exists
  have hm : ∀ {c c' : C} (u : c ⟶ c'), ∃! v : L c ⟶ L c',
      G₁.map v = eqToHom (e c).1 ≫ H₁.map u ≫ eqToHom (e c').1.symm ∧
      G₂.map v = eqToHom (e c).2 ≫ H₂.map u ≫ eqToHom (e c').2.symm := by
    intro c c' u
    refine hmap _ _ ?_
    simp only [Functor.map_comp, eqToHom_map]
    exact (conj_eqToHom_heq _ _ _).trans
      ((Functor.hcongr_hom h u).trans (conj_eqToHom_heq _ _ _).symm)
  choose Lm hLm using fun (c c' : C) (u : c ⟶ c') => (hm u).exists
  refine ⟨{ obj := L, map := fun {c c'} u => Lm c c' u, map_id := ?_, map_comp := ?_ }, ?_, ?_⟩
  · intro c
    exact ((hm (𝟙 c)).unique (hLm c c (𝟙 c)) ⟨by simp, by simp⟩)
  · intro c c' c'' u u'
    refine (hm (u ≫ u')).unique (hLm c c'' (u ≫ u')) ⟨?_, ?_⟩
    · simp [(hLm c c' u).1, (hLm c' c'' u').1]
    · simp [(hLm c c' u).2, (hLm c' c'' u').2]
  · exact CategoryTheory.Functor.ext (fun c => (e c).1) fun c c' u => (hLm c c' u).1
  · exact CategoryTheory.Functor.ext (fun c => (e c).2) fun c c' u => (hLm c c' u).2

end Functors

/-- A commuting square in `Cat` with unique amalgamation of objects and of morphisms is a
pullback.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §3, Definition 3.10
(PDF page 10), the pullbacks in `Cat` of semi-exactness. -/
theorem isPullback_of_amalgamation {P X₁ X₂ X : Cat.{v, u}} {G₁ : P ⟶ X₁} {G₂ : P ⟶ X₂}
    {F₁ : X₁ ⟶ X} {F₂ : X₂ ⟶ X} (w : G₁ ≫ F₁ = G₂ ≫ F₂)
    (hobj : ObjAmalgamation G₁.toFunctor G₂.toFunctor F₁.toFunctor F₂.toFunctor)
    (hmap : MapAmalgamation G₁.toFunctor G₂.toFunctor F₁.toFunctor F₂.toFunctor) :
    IsPullback G₁ G₂ F₁ F₂ := by
  have w' : G₁.toFunctor ⋙ F₁.toFunctor = G₂.toFunctor ⋙ F₂.toFunctor :=
    congrArg Cat.Hom.toFunctor w
  have hl : ∀ s : PullbackCone F₁ F₂, ∃ L : s.pt ⥤ P,
      L ⋙ G₁.toFunctor = s.fst.toFunctor ∧ L ⋙ G₂.toFunctor = s.snd.toFunctor := fun s =>
    exists_lift hobj hmap _ _ (congrArg Cat.Hom.toFunctor s.condition)
  choose L hL₁ hL₂ using hl
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w
    (fun s => Cat.Hom.ofFunctor (L s)) (fun s => Cat.Hom.ext (hL₁ s))
    (fun s => Cat.Hom.ext (hL₂ s)) fun s m h₁ h₂ => Cat.Hom.ext ?_)
  exact functor_ext w' hobj hmap ((congrArg Cat.Hom.toFunctor h₁).trans (hL₁ s).symm)
    ((congrArg Cat.Hom.toFunctor h₂).trans (hL₂ s).symm)

end Silmaril.Logic.Institution.CatPullback
