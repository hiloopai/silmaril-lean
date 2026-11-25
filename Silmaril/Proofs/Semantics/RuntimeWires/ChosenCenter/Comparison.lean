module

public import Silmaril.Semantics.RuntimeWires.ChosenCenter.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.DiagramInterpretation.Basic

public section

namespace Silmaril.RuntimeWires.Proofs.ChosenCenter

open CategoryTheory PremonoidalCategory StrictEffectful
open scoped SameArrow

universe u v u' v' u₁ v₁ u₂ v₂

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]
variable (S : StrictEffectful V C)

theorem obj_bijective : Function.Bijective S.toCenter.obj :=
  ⟨fun _ _ h => S.objects.1 (congrArg WideSubcategory.obj h),
    fun ⟨x⟩ => by
      obtain ⟨y, hy⟩ := S.objects.2 x
      exact ⟨y, congrArg WideSubcategory.mk hy⟩⟩

theorem full_iff_exhausts : S.toCenter.Full ↔ S.ExhaustsCenter := by
  constructor
  · intro h X Y f hf
    obtain ⟨p, hp⟩ := h.map_surjective (X := X) (Y := Y) ⟨f, hf⟩
    exact ⟨p, congrArg (fun g => g.hom) hp⟩
  · intro h
    constructor
    intro X Y f
    obtain ⟨p, hp⟩ := h f.hom f.property
    exact ⟨p, WideSubcategory.hom_ext (PremonoidalCategory.central C) hp⟩

theorem faithful_iff : S.toCenter.Faithful ↔ S.pure.Faithful := by
  constructor
  · intro h
    constructor
    intro X Y f g e
    exact h.map_injective (WideSubcategory.hom_ext (PremonoidalCategory.central C) e)
  · intro h
    constructor
    intro X Y f g e
    exact h.map_injective (congrArg (fun g => g.hom) e)

private theorem central_congr {D : Type u₂} [Category.{v₂} D] [PremonoidalCategory D]
    {A B X Y : D} {f : A ⟶ B} {g : X ⟶ Y} (e : f ≈ₐ g) (h : IsCentral g) : IsCentral f := by
  obtain ⟨rfl, rfl, e⟩ := e
  exact (eq_of_heq e).symm ▸ h

private theorem same_map {A : Type u} {B : Type u₂} [Category.{v} A] [Category.{v₂} B]
    {F G : A ⥤ B} (e : F = G) {X Y : A} (f : X ⟶ Y) : F.map f ≈ₐ G.map f := by
  cases e
  exact SameArrow.refl _

variable {W : Type u₁} {D : Type u₂} [Category.{v₁} W] [Category.{v₂} D]
variable [MonoidalCategory W] [PremonoidalCategory D] [IsStrictTensor W] [IsStrictTensor D]
variable {T : StrictEffectful W D}

theorem preserves_central (H : S.Hom T) (h : S.ExhaustsCenter)
    {A B : C} (f : A ⟶ B) (hf : IsCentral f) : IsCentral (H.computation.map f) := by
  obtain ⟨X, rfl⟩ := S.objects.2 A
  obtain ⟨Y, rfl⟩ := S.objects.2 B
  obtain ⟨p, rfl⟩ := h f hf
  exact central_congr (same_map H.square p) (T.central (H.value.map p))

end Silmaril.RuntimeWires.Proofs.ChosenCenter
