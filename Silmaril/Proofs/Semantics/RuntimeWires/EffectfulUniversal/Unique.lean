module

public import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulUniversal.Generation

public section

namespace Silmaril.RuntimeWires.Proofs.EffectfulUniversal

open CategoryTheory Diagram Presentation Position StrictEffectful.Assignment
open scoped MonoidalCategory SameArrow

universe u v u' v' u₁ v₁

private theorem boundary_injective {G : EffectfulPolygraph.{u₁,v₁}} :
    Function.Injective (Computations.boundary (G := G)) := by
  rintro ⟨A⟩ ⟨B⟩ h
  have e : none :: values A = none :: values B :=
    congrArg (fun X : Runtime G => X.word) h
  have c := congrArg eraseBoundary (List.cons.inj e).2
  rw [eraseBoundary_values, eraseBoundary_values] at c
  exact congrArg Computations.mk c

private theorem underlying_eq {G : EffectfulPolygraph.{u₁,v₁}}
    {A B X Y : Computations G} {f : A ⟶ B} {g : X ⟶ Y}
    {C : Type u'} [Category.{v'} C] (K : Computations G ⥤ C)
    (r : underlying f ≈ₐ underlying g) : K.map f ≈ₐ K.map g := by
  have hA := boundary_injective r.source
  have hB := boundary_injective r.target
  subst hA
  subst hB
  have e : f = g := r.eq
  exact SameArrow.of_eq (congrArg K.map e)

private theorem map_functor_eq {X : Type u} {C : Type u'} [Category.{v} X] [Category.{v'} C]
    {K L : X ⥤ C} (eq : K = L) {A B : X} (p : A ⟶ B) : K.map p ≈ₐ L.map p := by
  subst eq
  exact SameArrow.refl _

private theorem map_tensor {X : Type u} {C : Type u'} [Category.{v} X] [Category.{v'} C]
    [PremonoidalCategory X] [PremonoidalCategory C]
    (K : X ⥤ C) (h : IsStrictTensorFunctor K) {A B D E : X} (f : A ⟶ B) (g : D ⟶ E) :
    K.map (f ⊗ₘ g) ≈ₐ K.map f ⊗ₘ K.map g := by
  simp only [PremonoidalCategory.tensorHom_def, PremonoidalCategory.leftTensor, K.map_comp]
  exact (DiagramInterpretation.of_square (h.tensor A D) (h.tensor B D) (h.right f D)).comp
    (DiagramInterpretation.of_square (h.tensor B D) (h.tensor B E) (h.left B g))

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]
variable {T : StrictEffectful V C} {G : EffectfulPolygraph.{u₁,v₁}}

variable (F : T.Assignment G)
theorem wordObjects_of_sortObjects (H : (strictRuntime G).Hom T)
    (h : ∀ x : G.Obj, H.value.obj ⟨[x]⟩ = F.obj x) (X : Pure G) :
    H.value.obj X = StrictEffectful.wordObject F.obj X.word := by
  obtain ⟨A⟩ := X
  induction A with
  | nil => exact H.valueStrict.unit
  | cons x A ih =>
    exact (H.valueStrict.tensor ⟨[x]⟩ ⟨A⟩).trans (congrArg₂ (· ⊗ ·) (h x) ih)

variable {H K : (strictRuntime G).Hom T} (h : F.Extends H) (k : F.Extends K)
include h k

theorem value_unique : H.value = K.value :=
  (F.valuesInterpretation.uniqueExtension _ False.elim).unique h.values k.values

theorem computation_unique : H.computation = K.computation := by
  refine Functor.hext (fun X =>
    (F.computationObjects H h.values.objects X).trans
      (F.computationObjects K k.values.objects X).symm) ?_
  intro A B f
  have eq {A B : Computations G} {f : A ⟶ B} (gen : Generated f) :
      H.computation.map f ≈ₐ K.computation.map f := by
    induction gen with
    | id X =>
      rw [H.computation.map_id, K.computation.map_id]
      exact .id ((F.computationObjects H h.values.objects X).trans
        (F.computationObjects K k.values.objects X).symm)
    | effect e =>
      exact (DiagramInterpretation.of_square _ _ (h.effects e)).trans
        (DiagramInterpretation.of_square _ _ (k.effects e)).symm
    | pure p =>
      exact (map_functor_eq H.square p).trans
        ((DiagramInterpretation.map_congr T.pure (map_functor_eq (value_unique F h k) p)).trans
          (map_functor_eq K.square p).symm)
    | comp hf hg ihf ihg =>
      rw [Functor.map_comp, Functor.map_comp]
      exact ihf.comp ihg
    | tensor hf hg ihf ihg =>
      exact (map_tensor H.computation H.computationStrict _ _).trans
        ((ihf.tensor ihg).trans (map_tensor K.computation K.computationStrict _ _).symm)
    | related r hg ih =>
      exact (underlying_eq H.computation r).trans
        (ih.trans (underlying_eq K.computation r).symm)
  exact (eq (generated f)).arrow

theorem unique : H = K := by
  have hv := value_unique F h k
  have hc := computation_unique F h k
  cases H
  cases K
  cases hv
  cases hc
  rfl

end Silmaril.RuntimeWires.Proofs.EffectfulUniversal
