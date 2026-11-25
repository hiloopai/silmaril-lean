module

public import Silmaril.Semantics.RuntimeWires.EffectfulAdjunction.ForgetMap
public import Silmaril.Proofs.Semantics.RuntimeWires.DiagramInterpretation.Basic

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.EffectfulAdjunction

open CategoryTheory Diagram StrictEffectful Bundled
open scoped MonoidalCategory SameArrow

universe u v

theorem pureArrow_rel {X Y : Bundled.{u,v}} (H : X ⟶ Y) (e : X.polygraph.pure.Edge) :
    pureArrow H e ≈ₐ H.value.map e.2.2 :=
  DiagramInterpretation.transport_eq _ _ _

theorem effectArrow_rel {X Y : Bundled.{u,v}} (H : X ⟶ Y) (e : X.polygraph.effect.Edge) :
    effectArrow H e ≈ₐ H.computation.map e.2.2 :=
  DiagramInterpretation.transport_eq _ _ _

theorem edge_eq {V C : Type u} [Category.{max u v} C] {obj : List V → C}
    {a b : (wordSignature obj).Edge} (p : a.1 = b.1) (q : a.2.1 = b.2.1)
    (r : a.2.2 ≈ₐ b.2.2) : a = b := by
  obtain ⟨A, B, f⟩ := a
  obtain ⟨A', B', g⟩ := b
  cases p
  cases q
  cases r.eq
  rfl

theorem hom_eq {A B : EffectfulPolygraph.{u,v}} {f g : A ⟶ B} (h : f.obj = g.obj)
    (hp : ∀ e, f.pure.edge e = g.pure.edge e)
    (he : ∀ e, f.effect.edge e = g.effect.edge e) : f = g := by
  obtain ⟨a, ⟨p, hp₁, hp₂⟩, ⟨e, he₁, he₂⟩⟩ := f
  obtain ⟨b, ⟨q, hq₁, hq₂⟩, ⟨f, hf₁, hf₂⟩⟩ := g
  cases h
  have h₁ : p = q := funext hp
  have h₂ : e = f := funext he
  cases h₁
  cases h₂
  rfl

theorem forget_id (X : Bundled.{u,v}) : forgetMap (𝟙 X) = 𝟙 X.polygraph :=
  hom_eq rfl
    (fun e => edge_eq (List.map_id _) (List.map_id _) (pureArrow_rel (𝟙 X) e))
    (fun e => edge_eq (List.map_id _) (List.map_id _) (effectArrow_rel (𝟙 X) e))

theorem forget_comp {X Y Z : Bundled.{u,v}} (H : X ⟶ Y) (K : Y ⟶ Z) :
    forgetMap (H ≫ K) = forgetMap H ≫ forgetMap K := by
  refine hom_eq (f := forgetMap (H ≫ K)) (g := forgetMap H ≫ forgetMap K) rfl ?_ ?_
  · intro e
    refine edge_eq ?_ ?_ ?_
    · change e.1.map (K.value.obj ∘ H.value.obj) = (e.1.map H.value.obj).map K.value.obj
      exact List.map_map.symm
    · change e.2.1.map (K.value.obj ∘ H.value.obj) = (e.2.1.map H.value.obj).map K.value.obj
      exact List.map_map.symm
    · exact (pureArrow_rel (H ≫ K) e).trans
        ((DiagramInterpretation.map_congr K.value (pureArrow_rel H e)).symm.trans
          (pureArrow_rel K ((forgetMap H).pure.edge e)).symm)
  · intro e
    refine edge_eq ?_ ?_ ?_
    · change e.1.map (K.value.obj ∘ H.value.obj) = (e.1.map H.value.obj).map K.value.obj
      exact List.map_map.symm
    · change e.2.1.map (K.value.obj ∘ H.value.obj) = (e.2.1.map H.value.obj).map K.value.obj
      exact List.map_map.symm
    · exact (effectArrow_rel (H ≫ K) e).trans
        ((DiagramInterpretation.map_congr K.computation (effectArrow_rel H e)).symm.trans
          (effectArrow_rel K ((forgetMap H).effect.edge e)).symm)

end Silmaril.RuntimeWires.Proofs.EffectfulAdjunction
