module

public import Silmaril.Semantics.RuntimeWires.EffectfulAdjunction.Unit
public import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulAdjunction.Forget

public section

namespace Silmaril.RuntimeWires.Proofs.EffectfulAdjunction

open CategoryTheory Diagram Presentation StrictEffectful Bundled
open scoped MonoidalCategory SameArrow

universe u v

variable {G : EffectfulPolygraph.{u,max u v}} {X : Bundled.{u,v}}

private theorem pure_restrict_rel (H : Bundled.runtime G ⟶ X) (e : G.pure.Edge) :
    ((restrict H).pure.edge e).2.2 ≈ₐ H.value.map (pureGenerator e) := by
  let g := (generatorUnit G).pure.edge e
  have h : g.2.2 ≈ₐ pureGenerator e := DiagramInterpretation.transport_eq (runtimeWord _).symm (runtimeWord _).symm (pureGenerator e)
  exact (pureArrow_rel H g).trans (DiagramInterpretation.map_congr H.value h)

private theorem effect_restrict_rel (H : Bundled.runtime G ⟶ X) (e : G.effect.Edge) :
    ((restrict H).effect.edge e).2.2 ≈ₐ H.computation.map (effectGenerator G e) := by
  let g := (generatorUnit G).effect.edge e
  have h : g.2.2 ≈ₐ effectGenerator G e := DiagramInterpretation.transport_eq
    (congrArg (Bundled.runtime G).model.pure.obj (runtimeWord _)).symm
    (congrArg (Bundled.runtime G).model.pure.obj (runtimeWord _)).symm (effectGenerator G e)
  exact (effectArrow_rel H g).trans (DiagramInterpretation.map_congr H.computation h)

private theorem pure_assignment_rel (f : G ⟶ X.polygraph) (e : G.pure.Edge) :
    (assignment f).pure e ≈ₐ (f.pure.edge e).2.2 :=
  DiagramInterpretation.transport_eq
    ((congrArg (wordObject (id : X.Value → X.Value)) (f.pure.source e)).trans (wordImage_map f.obj _))
    ((congrArg (wordObject (id : X.Value → X.Value)) (f.pure.target e)).trans (wordImage_map f.obj _))
    (f.pure.edge e).2.2

private theorem effect_assignment_rel (f : G ⟶ X.polygraph) (e : G.effect.Edge) :
    (assignment f).effect e ≈ₐ (f.effect.edge e).2.2 :=
  DiagramInterpretation.transport_eq
    ((congrArg (X.model.pure.obj ∘ wordObject id) (f.effect.source e)).trans
      (congrArg X.model.pure.obj (wordImage_map f.obj _)))
    ((congrArg (X.model.pure.obj ∘ wordObject id) (f.effect.target e)).trans
      (congrArg X.model.pure.obj (wordImage_map f.obj _)))
    (f.effect.edge e).2.2

theorem restrict_extends (H : Bundled.runtime G ⟶ X) : (assignment (restrict H)).Extends H := by
  let F := assignment (restrict H)
  have hobj := F.wordObjects_of_sortObjects H (fun _ => rfl)
  refine ⟨⟨H.valueStrict, hobj, ?_⟩, ?_⟩
  · intro e
    exact (((pure_restrict_rel H e).symm.trans (pure_assignment_rel (restrict H) e).symm)).square
      (hobj ⟨G.pure.source e⟩) (hobj ⟨G.pure.target e⟩)
  · intro e
    exact (((effect_restrict_rel H e).symm.trans (effect_assignment_rel (restrict H) e).symm)).square
      (F.computationObjects H hobj ⟨G.effect.source e⟩)
      (F.computationObjects H hobj ⟨G.effect.target e⟩)

theorem restrict_of_extends {H : Bundled.runtime G ⟶ X} {f : G ⟶ X.polygraph}
    (h : (assignment f).Extends H) : restrict H = f := by
  have hobj : (restrict H).obj = f.obj := funext fun x =>
    (h.values.objects ⟨[x]⟩).trans (IsStrictTensor.rightObj (C := X.Value) (f.obj x))
  apply hom_eq hobj
  · intro e
    have hp : ((restrict H).pure.edge e).1 = (f.pure.edge e).1 :=
      ((restrict H).pure.source e).trans ((congrArg (List.map · (G.pure.source e)) hobj).trans (f.pure.source e).symm)
    have hq : ((restrict H).pure.edge e).2.1 = (f.pure.edge e).2.1 :=
      ((restrict H).pure.target e).trans ((congrArg (List.map · (G.pure.target e)) hobj).trans (f.pure.target e).symm)
    exact edge_eq hp hq ((pure_restrict_rel H e).trans
      ((DiagramInterpretation.of_square _ _ (h.values.generators e)).trans
        (pure_assignment_rel f e)))
  · intro e
    have hp : ((restrict H).effect.edge e).1 = (f.effect.edge e).1 :=
      ((restrict H).effect.source e).trans ((congrArg (List.map · (G.effect.source e)) hobj).trans (f.effect.source e).symm)
    have hq : ((restrict H).effect.edge e).2.1 = (f.effect.edge e).2.1 :=
      ((restrict H).effect.target e).trans ((congrArg (List.map · (G.effect.target e)) hobj).trans (f.effect.target e).symm)
    exact edge_eq hp hq ((effect_restrict_rel H e).trans
      ((DiagramInterpretation.of_square _ _ (h.effects e)).trans
        (effect_assignment_rel f e)))

theorem restriction_left_inverse (H : Bundled.runtime G ⟶ X) :
    (assignment (restrict H)).extension = H :=
  (Assignment.uniqueExtension (assignment (restrict H))).unique
    (Assignment.extension_extends (assignment (restrict H))) (restrict_extends H)

theorem restriction_right_inverse (f : G ⟶ X.polygraph) :
    restrict (assignment f).extension = f :=
  restrict_of_extends (Assignment.extension_extends (assignment f))

end Silmaril.RuntimeWires.Proofs.EffectfulAdjunction
