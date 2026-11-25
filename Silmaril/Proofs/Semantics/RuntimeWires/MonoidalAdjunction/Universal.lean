module

public import Silmaril.Semantics.RuntimeWires.MonoidalAdjunction.Unit
public import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulAdjunction.Forget

public section

namespace Silmaril.RuntimeWires.Proofs.MonoidalAdjunction

open CategoryTheory Diagram StrictEffectful StrictMonoidal
open scoped MonoidalCategory SameArrow

universe u v

variable {G : Polygraph.{u,max u v}} {X : StrictMonoidal.{u,v}}

private theorem restrict_edge_rel (F : terms G ⟶ X) (e : G.edges.Edge) :
    ((restrict F).edges.edge e).2.2 ≈ₐ F.1.map (generator e) := by
  let g := (generatorUnit G).edges.edge e
  have hg : g.2.2 ≈ₐ generator e :=
    DiagramInterpretation.transport_eq (termsWord _).symm (termsWord _).symm (generator e)
  exact (EffectfulAdjunction.effectArrow_rel (asEffectful.map F) g).trans
    (DiagramInterpretation.map_congr F.1 hg)

private theorem interpretation_edge_rel (f : G ⟶ forget.obj X) (e : G.edges.Edge) :
    (interpretation f).edge e ≈ₐ (f.edges.edge e).2.2 :=
  DiagramInterpretation.transport_eq (input f e) (output f e) (f.edges.edge e).2.2

private theorem restrict_objects (F : terms G ⟶ X) (A : List G.Obj) :
    F.1.obj ⟨A⟩ = (interpretation (restrict F)).obj A := by
  induction A with
  | nil => exact F.2.unit
  | cons x A ih =>
    exact (F.2.tensor ⟨[x]⟩ ⟨A⟩).trans (congrArg (F.1.obj ⟨[x]⟩ ⊗ ·) ih)

private theorem restrict_extends (F : terms G ⟶ X) :
    (interpretation (restrict F)).Extends (fun _ _ => False) F.1 where
  strict := F.2
  objects X := restrict_objects F X.word
  generators e :=
    ((restrict_edge_rel F e).symm.trans (interpretation_edge_rel (restrict F) e).symm).square
      (restrict_objects F _) (restrict_objects F _)

private theorem polygraph_hom_eq {A B : Polygraph.{u,v}} {f g : A ⟶ B} (h : f.obj = g.obj)
    (he : ∀ e, f.edges.edge e = g.edges.edge e) : f = g := by
  obtain ⟨a, ⟨e, hs, ht⟩⟩ := f
  obtain ⟨b, ⟨d, hs', ht'⟩⟩ := g
  cases h
  have eq : e = d := funext he
  cases eq
  rfl

private theorem restrict_of_extends {f : G ⟶ forget.obj X} {F : terms G ⟶ X}
    (h : (interpretation f).Extends (fun _ _ => False) F.1) : restrict F = f := by
  have ho : (restrict F).obj = f.obj := funext fun x =>
    (h.objects ⟨[x]⟩).trans (IsStrictTensor.rightObj (C := X.Object) (f.obj x))
  apply polygraph_hom_eq ho
  intro e
  have hs : ((restrict F).edges.edge e).1 = (f.edges.edge e).1 :=
    ((restrict F).edges.source e).trans
      ((congrArg (List.map · (G.edges.source e)) ho).trans (f.edges.source e).symm)
  have ht : ((restrict F).edges.edge e).2.1 = (f.edges.edge e).2.1 :=
    ((restrict F).edges.target e).trans
      ((congrArg (List.map · (G.edges.target e)) ho).trans (f.edges.target e).symm)
  exact EffectfulAdjunction.edge_eq hs ht ((restrict_edge_rel F e).trans
    ((DiagramInterpretation.of_square _ _ (h.generators e)).trans (interpretation_edge_rel f e)))

theorem restrict_left_inverse (F : terms G ⟶ X) :
    (interpretation (restrict F)).functor (fun _ _ => False) False.elim = F.1 :=
  ((interpretation (restrict F)).uniqueExtension _ False.elim).unique
    ((interpretation (restrict F)).functor_extends _ False.elim) (restrict_extends F)

theorem restrict_right_inverse (f : G ⟶ forget.obj X) :
    restrict (⟨(interpretation f).functor (fun _ _ => False) False.elim,
      ((interpretation f).functor_extends _ False.elim).strict⟩ : terms G ⟶ X) = f :=
  restrict_of_extends ((interpretation f).functor_extends _ False.elim)

end Silmaril.RuntimeWires.Proofs.MonoidalAdjunction
