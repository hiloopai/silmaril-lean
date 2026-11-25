module

public import Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Terms.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Proofs

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args args' outs outs' : Ports (Ty V S)}
variable {past past' sigs sigs' : List (Ports (Ty V S))}

theorem lambda_toGraph {fn : Function V S} (ids : Nat → Nat)
    (left : LambdaTerm Op args past fn) (right : LambdaTerm Op args' past' fn) :
    left.toGraph.Renumbered ids right.toGraph ↔ left.Renumbered ids right := by
  simp only [Lambda.Renumbered, LambdaTerm.Renumbered, LambdaTerm.toGraph,
    NestedTheta.Term.isomorphic_toGraph_iff]

theorem delta_toGraph {value : ValueSort V S} (ids : Nat → Nat)
    (left : DeltaTerm Op args past value) (right : DeltaTerm Op args' past' value) :
    left.toGraph.Renumbered ids right.toGraph ↔ left.Renumbered ids right := by
  simp only [Delta.Renumbered, DeltaTerm.Renumbered, DeltaTerm.toGraph,
    NestedTheta.Term.isomorphic_ofBase_toGraph_iff]

theorem phi_toGraph {members : List (Function V S)} (ids : Nat → Nat)
    (left : PhiTerm Op args past members) (right : PhiTerm Op args' past' members) :
    left.toGraph.Renumbered ids right.toGraph ↔ left.Renumbered ids right := by
  constructor
  · rintro ⟨captures, definitions⟩
    exact ⟨captures, fun i => (lambda_toGraph id _ _).1 (definitions i)⟩
  · rintro ⟨captures, definitions⟩
    exact ⟨captures, fun i => (lambda_toGraph id _ _).2 (definitions i)⟩

private theorem vertex_roundtrip (vertex : VertexTerm Op args past outs) : vertex.toGraph.toTerm = vertex := by
  cases vertex with
  | lambda term => exact congrArg VertexTerm.lambda term.toTerm_toGraph
  | delta term => exact congrArg VertexTerm.delta term.toTerm_toGraph
  | phi term => exact congrArg VertexTerm.phi term.toTerm_toGraph

private theorem vertex_toTerm {ids : Nat → Nat} {left : Vertex Op args past outs}
    {right : Vertex Op args' past' outs'} (related : Vertex.Renumbered Op ids left right) :
    VertexTerm.Renumbered Op ids left.toTerm right.toTerm := by
  cases related with
  | @lambda fn left right related =>
    apply VertexTerm.Renumbered.lambda
    apply (lambda_toGraph ids left.toTerm right.toTerm).1
    rwa [left.toGraph_toTerm, right.toGraph_toTerm]
  | @delta value left right related =>
    apply VertexTerm.Renumbered.delta
    apply (delta_toGraph ids left.toTerm right.toTerm).1
    rwa [left.toGraph_toTerm, right.toGraph_toTerm]
  | @phi members left right related =>
    apply VertexTerm.Renumbered.phi
    apply (phi_toGraph ids left.toTerm right.toTerm).1
    rwa [left.toGraph_toTerm, right.toGraph_toTerm]

theorem vertex_toGraph (ids : Nat → Nat)
    (left : VertexTerm Op args past outs) (right : VertexTerm Op args' past' outs') :
    Vertex.Renumbered Op ids left.toGraph right.toGraph ↔ VertexTerm.Renumbered Op ids left right := by
  constructor
  · intro related
    simpa only [vertex_roundtrip] using vertex_toTerm related
  · intro related
    cases related with
    | lambda h => exact .lambda ((lambda_toGraph ids _ _).2 h)
    | delta h => exact .delta ((delta_toGraph ids _ _).2 h)
    | phi h => exact .phi ((phi_toGraph ids _ _).2 h)

theorem bindingAt_toGraph (term : ModuleTerm Op args past sigs outs) (i : Fin sigs.length) :
    (term.bindingAt i).toGraph = term.vertices i := by
  induction term with
  | ret => exact i.elim0
  | bind definition rest ih => exact Fin.cases rfl (fun j => ih j) i

theorem omega_toGraph (left : OmegaTerm Op args outs sigs) (right : OmegaTerm Op args outs sigs')
    (ids : Fin sigs.length ≃ Fin sigs'.length) :
    left.toGraph.RenumberedBy right.toGraph ids ↔ left.RenumberedBy right ids := by
  constructor
  · intro related
    refine ⟨fun i => ?_, related.exports⟩
    apply (vertex_toGraph (renameVertex ids) _ _).1
    rw [bindingAt_toGraph, bindingAt_toGraph]
    exact related.vertices i
  · intro related
    refine ⟨fun i => ?_, related.exports⟩
    have wire := (vertex_toGraph (renameVertex ids) _ _).2 (related.bindings i)
    rw [bindingAt_toGraph, bindingAt_toGraph] at wire
    exact wire

private def addressProducer : Address → Option Nat
  | .arg _ => none
  | .output i _ => some i

theorem phi_number_eq {members : List (Function V S)}
    (left : Phi Op args past members) (right : Phi Op args' past' members)
    (ids : Fin members.length ≃ Fin members.length)
    (preservesResults : ∀ i, Address.rename (renameVertex ids) (left.resultOrigin i).address =
      (right.resultOrigin i).address) (i : Fin members.length) : ids i = i := by
  apply Fin.ext
  have equal := congrArg addressProducer (preservesResults i)
  change some (renameVertex ids i.val) = some i.val at equal
  simpa only [renameVertex, dite_eq_left i.isLt, Option.some.injEq] using equal

end Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Proofs
