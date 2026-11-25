module

public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Terms.Defs

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Terms.Proofs

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args args' outs outs' : Ports (PortType V S)}
variable {past sigs sigs' : List (Ports (PortType V S))}

private theorem bindingAt_fromTable (nodes : Nodes Op args past sigs)
    (children : (i : Fin sigs.length) → Children (Term Op) (nodes i))
    (results : Wires args (extend past sigs) outs) (i : Fin sigs.length) :
    (Term.fromTable past sigs nodes children results).bindingAt i = ⟨nodes i, children i⟩ := by
  induction sigs generalizing past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih (fun k => nodes k.succ) (fun k => children k.succ) results j

private theorem results_fromTable (nodes : Nodes Op args past sigs)
    (children : (i : Fin sigs.length) → Children (Term Op) (nodes i))
    (results : Wires args (extend past sigs) outs) :
    (Term.fromTable past sigs nodes children results).resultWires = results := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih => exact ih (fun j => nodes j.succ) (fun j => children j.succ) results

private theorem decode_bindingAt (graph : Graph Op args past sigs outs) (i : Fin sigs.length) :
    graph.toTerm.bindingAt i = ⟨graph.nodes i, fun j => (graph.children i j).toTerm⟩ := by
  cases graph with
  | region nodes children results => exact bindingAt_fromTable nodes (fun i j => (children i j).toTerm) results i

private theorem decode_resultWires (graph : Graph Op args past sigs outs) :
    graph.toTerm.resultWires = graph.results := by
  cases graph with
  | region nodes children results => exact results_fromTable nodes (fun i j => (children i j).toTerm) results

private theorem decode_iff_aux (graph : Graph Op args past sigs outs) (fresh : past = [])
    (right : Graph Op args' [] sigs' outs') :
    Graph.Isomorphic Op (fresh ▸ graph) right ↔ Term.Isomorphic Op (fresh ▸ graph).toTerm right.toTerm := by
  induction graph generalizing args' outs' sigs' with
  | @region args outs past sigs nodes children results ih =>
    subst past
    let left := Graph.region nodes children results
    change Graph.Isomorphic Op left right ↔ Term.Isomorphic Op left.toTerm right.toTerm
    constructor
    · intro related
      cases related with
      | intro entry exit ids labels inputs results sub =>
        refine .intro entry exit ids (fun i => ?_) ?_
        · rw [decode_bindingAt, decode_bindingAt]
          exact .intro (labels i) (inputs i) (fun arm => (ih i arm rfl _).1 (sub i arm))
        · rw [decode_resultWires, decode_resultWires]
          exact results
    · intro related
      cases related with
      | intro entry exit ids bindings results =>
        have vertex (i : Fin sigs.length) :
            ∃ label : (left.nodes i).label = (right.nodes (ids i)).label,
              (left.nodes i).inputs.addresses.map (Address.rename (renameVertex ids)) =
                (right.nodes (ids i)).inputs.addresses ∧
              ∀ arm, Term.Isomorphic Op (left.children i arm).toTerm
                (right.children (ids i) (Fin.cast (congrArg NodeLabel.arity label) arm)).toTerm := by
          have h := bindings i
          rw [decode_bindingAt, decode_bindingAt] at h
          cases h with
          | intro label inputs sub => exact ⟨label, inputs, sub⟩
        let labels := fun i => (vertex i).choose
        refine .intro entry exit ids labels (fun i => (vertex i).choose_spec.1) ?_ ?_
        · rw [decode_resultWires, decode_resultWires] at results
          exact results
        · intro i arm
          exact (ih i arm rfl _).2 ((vertex i).choose_spec.2 arm)

theorem decode_iff (left : Graph Op args [] sigs outs) (right : Graph Op args' [] sigs' outs') :
    Graph.Isomorphic Op left right ↔ Term.Isomorphic Op left.toTerm right.toTerm :=
  decode_iff_aux left rfl right

end Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Terms.Proofs
