module

public import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Isomorphism.Terms.Bridge
public import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Terms.Proofs

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args args' outs outs' : Ports (PortType V S)}
variable {past sigs sigs' : List (Ports (PortType V S))}

private def extendLabel (label : RVSDG.NodeLabel Op) : NodeLabel Op :=
  ⟨label.ins, label.outs, .base label.shape⟩

private def projectLabel : NodeLabel Op → Option (RVSDG.NodeLabel Op)
  | ⟨ins, outs, .base shape⟩ => some ⟨ins, outs, shape⟩
  | ⟨_, _, .theta _⟩ => none

private theorem extendLabel_injective {left right : RVSDG.NodeLabel Op}
    (same : extendLabel left = extendLabel right) : left = right :=
  have equal := congrArg projectLabel same
  Option.some.inj (show some left = some right from equal)

private theorem base_iso_aux (graph : RVSDG.Graph Op args past sigs outs) (fresh : past = [])
    (right : RVSDG.Graph Op args' [] sigs' outs') :
    RVSDG.Graph.Isomorphic Op (fresh ▸ graph) right ↔
      Graph.Isomorphic Op (Graph.ofBase (fresh ▸ graph)) (Graph.ofBase right) := by
  induction graph generalizing args' outs' sigs' with
  | @region args outs past sigs nodes children results ih =>
    subst past
    cases right with
    | region nodesR childrenR resultsR =>
      let left := RVSDG.Graph.region nodes children results
      let right := RVSDG.Graph.region nodesR childrenR resultsR
      change RVSDG.Graph.Isomorphic Op left right ↔
        Graph.Isomorphic Op (.ofBase left) (.ofBase right)
      constructor
      · intro iso
        cases iso with
        | intro entry exit ids labels inputs results sub =>
          have pairedLabels (i : Fin sigs.length) :
              ((Graph.ofBase left).nodes i).label = ((Graph.ofBase right).nodes (ids i)).label :=
            congrArg extendLabel (labels i)
          exact .intro entry exit ids pairedLabels inputs results
            (fun i arm => (ih i arm rfl _).1 (sub i arm))
      · intro iso
        generalize leftEq : Graph.ofBase left = lhs at iso
        generalize rightEq : Graph.ofBase right = rhs at iso
        cases iso with
        | intro entry exit ids labels inputs results sub =>
          subst lhs
          subst rhs
          have pairedLabels (i : Fin sigs.length) :
              (left.nodes i).label = (right.nodes (ids i)).label :=
            extendLabel_injective (labels i)
          exact .intro entry exit ids pairedLabels inputs results
            (fun i arm => (ih i arm rfl _).2 (sub i arm))

theorem base_iso (left : RVSDG.Graph Op args [] sigs outs) (right : RVSDG.Graph Op args' [] sigs' outs') :
    RVSDG.Graph.Isomorphic Op left right ↔ Graph.Isomorphic Op (.ofBase left) (.ofBase right) :=
  base_iso_aux left rfl right

private theorem ofBase_fromTable (nodes : RVSDG.Nodes Op args past sigs)
    (children : (i : Fin sigs.length) → RVSDG.Children (RVSDG.Term Op) (nodes i))
    (results : Wires args (extend past sigs) outs) :
    Term.ofBase (RVSDG.Term.fromTable past sigs nodes children results) =
      Term.fromTable past sigs (fun i => Node.ofBase (nodes i))
        (fun i j => Term.ofBase (children i j)) results := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih =>
    exact congrArg (Term.bind (Node.ofBase (nodes 0)) (fun j => Term.ofBase (children 0 j)))
      (ih (fun i => nodes i.succ) (fun i => children i.succ) results)

private theorem decode_ofBase (g : RVSDG.Graph Op args past sigs outs) :
    (Graph.ofBase g).toTerm = Term.ofBase g.toTerm := by
  induction g with
  | @region args outs past sigs nodes children results ih =>
    let mapped : Nodes Op args past sigs := fun i => Node.ofBase (nodes i)
    let decodeThenExtend : (i : Fin sigs.length) → Children (Term Op) (mapped i) :=
      fun i j => Term.ofBase (children i j).toTerm
    let extendThenDecode : (i : Fin sigs.length) → Children (Term Op) (mapped i) :=
      fun i j => (Graph.ofBase (children i j)).toTerm
    change Term.fromTable past sigs mapped extendThenDecode results = _
    have same : extendThenDecode = decodeThenExtend := funext fun i => funext (ih i)
    exact (congrArg (fun table => Term.fromTable past sigs mapped table results) same).trans
      (ofBase_fromTable nodes (fun i j => (children i j).toTerm) results).symm

theorem base_term_iso (left : RVSDG.Term Op args [] sigs outs) (right : RVSDG.Term Op args' [] sigs' outs') :
    RVSDG.Graph.Isomorphic Op left.toGraph right.toGraph ↔
      Term.Isomorphic Op (.ofBase left) (.ofBase right) := by
  have leftDecoded := (decode_ofBase left.toGraph).trans (congrArg Term.ofBase left.toTerm_toGraph)
  have rightDecoded := (decode_ofBase right.toGraph).trans (congrArg Term.ofBase right.toTerm_toGraph)
  rw [base_iso, decode_iff, leftDecoded, rightDecoded]

end Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Terms.Proofs
