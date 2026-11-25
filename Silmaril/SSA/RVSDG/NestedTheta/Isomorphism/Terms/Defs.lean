module

public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs

/-! Typed endpoint renumbering read directly from inductive bodies. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args args' outs outs' : Ports (PortType V S)}
variable {past past' sigs sigs' : List (Ports (PortType V S))}

abbrev Binding (Op : Dialect.{u, v} V S) (args : Ports (PortType V S))
    (past : List (Ports (PortType V S))) (outs : Ports (PortType V S)) :=
  Σ node : Node Op args past outs, Children (Term Op) node

/-- Read the binding at a position directly from the term, keeping its
original inputs and child terms. -/
def Term.bindingAt :
    {past sigs : List (Ports (PortType V S))} → Term Op args past sigs outs →
    (i : Fin sigs.length) → Binding Op args (site past sigs i).1 (site past sigs i).2
  | _, _, .ret _, i => i.elim0
  | _, _, .bind node children rest, i => Fin.cases ⟨node, children⟩ rest.bindingAt i

def Term.resultWires :
    {past sigs : List (Ports (PortType V S))} → Term Op args past sigs outs →
    Wires args (extend past sigs) outs
  | _, _, .ret wires => wires
  | _, _, .bind _ _ rest => rest.resultWires

mutual

/-- The binding spines choose a vertex map at each region. Both terms
supply their own typed endpoints, labels and children. -/
inductive Term.Isomorphic (Op : Dialect.{u, v} V S) :
    {args args' outs outs' : Ports (PortType V S)} → {sigs sigs' : List (Ports (PortType V S))} →
    Term Op args [] sigs outs → Term Op args' [] sigs' outs' → Prop where
  | intro {args args' outs outs' : Ports (PortType V S)} {sigs sigs' : List (Ports (PortType V S))}
      {left : Term Op args [] sigs outs} {right : Term Op args' [] sigs' outs'}
      (entry : args = args') (exit : outs = outs')
      (ids : Fin sigs.length ≃ Fin sigs'.length)
      (bindings : ∀ i, Binding.Renumbered Op (renameVertex ids)
        (left.bindingAt i) (right.bindingAt (ids i)))
      (results : left.resultWires.addresses.map (Address.rename (renameVertex ids)) =
        right.resultWires.addresses) :
      Term.Isomorphic Op left right

/-- A paired binding preserves the node kind, input origins and positional
children. Each child has its own binding-spine isomorphism. -/
inductive Binding.Renumbered (Op : Dialect.{u, v} V S) : (ids : Nat → Nat) →
    {args args' outs outs' : Ports (PortType V S)} → {past past' : List (Ports (PortType V S))} →
    Binding Op args past outs → Binding Op args' past' outs' → Prop where
  | intro {ids : Nat → Nat} {args args' outs outs' : Ports (PortType V S)}
      {past past' : List (Ports (PortType V S))}
      {left : Binding Op args past outs} {right : Binding Op args' past' outs'}
      (labels : left.1.label = right.1.label)
      (inputs : left.1.inputs.addresses.map (Address.rename ids) = right.1.inputs.addresses)
      (children : ∀ arm, Term.Isomorphic Op (left.2 arm)
        (right.2 (Fin.cast (congrArg NodeLabel.arity labels) arm))) :
      Binding.Renumbered Op ids left right

end

end Silmaril.SSA.RVSDG.NestedTheta
