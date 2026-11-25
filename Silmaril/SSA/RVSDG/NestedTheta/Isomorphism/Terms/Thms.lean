module

public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Terms.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Thms
public import Silmaril.SSA.RVSDG.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Isomorphism.Terms.Base

public section

namespace Silmaril.SSA.RVSDG.NestedTheta

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args args' outs outs' : Ports (PortType V S)}
variable {sigs sigs' : List (Ports (PortType V S))}

/-- Numbered graph isomorphism and renumbering of decoded binding spines agree. -/
theorem Graph.isomorphic_toTerm_iff (left : Graph Op args [] sigs outs) (right : Graph Op args' [] sigs' outs') :
    Term.Isomorphic Op left.toTerm right.toTerm ↔ Graph.Isomorphic Op left right :=
  (Isomorphism.Terms.Proofs.decode_iff left right).symm

theorem Term.isomorphic_toGraph_iff (left : Term Op args [] sigs outs) (right : Term Op args' [] sigs' outs') :
    Graph.Isomorphic Op left.toGraph right.toGraph ↔ Term.Isomorphic Op left right := by
  rw [← Graph.isomorphic_toTerm_iff, left.toTerm_toGraph, right.toTerm_toGraph]

/-- Check renumbering of primitive/γ binding spines via their inclusion in
the inductive nested language. -/
theorem Term.isomorphic_ofBase_toGraph_iff (left : RVSDG.Term Op args [] sigs outs)
    (right : RVSDG.Term Op args' [] sigs' outs') :
    RVSDG.Graph.Isomorphic Op left.toGraph right.toGraph ↔
      Term.Isomorphic Op (.ofBase left) (.ofBase right) :=
  Isomorphism.Terms.Proofs.base_term_iso left right

end Silmaril.SSA.RVSDG.NestedTheta
