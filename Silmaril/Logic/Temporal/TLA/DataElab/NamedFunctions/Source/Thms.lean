module

public import Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Source.Defs
public import Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Thms
import Silmaril.Proofs.Logic.Temporal.TLA.DataElab.NamedFunctions.Source

public section

namespace Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Source

open Data Data.Tagged

universe u

/-- The resolved subtraction at every positive key stays inside the declared
interval and strictly decreases the key. -/
theorem predecessor_key (policy : Tagged.Policy.{u}) (sequence : SequencePolicy.{u})
    (n : Nat) (i : Int) (hi : 0 < i) (hn : i ≤ n) :
    let key := (Sequences.external policy sequence subId 2 (by decide)).apply [.integer i, .integer 1]
    key = .integer (i - 1) ∧ (SetData.intRange.{u} 0 n).mem key ∧ i - 1 < i :=
  Proofs.predecessor_key policy sequence n i hi hn

/-- Evaluate the admitted source term as the reference CHOOSE equation followed
by the original IN expression. The complete predicate agrees for every candidate. -/
theorem CheckedVMem.eval_eq_choose_apply_len (checked : CheckedVMem) (policy : Tagged.Policy.{u})
    (invalid : Tagged.CollectionPolicy.{u}) (sequence : SequencePolicy.{u})
    (graph : Unspecified.{u}) (endpoints : Endpoints.EndpointValuation Value.{u})
    (entries : List Value.{u}) (queue : endpoints.source checked.predecessor.queue = .tuple entries) :
    checked.eval policy invalid sequence graph endpoints =
      (policy.choice.choose ((vmemDefinition graph (endpoints.source checked.predecessor.base)
        entries).FixedPoint graph)).apply graph (Value.len sequence (.tuple entries)) :=
  Proofs.eval_eq_choose_apply_len policy invalid sequence graph endpoints checked entries queue

/-- For a tuple-valued queue the admitted source term denotes the bounded
predecessor computation at the source state. The target valuation is arbitrary. -/
theorem CheckedVMem.eval_eq_vmem (checked : CheckedVMem) (policy : Tagged.Policy.{u})
    (invalid : Tagged.CollectionPolicy.{u}) (sequence : SequencePolicy.{u})
    (graph : Unspecified.{u}) (endpoints : Endpoints.EndpointValuation Value.{u})
    (entries : List Value.{u}) (queue : endpoints.source checked.predecessor.queue = .tuple entries) :
    checked.eval policy invalid sequence graph endpoints =
      vmem graph (endpoints.source checked.predecessor.base) entries :=
  (checked.eval_eq_choose_apply_len policy invalid sequence graph endpoints entries queue).trans
    (vmem_eq_choose_apply_len policy.choice graph sequence _ entries).symm

end Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Source
