module

public import Silmaril.Logic.ACL2.X86Step.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.X86Step

open Silmaril.Logic.ACL2 Silmaril.Logic.ACL2.Translated Silmaril.Logic.ACL2.X86Step

private theorem subsetOfCheck {xs ys : List (Name × Nat)}
    (check : (xs.all fun x => decide (x ∈ ys)) = true) {entry : Name × Nat} :
    entry ∈ xs → entry ∈ ys :=
  fun member => of_decide_eq_true (List.all_eq_true.mp check entry member)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem calls_exact (entry : Name × Nat) : entry ∈ source.calls ↔ entry ∈ manifestCalls :=
  ⟨subsetOfCheck (by decide), subsetOfCheck (by decide)⟩

theorem frontier_exact (entry : Name × Nat) :
    frontier.arity entry.1 = some entry.2 ↔ entry ∈ frontierEntries := by
  constructor
  · intro h
    obtain ⟨found, lookup, arity⟩ := Option.map_eq_some_iff.mp h
    have named : found.1 = entry.1 :=
      of_decide_eq_true (List.find?_some (p := fun x : Name × Nat => decide (x.1 = entry.1)) lookup)
    exact Prod.ext named arity ▸ List.mem_of_find?_eq_some lookup
  · intro h
    have lookup : (frontierEntries.all fun x => decide (frontier.arity x.1 = some x.2)) = true := by
      decide
    exact of_decide_eq_true (List.all_eq_true.mp lookup entry h)

end Silmaril.Proofs.Logic.ACL2.X86Step
