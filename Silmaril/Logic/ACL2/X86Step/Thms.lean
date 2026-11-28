module

public import Silmaril.Logic.ACL2.X86Step.Defs
public import Silmaril.Logic.ACL2.Translated.Thms
import Silmaril.Proofs.Logic.ACL2.X86Step.Checking

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Step

open Translated

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- A successful lowering certifies all variable slots, arguments and call resolutions
in the exact pinned body, including within translated lambdas. -/
theorem checked_agreement : lower frontier formals source = some definition.body :=
  Option.eq_some_of_isSome sourceChecks

/-- The source call set agrees with the manifest on full symbol identity and arity. -/
theorem calls_exact (entry : Name × Nat) : entry ∈ source.calls ↔ entry ∈ manifestCalls :=
  Proofs.Logic.ACL2.X86Step.calls_exact entry

theorem frontier_partition :
    frontierEntries = manifestCalls.filter
      (fun call => decide (call.1 ≠ ifName) && (Primitive.lookup call.1).isNone) := by
  decide

/-- The model caller supplies exactly the named external operations in this slice. -/
theorem frontier_exact (entry : Name × Nat) :
    frontier.arity entry.1 = some entry.2 ↔ entry ∈ frontierEntries :=
  Proofs.Logic.ACL2.X86Step.frontier_exact entry

/-- A total interpretation extends the abstract frontier by the step's checked defining equation. -/
theorem defining_equation (M : Interpretation frontier) (x86 : Standard.Object) :
    definition.extend M definition.symbol (fun _ => x86) =
      definition.body.eval M (fun _ => x86) := definition.equation M _

end Silmaril.Logic.ACL2.X86Step
