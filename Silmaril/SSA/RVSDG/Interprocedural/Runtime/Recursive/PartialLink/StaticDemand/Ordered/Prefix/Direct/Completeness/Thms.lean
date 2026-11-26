module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Completeness

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct

open Continuation.Partial.Executable (Actions)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {scope : Scope m} {actions : Actions m σ} {fn : Function V S}
variable {imports entry context outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
variable {inputsL inputsR : Tuple m.Val imports}
variable {checked : scope.Checked actions} {routes : Routes inputsL inputsR scope}

/-- Synthesis succeeds on every direct forwarding derivation. The
hypotheses require exact tracked slot sources in both links at each call. -/
theorem synthesizeAt_complete {source : ScopeBoundary imports entry scope.past past}
    {code : Code Op entry past sigs outs true (some scope.table)}
    (tracked : Tracked checked routes source code) :
    (synthesizeAt checked routes source code rfl).isSome = true :=
  Proofs.tracked_complete tracked

/-- The same completeness statement for a λ reached from its actual
capture wires. Whole-prefix admission also checks the binding itself. -/
theorem synthesize_complete {captures : Wires imports scope.past context}
    {code : Code Op (context ++ fn.args) past sigs outs true (some scope.table)}
    (tracked : Tracked checked routes (ScopeBoundary.start (captureBoundary captures) past) code) :
    (synthesize checked routes captures code).isSome = true := by
  simpa [synthesize, synthesizeWith, synthesizeAt] using Proofs.tracked_complete tracked

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct
