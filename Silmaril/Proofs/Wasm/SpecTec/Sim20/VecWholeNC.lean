module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeEntry

/-!
# The clause-less lane primitives have no clause in `simEnv20V B` (kernel lookups)

Split from `VecWholePrims` for build time.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecWhole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecNum (vecNB vecNB_call_of_ne)

variable {B : Builtins}

/-- The clause-less lane primitives of the 2.0 vector lanes. -/
def lanePrims : List IL.Id := ["ipopcnt_", "iavgr_", "iq15mulr_sat_", "fpmin_", "fpmax_"]

set_option maxRecDepth 100000 in
/-- None of them has a clause in `simEnv20V B` (kernel lookups). -/
theorem noClauses_lanePrims {x : IL.Id} (hx : x ∈ lanePrims) :
    Sim.IntNumeric.NoClauses (simEnv20V B) x := by
  simp only [lanePrims, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩

end Silmaril.Wasm.SpecTec.Sim20.VecWhole
