module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBase

/-!
# Float `VRELOP` at `f64x2` (gt, le, ge) in `simEnv20V B`, by evaluation
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm

set_option maxRecDepth 100000

variable {B : Builtins}

set_option maxHeartbeats 4000000 in
theorem hasTyp_floatRel20V_4 (op : FloatRelOp) (h : op ∈ [.gt, .le, .ge]) :
    hasTyp 200 (simEnv20V B) VarEnv.empty (.varT "admininstr" []) (instrToV (.vecFloatRelOp .f64x2 op)) =
      .ok true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> with_unfolding_all rfl

end Silmaril.Wasm.SpecTec.Sim20.VecFix
