module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecRefuteBase

/-!
# The float-only `VRELOP` operators in `simEnv20T B`, by evaluation, at `f32x4`
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecRefute

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)

set_option maxRecDepth 100000

variable {B : Builtins}

set_option maxHeartbeats 4000000 in
theorem hasTyp_floatRel20T_f32x4 (op : FloatRelOp) (h : op ∈ [.lt, .gt, .le, .ge]) :
    hasTyp 200 (simEnv20T B) VarEnv.empty (.varT "admininstr" []) (instrToV (.vecFloatRelOp .f32x4 op)) =
      .ok false := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> with_unfolding_all rfl

end Silmaril.Wasm.SpecTec.Sim20.VecRefute
