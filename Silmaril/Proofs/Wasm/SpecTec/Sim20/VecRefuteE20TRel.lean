module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecRefuteE20TRel32
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecRefuteE20TRel64

/-!
# The float-only `VRELOP` operators in `simEnv20T B`, by evaluation, from the two shape modules
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

theorem hasTyp_floatRel20T (s : FloatShape) (op : FloatRelOp) (h : op ∈ [.lt, .gt, .le, .ge]) :
    hasTyp 200 (simEnv20T B) VarEnv.empty (.varT "admininstr" []) (instrToV (.vecFloatRelOp s op)) =
      .ok false := by
  rcases s
  · exact hasTyp_floatRel20T_f32x4 op h
  · exact hasTyp_floatRel20T_f64x2 op h

end Silmaril.Wasm.SpecTec.Sim20.VecRefute
