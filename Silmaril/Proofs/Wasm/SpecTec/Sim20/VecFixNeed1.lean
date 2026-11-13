module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBase

/-!
# Without the erratum, `VEXTRACT_LANE` at integer shapes is not typed in `simEnv20T B`

At lane 0, with the sign V2 requires, `hasTyp` answers `false` at fuel 200 (by evaluation):
the case quantifies `numtype`, which its premise does not define.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)

set_option maxRecDepth 100000

variable {B : Builtins}

set_option maxHeartbeats 4000000 in
theorem hasTyp_extract20T_1 (s : IntShape) (sx : Option Signedness)
    (h : (V2.Instr.vecExtractLane (.int s) sx 0).immediatesValid = true) :
    hasTyp 200 (simEnv20T B) VarEnv.empty (.varT "admininstr" [])
      (instrToV (.vecExtractLane (.int s) sx 0)) = .ok false := by
  rcases s <;> rcases sx with _ | sx <;>
    simp [V2.Instr.immediatesValid, Shape.laneWidth, IntShape.laneWidth] at h <;> (try rcases sx) <;> with_unfolding_all rfl

end Silmaril.Wasm.SpecTec.Sim20.VecFix
