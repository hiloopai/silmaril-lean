module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixPremP

/-!
# The vector errata: the corrected `VEXTRACT_LANE` premise holds at V2's valid immediates

`premsOk_extract20V`: at every shape `s` and sign `sx?` that V2 accepts (`sx?` is present
exactly when the lanes are narrower than 32 bits), and at every lane index, the corrected premise
`extractPremFix` holds in the scope the payload binds (by evaluation, with the lane abstract: the
premise does not read it).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm

variable {B : Builtins}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The corrected premise holds at every valid `VEXTRACT_LANE`.** -/
theorem premsOk_extract20V (s : Shape) (sx : Option Signedness) (l : LaneIdx)
    (h : (V2.Instr.vecExtractLane s sx l).immediatesValid = true) :
    PremsOk (simEnv20V B) (caseScope VarEnv.empty extractPayT (extractW s sx l)) [extractPremFix] := by
  refine ⟨20, ?_⟩
  rcases s with s | s <;> rcases s <;> rcases sx with _ | sx <;>
    simp [V2.Instr.immediatesValid, Shape.laneWidth, IntShape.laneWidth,
      FloatShape.laneWidth] at h
  · exact premsOk_extractPacked20V _ (.inl rfl) sx l
  · exact premsOk_extractPacked20V _ (.inr rfl) sx l
  all_goals with_unfolding_all rfl

end Silmaril.Wasm.SpecTec.Sim20.VecFix
