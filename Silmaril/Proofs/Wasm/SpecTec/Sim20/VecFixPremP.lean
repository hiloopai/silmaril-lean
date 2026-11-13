module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBase

/-!
# The vector errata: the corrected `VEXTRACT_LANE` premise at packed lanes

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

/-- The payload of `VEXTRACT_LANE` at V2's immediates. -/
def extractW (s : Shape) (sx : Option Signedness) (l : LaneIdx) : Value :=
  .tuple [shapeV s, .opt (sx.map sxV), pctV l.val]

theorem instrToV_extract (s : Shape) (sx : Option Signedness) (l : LaneIdx) :
    instrToV (.vecExtractLane s sx l) = .case "VEXTRACT_LANE" (extractW s sx l) := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The corrected premise holds at `i8x16` and `i16x8` with a sign (by evaluation). -/
theorem premsOk_extractPacked20V (s : IntShape) (hs : s = .i8x16 ∨ s = .i16x8) (sx : Signedness)
    (l : LaneIdx) :
    premsOk 20 (simEnv20V B) (caseScope VarEnv.empty extractPayT (extractW (.int s) (some sx) l))
      [extractPremFix] = .ok true := by
  rcases hs with rfl | rfl <;> rcases sx <;> with_unfolding_all rfl

end Silmaril.Wasm.SpecTec.Sim20.VecFix
