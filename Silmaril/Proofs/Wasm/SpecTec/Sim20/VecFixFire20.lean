module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixFwd

/-!
# `vextract_lane` forward in the original 2.0 script

`extractEnv20`: `simEnv20 B` has the facts of `ExtractEnv` when `B` answers `$lanes_` as V2 does
(`Whole.LaneCalls20`); `Whole.storeB P` does. Rule 46 of `Step_pure` and its quantifier types are
the same in every 2.0 environment here, so **`fwd_vextractLaneNum20`** holds in the original
script too: what the erratum adds is that the instruction is typed (`typedA_extract20V`), which
lifting the rule through `Step/pure` at a typed configuration needs.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (Fires)

set_option maxRecDepth 100000 in
theorem hasRuleAt_vextractLaneNum20 (B : Builtins) :
    Equiv.Validation.HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 46 vextractLaneNumRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- **The original script has the facts of `ExtractEnv`**, at builtins answering `$lanes_`. -/
theorem extractEnv20 {B : Builtins} (hL : Whole.LaneCalls20 B) : ExtractEnv (simEnv20 B) where
  rule := hasRuleAt_vextractLaneNum20 B
  vec := Whole.typedV_vecV128_20
  numtype := (Pure.numTyped_simEnv20 B).numtype
  num t x := (Pure.numTyped_simEnv20 B).num (.int t) x "nt"
  N := Whole.typedV_N20
  laneidx := Whole.typedV_laneidx20
  lanesDef := Whole.findDef_lanes20 B
  lanes sz c := by
    rw [simEnv20, Env.builtins_withBuiltins]
    exact hL.lanes sz c

/-- **`vextract_lane` at `i32x4`/`i64x2` forward, in the original script** at `Whole.storeB P`. -/
theorem fwd_vextractLaneNum20 {P : Numerics.Profile} (t : IntType) {c : BitVec 128} {i : LaneIdx}
    {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecExtractLane (.int (numShape t)) none i)] code') :
    Fires (simEnv20 (Whole.storeB P)) "Step_pure" 46 (.tuple [.list (adminsToV [vconst c,
      .plain (.vecExtractLane (.int (numShape t)) none i)]), .list (adminsToV code')]) :=
  fwd_vextractLaneNum (extractEnv20 (Whole.laneCalls20_storeB P)) t h

end Silmaril.Wasm.SpecTec.Sim20.VecFix
