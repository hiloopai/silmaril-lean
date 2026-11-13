module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixTypV
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixLkE
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixLkF
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixFwd

/-!
# `vextract_lane` forward under the vector errata

`extractEnv20V`: `simEnv20V B` has the facts of `ExtractEnv` when `B` answers `$lanes_` as V2
does (`Whole.LaneCalls20`). **`fwd_vextractLaneNum20V`**: at `Whole.storeB P`, every V2 pure step
from `v128.const c; i32x4.extract_lane i` (or `i64x2`) is matched by rule 46 of `Step_pure` in the
corrected script, where the instruction is also typed (`typedA_extract20V`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (Fires)

/-- **The corrected script has the facts of `ExtractEnv`**, at builtins answering `$lanes_`. -/
theorem extractEnv20V {B : Builtins} (hL : Whole.LaneCalls20 B) : ExtractEnv (simEnv20V B) where
  rule := hasRuleAt_vextractLaneNum20V B
  vec := typedV_vecV128_20V
  numtype := typedV_numtype20V
  num t x := fun _ _ hx => hasTyp_num_int20V x (Sim.evalExp_var hx)
  N := typedV_N20V
  laneidx := typedV_laneidx20V
  lanesDef := findDef_lanes20V
  lanes sz c := by
    rw [simEnv20V, Env.builtins_withBuiltins]
    exact hL.lanes sz c

/-- **`vextract_lane` at `i32x4`/`i64x2` forward, in the corrected script** at `Whole.storeB P`. -/
theorem fwd_vextractLaneNum20V {P : Numerics.Profile} (t : IntType) {c : BitVec 128} {i : LaneIdx}
    {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecExtractLane (.int (numShape t)) none i)] code') :
    Fires (simEnv20V (Whole.storeB P)) "Step_pure" 46 (.tuple [.list (adminsToV [vconst c,
      .plain (.vecExtractLane (.int (numShape t)) none i)]), .list (adminsToV code')]) :=
  fwd_vextractLaneNum (extractEnv20V (Whole.laneCalls20_storeB P)) t h

end Silmaril.Wasm.SpecTec.Sim20.VecFix
