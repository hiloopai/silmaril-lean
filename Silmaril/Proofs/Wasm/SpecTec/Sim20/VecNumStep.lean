module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecNumB

/-!
# The 42 float vector operators are `Step`s of the corrected script at `vecNB P`

Round 7's `VecLane.sstepV_vecFloatUnOp`, `sstepV_vecFloatBinOp` and `sstepV_vecFloatRelOp` took
the hypothesis `VecNumAgree (simEnv20V B) P`. At `B = vecNB P` it holds
(`vecNumAgree_vecNB`), so the three lifts need only what they need besides it: the state typed in
`simEnv20T (vecNB P)` and `VOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecNum

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (SStep cfgV TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)

/-- **The float `vunop`s are `Step`s of the corrected script at `vecNB P`.** -/
theorem sstepV_vecFloatUnOp_vecNB {P : Profile} {z : Value}
    (hz : TypedV (simEnv20T (vecNB P)) stateT z) (hv : VecAgree.VOk z) {s : FloatShape}
    {op : FloatUnOp} {c : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecFloatUnOp s op)] code') :
    SStep (simEnv20V (vecNB P)) (cfgV z (adminsToV [vconst c, .plain (.vecFloatUnOp s op)]))
      (cfgV z (adminsToV code')) :=
  VecLane.sstepV_vecFloatUnOp (vecNumAgree_vecNB P) hz hv h

/-- **The float `vbinop`s are `Step`s of the corrected script at `vecNB P`.** -/
theorem sstepV_vecFloatBinOp_vecNB {P : Profile} {z : Value}
    (hz : TypedV (simEnv20T (vecNB P)) stateT z) (hv : VecAgree.VOk z) {s : FloatShape}
    {op : V2.VecFloatBinOp} {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatBinOp s op)] code') :
    SStep (simEnv20V (vecNB P))
      (cfgV z (adminsToV [vconst c₁, vconst c₂, .plain (.vecFloatBinOp s op)]))
      (cfgV z (adminsToV code')) :=
  VecLane.sstepV_vecFloatBinOp (vecNumAgree_vecNB P) hz hv h

/-- **The float `vrelop`s are `Step`s of the corrected script at `vecNB P`.** -/
theorem sstepV_vecFloatRelOp_vecNB {P : Profile} {z : Value}
    (hz : TypedV (simEnv20T (vecNB P)) stateT z) (hv : VecAgree.VOk z) {s : FloatShape}
    {op : FloatRelOp} {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatRelOp s op)] code') :
    SStep (simEnv20V (vecNB P))
      (cfgV z (adminsToV [vconst c₁, vconst c₂, .plain (.vecFloatRelOp s op)]))
      (cfgV z (adminsToV code')) :=
  VecLane.sstepV_vecFloatRelOp (vecNumAgree_vecNB P) hz hv h

end Silmaril.Wasm.SpecTec.Sim20.VecNum
