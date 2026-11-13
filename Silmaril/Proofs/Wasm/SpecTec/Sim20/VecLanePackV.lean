module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLaneLkA
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLaneLkB
public import Silmaril.Wasm.SpecTec.Sim20.VecAgree.Thms

/-!
# `vextract_lane-pack` forward and as a `Step` in the corrected script

* `packEnv20V`: `simEnv20V B` has the facts of `PackEnv` when `B` answers `$lanes_` as V2 does and
  the float primitives (`$extend__` among them) as the profile `P` does.
* **`fwd_vextractLanePack20V`**: at `Whole.storeB P`, every V2 pure step from
  `v128.const c; i8x16.extract_lane_sx i` (or `i16x8`) is matched by rule 47.
* **`sstepV_vextractLanePack`**: it is a `Step` of `simEnv20V (storeB P)` at every V2 state typed in
  `simEnv20T (storeB P)` (through `VecAgree.typedV_TtoV`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecLane

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.Wasm.SpecTec.Sim (Fires SStep cfgV TypedV stateT evalExp_case)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (jnnV20 storeB)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)

/-- `$psize` at `I8` and `I16`, in any environment with its two clauses. -/
theorem callDef_psize_of {env : Env} {ps : List Param} {t : Typ}
    (hd : env.findDef? "psize" = some (ps, t,
      [.defD [] [.expA (.caseE "I8" (.tupE []))] (.numE (.natN 8)) [],
       .defD [] [.expA (.caseE "I16" (.tupE []))] (.numE (.natN 16)) []]))
    {sz : PackSize} (hs : Packed sz) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "psize" = none) (ha : EvalArgs env ρ args [.val (jnnV20 sz)]) :
    CallDef env ρ "psize" args (natV sz.width) := by
  refine callDef_of_tryClauses hρ hd ha ?_
  rcases hs with rfl | rfl
  · exact tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
      matchArgs_nil) premsHold_nil evalExp_num
  · exact tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
      (matchExp_caseE_undef (by decide)))) (tryClauses_hit (matchArgs_cons (matchArg_expA
        (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil) premsHold_nil evalExp_num)

/-- `$extend__`, answered by builtins with the float primitives of `P`. -/
theorem extend_call_of {P : Numerics.Profile} {B : Builtins} (hF : Sim.Floats.FloatB P B)
    (N N' : Nat) (s : Signedness) (x : BitVec N) :
    B.call "extend__" [.val (natV N), .val (natV N'), .val (sxV s), .val (pctV x.toNat)] =
      some (Equiv.bvV (match s with | .signed => x.signExtend N' | .unsigned => x.setWidth N')) := by
  refine hF _ _ _ ?_
  rw [Pure.sxV_eq20]
  have h := Sim.Floats.floatCall_extend P N N' s x
  cases s <;> exact h

/-- **The corrected script has the facts of `PackEnv`.** -/
theorem packEnv20V {P : Numerics.Profile} {B : Builtins} (hL : Whole.LaneCalls20 B)
    (hF : Sim.Floats.FloatB P B) : PackEnv (simEnv20V B) where
  rule := hasRuleAt_vextractLanePack20V B
  vec := VecFix.typedV_vecV128_20V
  packtype _ hp := typedV_packtype20V hp
  N := VecFix.typedV_N20V
  sx := VecFix.typedV_sx20V
  laneidx := VecFix.typedV_laneidx20V
  num32 x _ _ := VecFix.hasTyp_num_int20V (t := .i32) x
    (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
  psize _ hp _ _ hρ ha := by
    obtain ⟨ps, t, hd⟩ := findDef_psize20V B
    exact callDef_psize_of hd hp hρ ha
  lanesDef := VecFix.findDef_lanes20V
  lanes sz c := by
    rw [simEnv20V, Env.builtins_withBuiltins]
    exact hL.lanes sz c
  extendDef := findDef_extend20V B
  extend N N' s x := by
    rw [simEnv20V, Env.builtins_withBuiltins]
    exact extend_call_of hF N N' s x

/-- **`vextract_lane` at `i8x16`/`i16x8` forward, in the corrected script** at `Whole.storeB P`. -/
theorem fwd_vextractLanePack20V {P : Numerics.Profile} {sz : PackSize} (hp : Packed sz)
    {s : Signedness} {c : BitVec 128} {i : LaneIdx} {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecExtractLane (.int (packShape sz)) (some s) i)] code') :
    Fires (simEnv20V (storeB P)) "Step_pure" 47 (.tuple [.list (adminsToV [vconst c,
      .plain (.vecExtractLane (.int (packShape sz)) (some s) i)]), .list (adminsToV code')]) :=
  fwd_vextractLanePack (packEnv20V (Whole.laneCalls20_storeB P) (Whole.floatB_storeB P)) hp h

/-- The source `v128.const c; sh.extract_lane_sx i` is a typed `admininstr*` of `simEnv20V`. -/
theorem typedV_extractPackSrc {B : Builtins} {sz : PackSize} (hp : Packed sz) (s : Signedness)
    (c : BitVec 128) (i : LaneIdx) :
    TypedV (simEnv20V B) StepFix.adminsTy
      (.list (adminsToV [vconst c, .plain (.vecExtractLane (.int (packShape sz)) (some s) i)])) := by
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  have hu' : u = adminToV (vconst c) ∨
      u = instrToV (.vecExtractLane (.int (packShape sz)) (some s) i) := by
    simpa [adminsToV, adminToV] using hu
  rcases hu' with rfl | rfl
  · exact Sim.typedV_list_iff.1 (VecAgree.typedV_admins_valV (.vec c)) _
      (by simp [adminsToV, Val.toAdmin])
  · exact VecFix.typedA_extract20V _ _ _ (by
      rcases hp with rfl | rfl <;>
        simp [V2.Instr.immediatesValid, packShape, Shape.laneWidth, IntShape.laneWidth])

/-- **`vextract_lane` at `i8x16`/`i16x8` is a `Step` of the corrected script**, at every state
typed in `simEnv20T` that is `VOk` (every V2 state image is). -/
theorem sstepV_vextractLanePack {P : Numerics.Profile} {sz : PackSize} (hp : Packed sz)
    {z : Value} (hz : TypedV (simEnv20T (storeB P)) stateT z) (hv : VecAgree.VOk z)
    {s : Signedness} {c : BitVec 128} {i : LaneIdx} {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecExtractLane (.int (packShape sz)) (some s) i)] code') :
    SStep (simEnv20V (storeB P))
      (cfgV z (adminsToV [vconst c, .plain (.vecExtractLane (.int (packShape sz)) (some s) i)]))
      (cfgV z (adminsToV code')) := by
  have hf := fwd_vextractLanePack20V hp h
  obtain ⟨-, rfl⟩ := pureStep_extractSx_inv h
  obtain ⟨ty, rules, hrel⟩ := VecAgree.findRel_pure20V (storeB P)
  have hpu : Sim.SPure (simEnv20V (storeB P)) _ _ := (Sim.dderives_iff_fires hrel).2 ⟨47, hf⟩
  exact VecAgree.sstepV_pure (VecAgree.typedV_TtoV VecAgree.ffT_state hv hz)
    (typedV_extractPackSrc hp s c i) (VecAgree.typedV_admins_valV _) hpu

end Silmaril.Wasm.SpecTec.Sim20.VecLane
