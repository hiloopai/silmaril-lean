module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecAgreeRel
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecAgreeImg
public import Silmaril.Wasm.SpecTec.Sim20.VecFix.Thms
public import Silmaril.Wasm.SpecTec.Sim20.StoreRun.Thms
public import Silmaril.Wasm.SpecTec.Sim20.StoreBulk.Thms

/-!
# `vextract_lane-num` lifted to `Step` in the corrected script

An earlier step proved `VecFix.fwd_vextractLaneNum20V`: a `Step_pure` firing in `simEnv20V`. Lifting
it through `Step/pure` needs the state typed in `simEnv20V`, and the round 6 invariants type
states in `simEnv20T`. `typedV_TtoV` moves that typing, at `VOk` values, and every state image is
`VOk` (`vOk_stateV`).

* `sstepV_pure`: `Step/pure` in `simEnv20V`.
* **`sstepV_vextractLaneNum`**: at a state typed in `simEnv20T (storeB P)` that is the image of a
  V2 state, every V2 pure step from `v128.const c; i32x4.extract_lane i` (or `i64x2`) is a step
  of `simEnv20V (storeB P)` between the images, with the state unchanged.
* `sstepV_vextractLaneNum_typF`: the same at the state of any configuration whose state part
  satisfies round 5's `TypF` over a `StoreOkB` store (the typing half of `Good20B`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (evalExp_iterPat)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk SStep cfgV TypedV ValsOnly stateT dderives_of_ruleAt
  evalExp_tup2 evalExp_case prems_one)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy iterV)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V numShape fwd_vextractLaneNum20V pureStep_extract_inv
  typedA_extract20V)

set_option maxRecDepth 100000 in
theorem hasRuleAt_pureFixV (B : Builtins) :
    HasRuleAt (simEnv20V B) "Step" "%~>%" 0 StepFix.pureFix :=
  ⟨_, _, _, rfl, rfl, rfl⟩

variable {B : Builtins}

/-- **`Step/pure`** in `simEnv20V`: a `Step_pure` step between `admininstr*` sequences is a `Step`
step at any state. (The proof of `StoreRun.sstepT_pure`, at `simEnv20V`.) -/
theorem sstepV_pure {z : Value} {is js : List Value} (hz : TypedV (simEnv20V B) stateT z)
    (his : TypedV (simEnv20V B) adminsTy (.list is)) (hjs : TypedV (simEnv20V B) adminsTy (.list js))
    (hp : Sim.SPure (simEnv20V B) is js) : SStep (simEnv20V B) (cfgV z is) (cfgV z js) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("instr*", .list is), ("instr'*", .list js)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fj : ρ.findVal? "instr'*" = some (.list js) := rfl
  have hq : QuantsOk (simEnv20V B) ρ
      [.expP "z" stateT, .expP "instr*" adminsTy, .expP "instr'*" adminsTy] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fj (hjs ρ hρ) QuantsOk.nil))
  have ei : EvalExp (simEnv20V B) ρ (iterV "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ej : EvalExp (simEnv20V B) ρ (iterV "instr'" "instr'*") (.list js) :=
    evalExp_iterPat (by decide) fj
  exact dderives_of_ruleAt (hasRuleAt_pureFixV B) _ hq
    (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ej)))
    (prems_one (.rulePr Equiv.evalArgs_nil (evalExp_tup2 ei ej) hp))

theorem ffT_state : ffT stateT := by
  simp [ffT, Sim.Round7.Script.evTyp, Sim.Round7.Script.evArgs, ElseAgree.GoodT,
    ElseAgree.tyEvB, fams]

theorem ffT_admins : ffT adminsTy := by
  simp [ffT, Sim.Round7.Script.evTyp, Sim.Round7.Script.evArgs, Sim.Round7.Script.evIter,
    ElseAgree.GoodT, ElseAgree.tyEvB, fams]

/-- A V2 value is a typed `admininstr*` of `simEnv20V`. -/
theorem typedV_admins_valV (v : Val) :
    TypedV (simEnv20V B) adminsTy (.list (adminsToV [v.toAdmin])) :=
  typedV_TtoV ffT_admins (vOk_adminsToV _) (StoreGood.typedV_admins_to20T (Whole.typedV_admins_val20 v))

set_option maxRecDepth 100000 in
theorem findRel_pure20V (B : Builtins) : ∃ t rules,
    (simEnv20V B).findRel? "Step_pure" = some ([], "%~>%", t, rules) :=
  ⟨_, _, rfl⟩

/-- The source `v128.const c; sh.extract_lane i` is a typed `admininstr*` of `simEnv20V`. -/
theorem typedV_extractSrc (t : IntType) (c : BitVec 128) (i : LaneIdx) :
    TypedV (simEnv20V B) adminsTy
      (.list (adminsToV [vconst c, .plain (.vecExtractLane (.int (numShape t)) none i)])) := by
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  have hu' : u = adminToV (vconst c) ∨
      u = instrToV (.vecExtractLane (.int (numShape t)) none i) := by
    simpa [adminsToV, adminToV] using hu
  rcases hu' with rfl | rfl
  · exact Sim.typedV_list_iff.1 (typedV_admins_valV (.vec c)) _ (by simp [adminsToV, Val.toAdmin])
  · exact typedA_extract20V _ _ _ (by cases t <;> simp [V2.Instr.immediatesValid, numShape, Shape.laneWidth, IntShape.laneWidth])

/-- **`vextract_lane` at `i32x4`/`i64x2` is a `Step` of the corrected script**, at every state
typed in `simEnv20T` that is `VOk` (every V2 state image is, `vOk_stateV`). -/
theorem sstepV_vextractLaneNum {P : Numerics.Profile} (t : IntType) {z : Value}
    (hz : TypedV (simEnv20T (Whole.storeB P)) stateT z) (hv : VOk z) {c : BitVec 128}
    {i : LaneIdx} {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecExtractLane (.int (numShape t)) none i)] code') :
    SStep (simEnv20V (Whole.storeB P))
      (cfgV z (adminsToV [vconst c, .plain (.vecExtractLane (.int (numShape t)) none i)]))
      (cfgV z (adminsToV code')) := by
  have hf := fwd_vextractLaneNum20V t h
  obtain ⟨-, rfl⟩ := pureStep_extract_inv h
  obtain ⟨ty, rules, hrel⟩ := findRel_pure20V (Whole.storeB P)
  have hp : Sim.SPure (simEnv20V (Whole.storeB P)) _ _ := (Sim.dderives_iff_fires hrel).2 ⟨46, hf⟩
  exact sstepV_pure (typedV_TtoV ffT_state hv hz) (typedV_extractSrc t c i)
    (typedV_admins_valV _) hp

/-- **The same at the state of a configuration with round 5's typing invariant** (`TypF`, the
typing half of `Good20B`) over a `StoreOkB` store: the state is typed in `simEnv20T`
(`StoreBulk.typF_stateB`) and is a V2 image. -/
theorem sstepV_vextractLaneNum_typF {H : Type} {hn : H → String} {P : Numerics.Profile}
    {cfg : Config H} (hT : StoreFn.TypF (Whole.storeB P) hn cfg) (hs : StoreBulk.StoreOkB cfg.store)
    (t : IntType) {c : BitVec 128} {i : LaneIdx} {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecExtractLane (.int (numShape t)) none i)] code') :
    SStep (simEnv20V (Whole.storeB P))
      (cfgV (stateV hn cfg.store cfg.frame)
        (adminsToV [vconst c, .plain (.vecExtractLane (.int (numShape t)) none i)]))
      (cfgV (stateV hn cfg.store cfg.frame) (adminsToV code')) :=
  sstepV_vextractLaneNum t (StoreBulk.typF_stateB hT hs) (vOk_stateV hn _ _) h

end Silmaril.Wasm.SpecTec.Sim20.VecAgree
