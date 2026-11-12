module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdLoad

/-!
# `call_indirect-call` forward (`Step_read` 3)

2.0's

  `z; (CONST I32 i) (CALL_INDIRECT x y) ~> (CALL_ADDR a)`

under `$table(z, x).REFS[i] = (REF.FUNC_ADDR a)` and `$type(z, y) = $funcinst(z)[a].TYPE`: V2's
`ReadStep.callIndirectCall`. The address `a` is bound only by the first premise; forward it is
the address V2 finds in the table.

* `fires_callIndirectCall20`: the rule fires at the image of V2's step, from a typed state;
* `CallIndFwd20`, `fwdBase20_callInd`, and **`Task.wholeStepFwd20E`** (proved): at `storeB`, the
  nested fragment `FwdStep20D` plus `call_indirect-call` is matched forward.

`call_indirect-trap` (rule 4) is an `otherwise`: forward it needs `call_indirect-call`'s body
refuted at every assignment, which is not done here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly stateT QuantsOk evalExp_tup2 evalExp_case
  evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S adminsTy)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-- `Step_read/call_indirect-call`, rule 3 (transcribed). -/
def callIndirectCallRule20 : Rule :=
  .ruleD "call_indirect-call" [.expP "z" (.varT "state" []),
      .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]), .expP "x" (.varT "idx" []),
      .expP "y" (.varT "idx" []), .expP "a" (.varT "addr" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
        .caseE "CALL_INDIRECT" (.tupE [.varE "x", .varE "y"])]]),
      .listE [.caseE "CALL_ADDR" (.varE "a")]])
    [.ifPr (.cmpE .eqOp .boolT (.idxE (.dotE tableE "REFS") iPay)
        (.caseE "REF.FUNC_ADDR" (.varE "a"))),
      .ifPr (.cmpE .eqOp .boolT (.callE "type" [.expA (.varE "z"), .expA (.varE "y")])
        (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) "TYPE"))]

theorem hasRuleAt_callIndirectCall20 :
    HasRuleAt (simEnv20 B) "Step_read" "%~>%" 3 callIndirectCallRule20 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- The table of the frame, split. -/
theorem table?_some {s : Store H} {f : Frame} {x : TableIdx} {ti : TableInst}
    (h : (⟨s, f⟩ : State H).table? x = some ti) :
    ∃ a, f.module.tables[x.toNat]? = some a ∧ s.tables[a]? = some ti := by
  cases ha : f.module.tableAddr? x with
  | none => simp [State.table?, ha] at h
  | some a =>
    exact ⟨a, by simpa [ModuleInst.tableAddr?] using ha,
      by simpa [State.table?, ha, Store.tableInst?] using h⟩

/-- **`Step_read/call_indirect-call` fires forward** at the image of V2's
`ReadStep.callIndirectCall`, from a typed state. -/
theorem fires_callIndirectCall20 {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx}
    {i : BitVec 32} {ti : TableInst} {a : FuncAddr} {fi : FuncInst H}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (hr : ti.refs[i.toNat]? = some (.funcAddr a))
    (hf : s.funcInst? a = some fi) (hy : (⟨s, f⟩ : State H).type? y = some fi.type) :
    Fires (simEnv20 B) "Step_read" 3 (.tuple [
      configV hn ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩,
      .list (adminsToV [.callAddr a])]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat), ("x", idxV x),
    ("y", idxV y), ("a", .num (.natN a))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match callIndirectCallRule20 with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons rfl (typedV_idx20 x _ hρ) (QuantsOk.cons rfl (typedV_idx20 y _ hρ)
        (QuantsOk.cons rfl (typedV_addr20 a _ hρ) QuantsOk.nil))))
  have hl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
        .caseE "CALL_INDIRECT" (.tupE [.varE "x", .varE "y"])]]))
      (configV hn ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩) :=
    evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_listE_iff.2 ⟨_, evalExps_cons
      (evalExp_constIE rfl) (evalExps_cons (evalExp_case (evalExp_tup2 (evalExp_var rfl)
        (evalExp_var rfl))) evalExps_nil), rfl⟩))
  have hr' : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CALL_ADDR" (.varE "a")]) (.list (adminsToV [.callAddr a])) :=
    evalExp_list1 (evalExp_case (evalExp_var rfl))
  obtain ⟨ta, hta, htt⟩ := table?_some ht
  have p₁ : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.idxE (.dotE tableE "REFS") iPay) (.caseE "REF.FUNC_ADDR" (.varE "a")))
      (.bool true) := by
    refine evalExp_eqTrue (v := refV (.funcAddr a)) (evalExp_idxE_iff.2 ⟨_, i.toNat,
      evalExp_dotE_iff.2 ⟨tableInstV ti, evalExp_table20 rfl (evalExp_var rfl) (evalExp_var rfl)
        hta htt, rfl⟩, evalExp_iPay rfl, ?_⟩) (evalExp_case (evalExp_var rfl))
    simp [Value.idx?, List.getElem?_map, hr]
  have p₂ : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.callE "type" [.expA (.varE "z"), .expA (.varE "y")])
        (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) "TYPE")) (.bool true) :=
    evalExp_eqTrue (evalExp_type20 rfl (evalExp_var rfl) (evalExp_var rfl)
      (by simpa [State.type?, ModuleInst.type?] using hy))
      (evalExp_dotE_iff.2 ⟨funcInstV hn fi, evalExp_funcinstAt20 rfl rfl rfl hf, rfl⟩)
  refine Pure.fires_of_ruleAt hasRuleAt_callIndirectCall20 σ hq (evalExp_tup2 hl hr') ?_
  intro pr hpr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .ifPr p₁
  · exact .ifPr p₂

/-! ## The fragment -/

/-- **V2's `call_indirect` that calls**, with V2's premises. -/
inductive CallIndFwd20 : Config H → Config H → Prop where
  | mk {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {i : BitVec 32} {ti : TableInst}
      {a : FuncAddr} {fi : FuncInst H} (ht : (⟨s, f⟩ : State H).table? x = some ti)
      (hr : ti.refs[i.toNat]? = some (.funcAddr a)) (hf : s.funcInst? a = some fi)
      (hy : (⟨s, f⟩ : State H).type? y = some fi.type) :
      CallIndFwd20 ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩ ⟨s, f, [.callAddr a]⟩

theorem CallIndFwd20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : CallIndFwd20 c c') : Step P host c c' := by
  cases h with
  | mk ht hr hf hy => exact .read (.callIndirectCall ht hr hf hy)

/-- **`call_indirect-call` is a base**, at every builtins and any store condition. -/
theorem fwdBase20_callInd {W : Store H → Prop} : FwdBase20 B hn W (CallIndFwd20 (H := H)) where
  sr _ _ hc h := by
    cases h with
    | mk _ _ _ _ => exact typed20_iff.2 ⟨(typed20_iff.1 hc).1, typedV_admins_callAddr20 _⟩
  fwd c c' hc _ h := by
    have hz := typedV_state_of_typed20 hc
    cases h with
    | @mk s f x y i ti a fi ht hr hf hy =>
      have hc' : Typed20 (simEnv20 B) hn ⟨s, f, [.callAddr a]⟩ :=
        typed20_iff.2 ⟨(typed20_iff.1 hc).1, typedV_admins_callAddr20 _⟩
      exact fwdS_read hc hc' (sread_of_firesB20 (firesB_read20_iff.2
        (fires_callIndirectCall20 hz ht hr hf hy)))

/-- **The base at `storeB`, with `call_indirect-call`.** -/
inductive FwdStep20E (P : Profile) : Config H → Config H → Prop where
  | fwd {c c' : Config H} (h : FwdStep20D P c c') : FwdStep20E P c c'
  | callInd {c c' : Config H} (h : CallIndFwd20 c c') : FwdStep20E P c c'

theorem FwdStep20E.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : FwdStep20E P c c') : Step P host c c' := by
  cases h with
  | fwd h => exact h.step
  | callInd h => exact h.step

/-- The widened base is a base at `storeB`. -/
theorem fwdBase20_fwdE (P : Profile) :
    FwdBase20 (storeB P) hn WholePages (FwdStep20E (H := H) P) where
  sr c c' hc h := by
    cases h with
    | fwd h => exact (fwdBase20_fwdD P).sr c c' hc h
    | callInd h => exact (fwdBase20_callInd (W := WholePages)).sr c c' hc h
  fwd c c' hc hw h := by
    cases h with
    | fwd h => exact (fwdBase20_fwdD P).fwd c c' hc hw h
    | callInd h => exact fwdBase20_callInd.fwd c c' hc hw h

/-- **The forward 2.0 half with `call_indirect-call`** (stated and proved): at `storeB`, every
step of `Nest20 (FwdStep20E P)` from a configuration with typed image and whole pages is a step of
the corrected script between the images, with a typed successor image. -/
def Task.wholeStepFwd20E : Prop :=
  ∀ (H : Type) (hn : H → String) (P : Profile) (c c' : Config H),
    Typed20 (simEnv20 (storeB P)) hn c → WholePages c.store → Nest20 (FwdStep20E P) c c' →
    Typed20 (simEnv20 (storeB P)) hn c' ∧
      SStepB (simEnv20S (storeB P)) (configV hn c) (configV hn c')

/-- **`Task.wholeStepFwd20E` is proved**, at every profile. -/
theorem wholeStepFwd20E : Task.wholeStepFwd20E :=
  fun _ _ P _ _ hc hw h => fwd_nest20 (fwdBase20_fwdE P) h hc hw

end Silmaril.Wasm.SpecTec.Sim20.Whole
