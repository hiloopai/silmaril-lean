module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.CallIndGoodSize

/-!
# `table.get` forward (`Step_read` 9 and 10)

Round 2 proved `table.get-val` backwards (`Whole.bwdRead_tableGetVal`); `table.get-trap` has an
explicit premise `i >= |$table(z, x).REFS|` (no `otherwise`). Both fire forward at V2's steps,
from a typed state:

* `fires_tableGetTrap20`: `z; (CONST I32 i) (TABLE.GET x) ~> TRAP` where `i` is out of range;
* `fires_tableGetVal20`: `z; (CONST I32 i) (TABLE.GET x) ~> $table(z, x).REFS[i]`, the reference
  V2 reads.

`TableGetFwd20` is V2's two steps, a base fragment by `fwdBase20_tableGet`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.CallIndGood

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV stateT QuantsOk evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim20.Whole (FwdBase20 typed20_iff constIE iPay tableE tableLenE)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-- `Step_read/table.get-trap`, rule 9 of `Step_read` (verbatim). -/
def tableGetTrapRule20 : Rule :=
  .ruleD "table.get-trap" [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA
    (.caseE "I32" (.tupE []))]), .expP "x" (.varT "idx" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE, .caseE "TABLE.GET" (.varE "x")]]),
      .listE [.caseE "TRAP" (.tupE [])]])
    [.ifPr (.cmpE .geOp (.numT .natT) iPay tableLenE)]

theorem hasRuleAt_tableGetTrap20 :
    HasRuleAt (simEnv20 B) "Step_read" "%~>%" 9 tableGetTrapRule20 := ⟨_, _, _, rfl, rfl, rfl⟩

/-- The scope of both rules. -/
abbrev tableGetScope (s : Store H) (f : Frame) (i : BitVec 32) (x : TableIdx) :
    List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat), ("x", idxV x)]

theorem quantsOk_tableGet {s : Store H} {f : Frame} {i : BitVec 32} {x : TableIdx}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f)) :
    QuantsOk (simEnv20 B) (VarEnv.empty.bindVals (tableGetScope (hn := hn) s f i x))
      [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]),
        .expP "x" (.varT "idx" [])] := by
  have hρ := Pure.valsOnly_bindVals (tableGetScope (hn := hn) s f i x)
  exact QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
    (QuantsOk.cons rfl (Whole.typedV_idx20 x _ hρ) QuantsOk.nil))

/-- The left-hand side `z; (CONST I32 i) (TABLE.GET x)`, evaluated. -/
theorem evalExp_tableGetLhs {s : Store H} {f : Frame} {i : BitVec 32} {x : TableIdx} :
    EvalExp (simEnv20 B) (VarEnv.empty.bindVals (tableGetScope (hn := hn) s f i x))
      (.caseE "%;%" (.tupE [.varE "z", .listE [constIE, .caseE "TABLE.GET" (.varE "x")]]))
      (configV hn ⟨s, f, [constI32 i, .plain (.tableGet x)]⟩) :=
  evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (Whole.evalExp_constIE rfl) (evalExps_cons (evalExp_case (evalExp_var rfl)) evalExps_nil), rfl⟩))

/-- **`Step_read/table.get-trap` fires forward** at the image of V2's `tableGetTrap`. -/
theorem fires_tableGetTrap20 {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32}
    {ti : TableInst} (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (hge : ti.refs.length ≤ i.toNat) :
    Fires (simEnv20 B) "Step_read" 9 (.tuple [
      configV hn ⟨s, f, [constI32 i, .plain (.tableGet x)]⟩, .list (adminsToV [.trap])]) := by
  obtain ⟨a, ha, hti⟩ := Whole.table?_some ht
  refine Pure.fires_of_ruleAt hasRuleAt_tableGetTrap20 (tableGetScope (hn := hn) s f i x)
    (quantsOk_tableGet hz) (evalExp_tup2 evalExp_tableGetLhs Whole.evalExp_trapRhs)
    (Pure.prems_one (.ifPr ?_))
  exact evalExp_cmpNum (Whole.evalExp_iPay rfl) (Whole.evalExp_tableLen20 rfl rfl rfl ha hti)
    (by simpa [Num.cmp] using hge)

/-- **`Step_read/table.get-val` fires forward** at the image of V2's `tableGetVal`. -/
theorem fires_tableGetVal20 {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32}
    {ti : TableInst} {r : Ref} (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (hr : ti.refs[i.toNat]? = some r) :
    Fires (simEnv20 B) "Step_read" 10 (.tuple [
      configV hn ⟨s, f, [constI32 i, .plain (.tableGet x)]⟩, .list (adminsToV [aref r])]) := by
  obtain ⟨a, ha, hti⟩ := Whole.table?_some ht
  have hlt : i.toNat < ti.refs.length := by
    rcases List.getElem?_eq_some_iff.1 hr with ⟨h, -⟩
    exact h
  have hres : adminsToV [aref r] = [refV r] :=
    congrArg (fun v => [v]) (Pure.adminToV_toAdmin (.ref r))
  rw [hres]
  refine Pure.fires_of_ruleAt Whole.hasRuleAt_tableGetVal (tableGetScope (hn := hn) s f i x)
    (quantsOk_tableGet hz) (evalExp_tup2 evalExp_tableGetLhs (evalExp_list1 (evalExp_subE_iff.2
      (evalExp_idxE_iff.2 ⟨_, i.toNat, evalExp_dotE_iff.2 ⟨tableInstV ti,
        Whole.evalExp_table20 rfl (evalExp_var rfl) (evalExp_var rfl) ha hti, rfl⟩,
        Whole.evalExp_iPay rfl, by simp [Value.idx?, List.getElem?_map, hr]⟩))))
    (Pure.prems_one (.ifPr ?_))
  exact evalExp_cmpNum (Whole.evalExp_iPay rfl) (Whole.evalExp_tableLen20 rfl rfl rfl ha hti)
    (by simpa [Num.cmp] using hlt)

/-! ## The fragment -/

/-- **V2's `table.get`**, both rules, with their premises. -/
inductive TableGetFwd20 : Config H → Config H → Prop where
  | trap {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32} {ti : TableInst}
      (ht : (⟨s, f⟩ : State H).table? x = some ti) (h : ti.refs.length ≤ i.toNat) :
      TableGetFwd20 ⟨s, f, [constI32 i, .plain (.tableGet x)]⟩ ⟨s, f, [.trap]⟩
  | val {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32} {ti : TableInst} {r : Ref}
      (ht : (⟨s, f⟩ : State H).table? x = some ti) (hr : ti.refs[i.toNat]? = some r) :
      TableGetFwd20 ⟨s, f, [constI32 i, .plain (.tableGet x)]⟩ ⟨s, f, [aref r]⟩

theorem TableGetFwd20.step {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    {c c' : Config H} (h : TableGetFwd20 c c') : Step P host c c' := by
  cases h with
  | trap ht h => exact .read (.tableGetTrap ht h)
  | val ht hr => exact .read (.tableGetVal ht hr)

/-- **`table.get` is a base**, at every builtins and store condition. -/
theorem fwdBase20_tableGet {W : Store H → Prop} : FwdBase20 B hn W (TableGetFwd20 (H := H)) where
  sr _ _ hc h := by
    cases h with
    | trap _ _ => exact typed20_iff.2 ⟨(typed20_iff.1 hc).1, Whole.typedV_admins_trap20⟩
    | val _ _ => exact typed20_iff.2 ⟨(typed20_iff.1 hc).1, Whole.typedV_admins_val20 (.ref _)⟩
  fwd c c' hc _ h := by
    have hz := Whole.typedV_state_of_typed20 hc
    cases h with
    | @trap s f x i ti ht hge =>
      exact Whole.fwdS_read hc (typed20_iff.2 ⟨(typed20_iff.1 hc).1, Whole.typedV_admins_trap20⟩)
        (Whole.sread_of_firesB20 (Whole.firesB_read20_iff.2 (fires_tableGetTrap20 hz ht hge)))
    | @val s f x i ti r ht hr =>
      exact Whole.fwdS_read hc
        (typed20_iff.2 ⟨(typed20_iff.1 hc).1, Whole.typedV_admins_val20 (.ref _)⟩)
        (Whole.sread_of_firesB20 (Whole.firesB_read20_iff.2 (fires_tableGetVal20 hz ht hr)))

end Silmaril.Wasm.SpecTec.Sim20.CallIndGood
