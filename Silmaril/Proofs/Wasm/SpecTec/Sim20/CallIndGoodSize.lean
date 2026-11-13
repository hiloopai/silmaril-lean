module

public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# `table.size` and `memory.size` forward (`Step_read` 11 and 36)

Round 2 proved both rules backwards (`Whole.bwdRead_tableSize`, `Whole.bwdRead_memorySize`); no
forward firing existed. Here each fires at the image of V2's step, from a typed state, with the
same evaluation lemmas (`Whole.evalExp_tableLen20`, `Whole.evalExp_memLen20`,
`Whole.evalExp_ki20`):

* `fires_tableSize20`: `z; TABLE.SIZE x ~> CONST I32 (% n)` with `n` the length of the table;
* `fires_memorySize20`: `z; MEMORY.SIZE ~> CONST I32 (% n)` with `n * 64 * $Ki` the byte size of
  the memory (V2's premise `n * pageSize = |bytes|`, so no whole-pages hypothesis is needed).

`SizeFwd20` is V2's two steps, and `fwdBase20_size` makes it a base fragment for
`Whole.fwd_nest20` at every builtins and store condition.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.CallIndGood

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV stateT QuantsOk evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim20.Whole (FwdBase20 typed20_iff)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-- The result `CONST I32 (% n)`, as a list. -/
theorem adminsToV_constI32 (n : BitVec 32) :
    adminsToV [constI32 n] = [.case "CONST" (.tuple [caseNilV "I32", pctV n.toNat])] := rfl

/-- **`Step_read/table.size` fires forward** at the image of V2's `ReadStep.tableSize`. -/
theorem fires_tableSize20 {s : Store H} {f : Frame} {x : TableIdx} {ti : TableInst} {n : BitVec 32}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (hn' : ti.refs.length = n.toNat) :
    Fires (simEnv20 B) "Step_read" 11
      (.tuple [configV hn ⟨s, f, [.plain (.tableSize x)]⟩, .list (adminsToV [constI32 n])]) := by
  obtain ⟨a, ha, hti⟩ := Whole.table?_some ht
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("x", idxV x), ("n", .num (.natN n.toNat))]
  have hρ : Sim.ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      [.expP "z" (.varT "state" []), .expP "x" (.varT "idx" []), .expP "n" (.varT "n" [])] :=
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (Whole.typedV_idx20 x _ hρ)
      (QuantsOk.cons rfl (Whole.typedV_n20 _ _ hρ) QuantsOk.nil))
  have he : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE "TABLE.SIZE" (.varE "x")]]),
        Whole.constNRhs])
      (.tuple [configV hn ⟨s, f, [.plain (.tableSize x)]⟩, .list (adminsToV [constI32 n])]) :=
    evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var rfl)
      (evalExp_list1 (evalExp_case (evalExp_var rfl)))))
      (evalExp_list1 (Whole.evalExp_constN rfl))
  have hpr : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT Whole.tableLenE (.varE "n")) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, Whole.evalExp_tableLen20 rfl rfl rfl ha hti, evalExp_var rfl,
      cmpValues_eq_true_iff.2 (by rw [hn'])⟩
  exact Pure.fires_of_ruleAt Whole.hasRuleAt_tableSize σ hq he (Pure.prems_one (.ifPr hpr))

/-- `n * 64 * $Ki`, evaluated. -/
theorem evalExp_pages {env : Env} {ρ : VarEnv} {k : Nat}
    (fn : ρ.findVal? "n" = some (.num (.natN k)))
    (hki : EvalExp env ρ (.callE "Ki" []) (.num (.natN 1024))) :
    EvalExp env ρ (.binE .mulOp (.numT .natT) (.binE .mulOp (.numT .natT) (.varE "n")
      (.numE (.natN 64))) (.callE "Ki" [])) (.num (.natN (k * 64 * 1024))) :=
  evalExp_binE_iff.2 ⟨_, evalExp_binE_iff.2 ⟨_, evalExp_var fn, .inr ⟨rfl, _,
    evalExp_numE_iff.2 rfl, rfl⟩⟩, .inr ⟨rfl, _, hki, rfl⟩⟩

/-- **`Step_read/memory.size` fires forward** at the image of V2's `ReadStep.memorySize`. -/
theorem fires_memorySize20 {s : Store H} {f : Frame} {mi : MemInst} {n : BitVec 32}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (hn' : n.toNat * Silmaril.Wasm.Execution.Memory.pageSize = mi.bytes.size) :
    Fires (simEnv20 B) "Step_read" 36
      (.tuple [configV hn ⟨s, f, [.plain .memorySize]⟩, .list (adminsToV [constI32 n])]) := by
  obtain ⟨a, ha, hmi⟩ := Whole.mem?_some hm
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("n", .num (.natN n.toNat))]
  have hρ : Sim.ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      [.expP "z" (.varT "state" []), .expP "n" (.varT "n" [])] :=
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (Whole.typedV_n20 _ _ hρ) QuantsOk.nil)
  have he : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE "MEMORY.SIZE" (.tupE [])]]),
        Whole.constNRhs])
      (.tuple [configV hn ⟨s, f, [.plain .memorySize]⟩, .list (adminsToV [constI32 n])]) :=
    evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var rfl)
      (evalExp_list1 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)))))
      (evalExp_list1 (Whole.evalExp_constN rfl))
  have hsize : n.toNat * 64 * 1024 = mi.bytes.size := by
    rw [← hn']
    show n.toNat * 64 * 1024 = n.toNat * 65536
    omega
  have hpr : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.binE .mulOp (.numT .natT) (.binE .mulOp (.numT .natT) (.varE "n")
        (.numE (.natN 64))) (.callE "Ki" [])) (.lenE (.dotE Whole.mem0E "BYTES"))) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, evalExp_pages rfl (Whole.evalExp_ki20 rfl),
      Whole.evalExp_memLen20 rfl rfl ha hmi, cmpValues_eq_true_iff.2 (by rw [hsize])⟩
  exact Pure.fires_of_ruleAt Whole.hasRuleAt_memorySize σ hq he (Pure.prems_one (.ifPr hpr))

/-! ## The fragment -/

/-- **V2's `table.size` and `memory.size`**, with their premises. -/
inductive SizeFwd20 : Config H → Config H → Prop where
  | table {s : Store H} {f : Frame} {x : TableIdx} {ti : TableInst} {n : BitVec 32}
      (ht : (⟨s, f⟩ : State H).table? x = some ti) (hn : ti.refs.length = n.toNat) :
      SizeFwd20 ⟨s, f, [.plain (.tableSize x)]⟩ ⟨s, f, [constI32 n]⟩
  | memory {s : Store H} {f : Frame} {mi : MemInst} {n : BitVec 32}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hn : n.toNat * Silmaril.Wasm.Execution.Memory.pageSize = mi.bytes.size) :
      SizeFwd20 ⟨s, f, [.plain .memorySize]⟩ ⟨s, f, [constI32 n]⟩

theorem SizeFwd20.step {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    {c c' : Config H} (h : SizeFwd20 c c') : Step P host c c' := by
  cases h with
  | table ht hn => exact .read (.tableSize ht hn)
  | memory hm hn => exact .read (.memorySize hm hn)

/-- **`table.size` and `memory.size` are a base**, at every builtins and store condition. -/
theorem fwdBase20_size {W : Store H → Prop} : FwdBase20 B hn W (SizeFwd20 (H := H)) where
  sr _ _ hc h := by
    cases h with
    | table _ _ | memory _ _ =>
      exact typed20_iff.2 ⟨(typed20_iff.1 hc).1, Whole.typedV_admins_const20 _⟩
  fwd c c' hc _ h := by
    have hz := Whole.typedV_state_of_typed20 hc
    cases h with
    | @table s f x ti n ht hn' =>
      exact Whole.fwdS_read hc (typed20_iff.2 ⟨(typed20_iff.1 hc).1, Whole.typedV_admins_const20 _⟩)
        (Whole.sread_of_firesB20 (Whole.firesB_read20_iff.2 (fires_tableSize20 hz ht hn')))
    | @memory s f mi n hm hn' =>
      exact Whole.fwdS_read hc (typed20_iff.2 ⟨(typed20_iff.1 hc).1, Whole.typedV_admins_const20 _⟩)
        (Whole.sread_of_firesB20 (Whole.firesB_read20_iff.2 (fires_memorySize20 hz hm hn')))

end Silmaril.Wasm.SpecTec.Sim20.CallIndGood
