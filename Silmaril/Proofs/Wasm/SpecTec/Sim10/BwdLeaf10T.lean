module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FiresBack10T

/-!
# The 1.0 leaf rules backwards in `simEnv10T`

Round 2–4 proved every leaf rule of the wasm-1.0 script backwards in `simEnv10 B`: a firing at the
image of a V1 configuration is the image of a V1 step. Their hypothesis is a firing in
`simEnv10 B`. This module re-proves them for firings in `simEnv10T B`, the environment with the
`STORE` erratum, where states whose store holds storing functions, and code with stores, are
typed.

The rules whose quantifiers avoid `tbad10` need nothing new: `fires_back10T` moves their firings
back, and the round 2–4 lemma applies (`BwdT10`). The rules below quantify `state`, `instr*` or
`admininstr*`. Each proof is the round 2–4 proof, re-run over `firesPure10_invT` or
`firesCfg10_invT` (evaluations and premises read in `simEnv10`, quantifier typing in `simEnv10T`):

* `Step_pure`: `if-true`, `if-false`, `label-vals`, `br-zero`, `br-succ`, `return-frame`,
  `return-label`, `trap-vals`, `trap-label`;
* `Step_read`: `block`, `loop`, `call`, `call_indirect-call`, `call_addr`, `local.get`,
  `global.get`, the load rules (`load-num-val` and `load-pack-val` at `bytesB10`);
* `Step`: `local.set`, `global.set`, `memory.grow-succeed` (at `bytesB10`), `memory.grow-fail`.

The typing the proofs read is at types off `tbad10` (`val*`, `labelidx`, `iN`), moved back by
`hasTyp_off10T`. `call_indirect-trap`, `memory.size` and the store rules are in `BwdT10`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression lowerLabel frameTable frameMemory effectiveAddress setGlobal)
open Silmaril.Wasm.Execution.Runtime (Frame GlobalInst FuncInst TableInst MemInst)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV iterPat evalExp_iterPat)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk PremW DDerives otherwise ValsOnly quant_list quant_of
  evalExp_case evalExp_tup2 evalExp_tup3 evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim20.Pure (evalExp_caseNil evalExp_list0 evalExp_list2 evalExp_sub
  immCmp_of_eval ne_zero_of_cmp eq_zero_of_cmp ifPrem quant_val quant_listT evalExp_valsN_inv
  eval_labelVals eval_trapVals eval_returnLabel eval_brZero eval_returnFrame eval_brSucc or_of_eval
  hasTyp_closedAlias labelidxT)
open Silmaril.Wasm.SpecTec.Sim20.Whole (evalExp_subIterPat width_cases evalExp_trapRhs growFailRhs)
open Silmaril.Wasm.SpecTec.Sim.State (idxPayload evalExp_idxPayload)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.StoreAgree (hasTyp_off10T hasTyp_vals10T hasRuleAtT envSame10T
  evalExp_back)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (goodT_of_all)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## The inversions the leaf proofs use, in `simEnv10T` -/

/-- **A firing rule of `simEnv10T`, inverted in `simEnv10`**, with the quantifier typing kept in
`simEnv10T` (the generic `Sim20.Pure.fires_inv`, moved back). -/
theorem fires_invT {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param} {e : Exp}
    {prems : List Prem} (h : HasRuleAt (simEnv10 B) x "%~>%" k (.ruleD nm qs "%~>%" e prems))
    {v : Value} (hf : Fires (simEnv10T B) x k v)
    (hok : prems.all premOkB = true := by decide) :
    ∃ σ, QuantsOk (simEnv10T B) (VarEnv.empty.bindVals σ) qs ∧
      EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) e v ∧
      ∀ pr ∈ prems, PremW (simEnv10 B) (DDerives (simEnv10 B) (otherwise (simEnv10 B)))
        (otherwise (simEnv10 B) x [] k v) (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨σ, hq, he, hp⟩ := Sim20.Pure.fires_inv (hasRuleAtT h) hf
  exact ⟨σ, hq, evalExp_back (envSame10T B) he, prems_back10T hp hok⟩

/-- A `val*` quantifier typed in `simEnv10T` is typed in `simEnv10`. -/
theorem quant_listT10 {ρ : VarEnv} (hρ : ValsOnly ρ) {qs : List Param} {x : IL.Id}
    {t : Typ} (ht : t = .varT "val" []) (hq : QuantsOk (simEnv10T B) ρ qs)
    (hm : Param.expP x (.iterT t .list) ∈ qs) :
    ∃ l, ρ.findVal? x = some (.list l) ∧ HasTyp (simEnv10 B) ρ (.iterT t .list) (.list l) := by
  subst ht
  obtain ⟨l, fl, tl⟩ := quant_listT hq hm
  exact ⟨l, fl, (hasTyp_vals10T B hρ.1).1 tl⟩

/-- `blockParts10`, from a scope typed in `simEnv10T`. -/
theorem blockParts10T {σ : List (IL.Id × Value)} {qs : List Param} {op : MixopS}
    {bt : V1.BlockType} {body : V1.Expr} (hq : QuantsOk (simEnv10T B) (VarEnv.empty.bindVals σ) qs)
    (hm : Param.expP "instr*" (.iterT (.varT "instr" []) .list) ∈ qs)
    (h : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.caseE op (.tupE [optT, iterPat "instr" "instr*"]))
      (.case op (.tuple [blockTypeV bt, .list (instrsToV body)]))) :
    EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) optT (blockTypeV bt) ∧
      (VarEnv.empty.bindVals σ).findVal? "instr*" = some (.list (instrsToV body)) := by
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 h
  obtain rfl := (Value.case.inj hcu).2
  obtain ⟨u₁, u₂, h₁, h₂, he⟩ := Sim.State.evalExp_tup2_inv hu
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨l, fl, -⟩ := quant_list hq hm
  have el := EvalExp.unique h₂ (evalExp_iterPat (by decide) fl)
  rw [← el] at fl
  exact ⟨h₁, fl⟩

/-- `callAddr_quants`, from a scope typed in `simEnv10T`. -/
theorem callAddr_quantsT {σ : List (IL.Id × Value)} {qs : List Param}
    (hq : QuantsOk (simEnv10T B) (VarEnv.empty.bindVals σ) qs)
    (hm : ∀ p ∈ callAddrRule10Qs, p ∈ qs) :
    ∃ ws xv ts is fv₀, (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list ws) ∧
      HasTyp (simEnv10 B) (VarEnv.empty.bindVals σ) (.iterT (.varT "val" []) .list) (.list ws) ∧
      (VarEnv.empty.bindVals σ).findVal? "x" = some xv ∧
      (VarEnv.empty.bindVals σ).findVal? "t*" = some (.list ts) ∧
      (VarEnv.empty.bindVals σ).findVal? "instr*" = some (.list is) ∧
      (VarEnv.empty.bindVals σ).findVal? "f" = some fv₀ := by
  obtain ⟨ws, fws, ht⟩ := quant_listT10 (Sim.valsOnly_bindVals σ) rfl (x := "val*") hq
    (hm _ (by simp))
  obtain ⟨xv, fx⟩ := quant_val (x := "x") (t := .varT "idx" []) hq (hm _ (by simp))
  obtain ⟨ts, fts, -⟩ := quant_list (x := "t*") (t := .varT "valtype" []) hq (hm _ (by simp))
  obtain ⟨is, fis, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (hm _ (by simp))
  obtain ⟨fv₀, ff⟩ := quant_val (x := "f") (t := .varT "frame" []) hq (hm _ (by simp))
  exact ⟨ws, xv, ts, is, fv₀, fws, ht, fx, fts, fis, ff⟩

/-! ## `Step_pure` -/

/-- `Step_pure/trap-label` at any code. -/
theorem bwd10T_trapLabel {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10T B) "Step_pure" 18 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, -, hes, hrh, -⟩ := firesPure10_invT (hasRuleAt10_trapLabel B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain ⟨n, cont, body, rfl⟩ := head10_label (head10_of_caseE ha)
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 ha
  obtain ⟨us, hus, rfl⟩ := evalExp_tupE_iff.1 hu
  obtain ⟨u₁, us₁, -, hus₁, rfl⟩ := evalExps_cons_iff.1 hus
  obtain ⟨u₂, us₂, -, hus₂, rfl⟩ := evalExps_cons_iff.1 hus₁
  obtain ⟨u₃, us₃, h₃, hus₃, rfl⟩ := evalExps_cons_iff.1 hus₂
  obtain rfl := evalExps_nil_iff.1 hus₃
  have hb : Value.list (adminsToV body) = u₃ := by
    simp only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at hcu
    exact hcu.2.2.1
  have hb' : Value.list (adminsToV body) = .list [caseNilV "TRAP"] :=
    hb.trans (EvalExp.unique h₃ (evalExp_list1 evalExp_caseNil))
  obtain ⟨t, rfl, ht⟩ := adminsToV_eq_single10 (Value.list.inj hb')
  obtain rfl := head10_trap (adminToV_case10 ht)
  exact pureBwd10_of (EvalExp.unique hrh (evalExp_list1 evalExp_caseNil)) (.labelTrap n cont)

/-- `Step_pure/if-true` at any code. -/
theorem bwd10T_ifTrue {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10T B) "Step_pure" 5 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, -, hes, hrh, hp⟩ := firesPure10_invT (hasRuleAt10_ifTrue B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨c, rfl, hc⟩ := immCmp10 h₁ (ifPrem (hp _ (.head _)))
  obtain ⟨bt, b₁, b₂, rfl, ht, hb₁, -⟩ := if_parts10 h₂
  exact pureBwd10_of (EvalExp.unique hrh (evalExp_list1 (evalExp_case (evalExp_tup2 ht hb₁))))
    (.ifNonzero bt b₁ b₂ c (ne_zero_of_cmp hc))

/-- `Step_pure/if-false` at any code. -/
theorem bwd10T_ifFalse {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10T B) "Step_pure" 6 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, -, hes, hrh, hp⟩ := firesPure10_invT (hasRuleAt10_ifFalse B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨c, rfl, hc⟩ := immCmp10 h₁ (ifPrem (hp _ (.head _)))
  obtain ⟨bt, b₁, b₂, rfl, ht, -, hb₂⟩ := if_parts10 h₂
  obtain rfl := eq_zero_of_cmp hc
  exact pureBwd10_of (EvalExp.unique hrh (evalExp_list1 (evalExp_case (evalExp_tup2 ht hb₂))))
    (.ifZero bt b₁ b₂)

/-- **`Step_pure/label-vals` backwards**: V1's `labelDone`. -/
theorem bwd10T_labelVals {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10T B) "Step_pure" 7 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, he, -⟩ := fires_invT (hasRuleAt10_labelVals B) hf
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := .varT "n" []) hq (by simp)
  obtain ⟨cs, fc, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, ht⟩ := quant_listT10 (Sim.valsOnly_bindVals σ) rfl (x := "val*") hq (by simp)
  obtain ⟨hl, hw⟩ := tuple_split (EvalExp.unique he (eval_labelVals fn fc fv))
  obtain ⟨n, cont, body, rfl, -, -, hb⟩ := label_of_image (Value.list.inj hl)
  obtain ⟨us, rfl⟩ := values_of_image hb (consts_of_typed10 (Sim.valsOnly_bindVals σ) ht)
  exact pureBwd10_of (hw.trans (congrArg Value.list hb.symm)) (.labelDone n cont us)

/-- **`Step_pure/trap-vals` backwards**: V1's `trapValues` or `trapTail`. -/
theorem bwd10T_trapVals {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10T B) "Step_pure" 17 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, he, hp⟩ := fires_invT (hasRuleAt10_trapVals B) hf
  obtain ⟨ws, fv, ht⟩ := quant_listT10 (Sim.valsOnly_bindVals σ) rfl (x := "val*") hq (by simp)
  obtain ⟨rs, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨hl, hw⟩ := tuple_split (EvalExp.unique he (eval_trapVals fv fi))
  have hor : ws ≠ [] ∨ rs ≠ [] := or_of_eval fv fi (ifPrem (hp _ (List.mem_singleton_self _)))
  obtain ⟨l₁, m, l₃, rfl, h₁, hm, h₃⟩ := split_marked10 (Value.list.inj hl)
  obtain rfl := head10_trap (adminToV_case10 hm)
  obtain ⟨us, rfl⟩ := values_of_image h₁ (consts_of_typed10 (Sim.valsOnly_bindVals σ) ht)
  have hw' : Value.list w = .list (adminsToV [.trap]) := hw
  rcases us with _ | ⟨v, us⟩
  · cases l₃ with
    | nil =>
      exfalso
      rcases hor with h | h
      · exact h (h₁.symm.trans rfl)
      · exact h h₃.symm
    | cons i tail => exact pureBwd10_of hw' (.trapTail i tail)
  · exact pureBwd10_of hw' (.trapValues v us l₃)

/-- **`Step_pure/return-label` backwards**: V1's `labelReturn`. -/
theorem bwd10T_returnLabel {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10T B) "Step_pure" 16 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, he, -⟩ := fires_invT (hasRuleAt10_returnLabel B) hf
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := .varT "n" []) hq (by simp)
  obtain ⟨cs, fc, -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, ht⟩ := quant_listT10 (Sim.valsOnly_bindVals σ) rfl (x := "val*") hq (by simp)
  obtain ⟨rs, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨hl, hw⟩ := tuple_split (EvalExp.unique he (eval_returnLabel fn fc fv fi))
  obtain ⟨n, cont, body, rfl, -, -, hb⟩ := label_of_image (Value.list.inj hl)
  obtain ⟨l₁, m, l₃, rfl, h₁, hm, -⟩ := split_marked10 (by simpa using hb)
  obtain rfl := head10_return (adminToV_case10 hm)
  obtain ⟨us, rfl⟩ := values_of_image h₁ (consts_of_typed10 (Sim.valsOnly_bindVals σ) ht)
  have hw' : Value.list w = .list (adminsToV (values us ++ [.source .return_])) := by
    rw [hw, adminsToV_map10, List.map_append, ← adminsToV_map10, h₁]
    rfl
  exact pureBwd10_of hw' (.labelReturn n cont us l₃)

/-- **`Step_pure/br-zero` backwards**: V1's `labelBranch`. -/
theorem bwd10T_brZero {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10T B) "Step_pure" 8 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, he, -⟩ := fires_invT (hasRuleAt10_brZero B) hf
  obtain ⟨cs, fc, -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws₁, fv₁, ht₁⟩ := quant_listT10 (Sim.valsOnly_bindVals σ) rfl (x := "val'*") hq (by simp)
  obtain ⟨ws', fv', ht⟩ := quant_listT10 (Sim.valsOnly_bindVals σ) rfl (x := "val*") hq (by simp)
  obtain ⟨rs, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨v₁, v₂, h₁, -, -⟩ := evalExp_catE_iff.1 (Sim.RefsGC.rhs_of_concl he)
  obtain ⟨ws, fv, fn, -⟩ := evalExp_valsN_inv (by decide) h₁
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  obtain ⟨hl, hw⟩ := tuple_split (EvalExp.unique he (eval_brZero fn fc fv₁ fv fi))
  obtain ⟨n, cont, body, rfl, hn, hc, hb⟩ := label_of_image (Value.list.inj hl)
  have hb₂ : adminsToV body = (ws₁ ++ ws) ++ .case "BR" (pctV 0) :: rs := by
    rw [hb]
    simp only [List.append_assoc, List.singleton_append]
  obtain ⟨extra, us, m, l₃, rfl, hb', hm⟩ := split_vals_marked10 hb₂ ht₁ (ew ▸ ht)
  obtain ⟨l, rfl⟩ := head10_br (adminToV_case10 hm)
  have hl0 : l = ⟨0⟩ := Idx.toNat_injective (Sim20.Pure.pctV_inj (Value.case.inj hm).2)
  have hlen : us.length = n := by
    rw [Sim.Bwd.natN_inj hn, ← hb', adminsToV_values, List.length_map]
  have hw' : Value.list w = .list (adminsToV (values us ++ expression cont)) := by
    rw [hw, adminsToV_map10, List.map_append, ← adminsToV_map10, ← adminsToV_map10, hb',
      adminsToV_expression, hc]
  exact hl0 ▸ pureBwd10_of hw' (.labelBranch n cont extra us l₃ hlen)

/-- **`Step_pure/return-frame` backwards**: V1's `frameReturn`. -/
theorem bwd10T_returnFrame {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10T B) "Step_pure" 15 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, he, -⟩ := fires_invT (hasRuleAt10_returnFrame B) hf
  obtain ⟨vf, ff⟩ := quant_val (x := "f") (t := .varT "frame" []) hq (by simp)
  obtain ⟨ws₁, fv₁, ht₁⟩ := quant_listT10 (Sim.valsOnly_bindVals σ) rfl (x := "val'*") hq (by simp)
  obtain ⟨ws', fv', ht⟩ := quant_listT10 (Sim.valsOnly_bindVals σ) rfl (x := "val*") hq (by simp)
  obtain ⟨rs, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, fn, -⟩ := evalExp_valsN_inv (by decide) (Sim.RefsGC.rhs_of_concl he)
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  obtain ⟨hl, hw⟩ := tuple_split (EvalExp.unique he (eval_returnFrame fn ff fv₁ fv fi))
  obtain ⟨n, fr, body, rfl, hn, hb⟩ := frame_of_image (Value.list.inj hl)
  have hb₂ : adminsToV body = (ws₁ ++ ws) ++ caseNilV "RETURN" :: rs := by
    rw [hb]
    simp only [List.append_assoc, List.singleton_append]
  obtain ⟨extra, us, m, l₃, rfl, hb', hm⟩ := split_vals_marked10 hb₂ ht₁ (ew ▸ ht)
  obtain rfl := head10_return (adminToV_case10 hm)
  have hlen : us.length = n := by
    rw [Sim.Bwd.natN_inj hn, ← hb', adminsToV_values, List.length_map]
  exact pureBwd10_of (hw.trans (congrArg Value.list hb'.symm)) (.frameReturn n fr extra us l₃ hlen)

/-- **`Step_pure/br-succ` backwards**: V1's `labelBranchOuter`. -/
theorem bwd10T_brSucc {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10T B) "Step_pure" 9 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, he, -⟩ := fires_invT (hasRuleAt10_brSucc B) hf
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := .varT "n" []) hq (by simp)
  obtain ⟨cs, fc, -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, ht⟩ := quant_listT10 (Sim.valsOnly_bindVals σ) rfl (x := "val*") hq (by simp)
  obtain ⟨lv, fl, hlt⟩ := hq "l" labelidxT (by simp)
  obtain ⟨k, rfl⟩ := labelidx10_inv (Sim.valsOnly_bindVals σ)
    ((hasTyp_off10T B (Sim.valsOnly_bindVals σ).1 (goodT_of_all (by decide))).1 hlt)
  obtain ⟨rs, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨hl, hw⟩ := tuple_split (EvalExp.unique he (eval_brSucc fn fc fv fl fi))
  obtain ⟨n, cont, body, rfl, -, -, hb⟩ := label_of_image (Value.list.inj hl)
  obtain ⟨l₁, m, l₃, rfl, h₁, hm, -⟩ := split_marked10 (by simpa using hb)
  obtain ⟨l, rfl⟩ := head10_br (adminToV_case10 hm)
  have hk : l.toNat = k + 1 := Sim20.Pure.pctV_inj (Value.case.inj hm).2
  obtain ⟨us, rfl⟩ := values_of_image h₁ (consts_of_typed10 (Sim.valsOnly_bindVals σ) ht)
  have hw' : Value.list w = .list (adminsToV (values us ++ [.source (.br (lowerLabel l))])) := by
    rw [hw, adminsToV_map10, List.map_append, ← adminsToV_map10, h₁]
    show Value.list (ws ++ [.case "BR" (pctV k)]) = .list (ws ++ [.case "BR" (pctV (l.toNat - 1))])
    rw [hk, Nat.add_sub_cancel]
  exact pureBwd10_of hw' (.labelBranchOuter n cont us l₃ l (by omega))


/-! ## `Step_read` -/

/-- **`Step_read/loop` backwards**: V1's `PureStep.loop`. -/
theorem bwd10T_loop {host : HostSemantics H} {c : Config H} {w : List Value}
    (hf : Fires (simEnv10T B) "Step_read" 1 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, -, hes, hrh, -⟩ := firesCfg10_invT (hasRuleAt10_loop B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain ⟨bt, body, rfl⟩ := head10_loop (head10_of_caseE ha)
  obtain ⟨-, fb⟩ := blockParts10T hq (by simp) ha
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "LABEL_%{%}%" (.tupE [.numE (.natN 0), .listE [loopE], instrsAdmE])])
      (.list (adminsToV [.label 0 [.loop bt body] (expression body)])) := by
    have hv : adminsToV [.label 0 [.loop bt body] (expression body)] =
        [.case "LABEL_%{%}%" (.tuple [.num (.natN 0), .list [adminToV (.source (.loop bt body))],
          .list (instrsToV body)])] := by
      show [adminToV _] = _
      simp only [adminToV, adminsToV_expression]
      rfl
    rw [hv]
    exact evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_numE_iff.2 rfl) (evalExp_list1 ha)
      (evalExp_subIterPat (by decide) fb)))
  exact ⟨_, Value.list.inj (EvalExp.unique hrh he), .pure s f (.loop bt body)⟩

/-- **`Step_read/block` backwards**: V1's `PureStep.block`. -/
theorem bwd10T_block {host : HostSemantics H} {c : Config H} {w : List Value}
    (hf : Fires (simEnv10T B) "Step_read" 0 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, -, hes, hrh, hp⟩ := firesCfg10_invT (hasRuleAt10_block B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain ⟨bt, body, rfl⟩ := head10_block (head10_of_caseE ha)
  obtain ⟨ht, fb⟩ := blockParts10T hq (by simp) ha
  obtain ⟨N, fN, -⟩ := quant_of (x := "n") (t := .varT "n" []) hq (by simp)
  have hN : N = .num (.natN bt.toList.length) :=
    block_arity10 ht fN (Sim20.Pure.ifPrem (hp _ (.head _)))
  have hv : adminsToV [.label bt.toList.length [] (expression body)] =
      [.case "LABEL_%{%}%" (.tuple [.num (.natN bt.toList.length), .list [],
        .list (instrsToV body)])] := by
    show [adminToV _] = _
    simp only [adminToV, adminsToV_expression]
    rfl
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "LABEL_%{%}%" (.tupE [.varE "n", .listE [], instrsAdmE])])
      (.list (adminsToV [.label bt.toList.length [] (expression body)])) :=
    hv ▸ evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var (hN ▸ fN)) evalExp_list0
      (evalExp_subIterPat (by decide) fb)))
  exact ⟨_, Value.list.inj (EvalExp.unique hrh he), .pure s f (.block bt body)⟩

/-- **`Step_read/local.get` backwards**, at a `GoodV1` configuration. -/
theorem bwd10T_localGet {host : HostSemantics H} {c : Config H} {w : List Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10T B) "Step_read" 6 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, -⟩ := firesCfg10_invT (hasRuleAt10_localGet B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain ⟨x, rfl⟩ := head10_localGet (head10_of_caseE ha)
  have hr : x.toNat < f.locals.length := instrResOk_of_good hg
  obtain ⟨v, hv⟩ : ∃ v, f.locals[x.toNat]? = some v := ⟨_, List.getElem?_eq_getElem hr⟩
  have hx := idx_of_caseE10 ha rfl
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.listE [.subE (.callE "local" [.expA (.varE "z"),
      .expA (.varE "x")]) (.varT "val" []) (.varT "admininstr" [])]) (.list (adminsToV [value v])) := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
    exact evalExp_list1 (evalExp_subE_iff.2 (evalExp_local10 rfl (evalExp_var fz) hx hv))
  exact ⟨[value v], Value.list.inj (EvalExp.unique hrh he), .localGet s f x v hv⟩

/-- **`Step_read/global.get` backwards**, at a `GoodV1` configuration. -/
theorem bwd10T_globalGet {host : HostSemantics H} {c : Config H} {w : List Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10T B) "Step_read" 7 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, -⟩ := firesCfg10_invT (hasRuleAt10_globalGet B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain ⟨x, rfl⟩ := head10_globalGet (head10_of_caseE ha)
  obtain ⟨ad, g, had, hgl⟩ : ∃ ad g, f.module.globals[x.toNat]? = some ad ∧
      s.globals[ad.value]? = some g := instrResOk_of_good hg
  have hx := idx_of_caseE10 ha rfl
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.listE [.subE (.dotE (.callE "global" [.expA (.varE "z"),
      .expA (.varE "x")]) "VALUE") (.varT "val" []) (.varT "admininstr" [])])
      (.list (adminsToV [value g.value])) := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
    exact evalExp_list1 (evalExp_subE_iff.2 (evalExp_dotE_iff.2
      ⟨_, evalExp_global10 rfl (evalExp_var fz) hx had hgl, rfl⟩))
  exact ⟨[value g.value], Value.list.inj (EvalExp.unique hrh he),
    .globalGet s f x ad g had hgl⟩

/-- **`Step_read/call` backwards**, at a `GoodV1` configuration. -/
theorem bwd10T_call {host : HostSemantics H} {c : Config H} {w : List Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10T B) "Step_read" 2 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, -⟩ := firesCfg10_invT (hasRuleAt10_call B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain ⟨x, rfl⟩ := head10_call (head10_of_caseE ha)
  have hr : (f.module.funcs[x.toNat]?).isSome := instrResOk_of_good hg
  obtain ⟨fa, hfa⟩ := Option.isSome_iff_exists.1 hr
  have hx := idx_of_caseE10 ha rfl
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CALL_ADDR" (.idxE (.callE "funcaddr" [.expA (.varE "z")]) idxPayload)])
      (.list (adminsToV [.invoke fa])) :=
    evalExp_list1 (evalExp_case (evalExp_idxE_iff.2 ⟨_, x.toNat,
      evalExp_funcaddr10 rfl (evalExp_var fz), evalExp_idxPayload (evalExp_varE_iff.1 hx),
      by simp [Value.idx?, addrsV, List.getElem?_map, hfa]⟩))
  exact ⟨[.invoke fa], Value.list.inj (EvalExp.unique hrh he), .call s f x fa hfa⟩

/-- **`Step_read/call_addr` backwards**, at a `GoodV1` configuration: V1's `invokeWasm`. -/
theorem bwd10T_callAddr {host : HostSemantics H} {c : Config H} {w : List Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10T B) "Step_read" 5 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, he, hp⟩ := fires_invT (hasRuleAt10_callAddr B) hf
  obtain ⟨ws, xv, ts, is, fv₀, fws, ht, fx, fts, fis, ff⟩ := callAddr_quantsT hq fun _ h => h
  obtain ⟨args, fa, rfl, fz, fv, fk, fA⟩ := lhs_callAddr10 fws ht (Sim.RefsGC.lhs_of_concl he)
  obtain ⟨ft, m, fn, hfi, fk', fn', fm, ffn⟩ := prem1_of_eval10 fz fA rfl
    (func_of_prem2 (Sim20.Pure.ifPrem (hp _ (.tail _ (.head _))))) (Sim20.Pure.ifPrem (hp _ (.head _)))
  have hcode : ts = fn.locals.map valTypeV ∧ is = instrsToV fn.body :=
    code_of_eval10 ffn fx fts fis (Sim20.Pure.ifPrem (hp _ (.tail _ (.head _))))
  have hF : fv₀ = frameV ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩ :=
    frame_of_eval10 rfl ff fk fv (hcode.1 ▸ fts) fm
      (Sim20.Pure.ifPrem (hp _ (.tail _ (.tail _ (.head _)))))
  have harity : args.length = ft.params.length := by
    simpa using Sim.Bwd.natN_inj (Option.some.inj (fk.symm.trans fk'))
  have hres : ft.results.length ≤ 1 := hg.2.1.1 _ (List.mem_of_getElem? hfi)
  have hw : w = adminsToV [.frame ft.results.length
      ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩
      [.label ft.results.length [] (expression fn.body)]] := by
    rw [adminsToV_callFrame10, ← hF]
    exact Value.list.inj (EvalExp.unique (Sim.RefsGC.rhs_of_concl he)
      (evalExp_callAddrRhs fn' ff (hcode.2 ▸ fis)))
  exact ⟨_, hw, .invokeWasm s f fa ft m fn args hfi harity hres⟩

/-- **`Step_read/call_indirect-call` backwards**, at a `GoodV1` configuration. -/
theorem bwd10T_callIndirect {host : HostSemantics H} {c : Config H} {w : List Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10T B) "Step_read" 3 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ := firesCfg10_invT (hasRuleAt10_callIndirect B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨i, rfl, fi⟩ := constI32_of_lhs10 h₁
  obtain ⟨x, rfl⟩ := head10_callIndirect (head10_of_caseE h₂)
  have hres : (frameTable s f).isSome ∧ (f.module.types[x.toNat]?).isSome := hg.1.2.1
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hres.1
  obtain ⟨ft, hft⟩ := Option.isSome_iff_exists.1 hres.2
  obtain ⟨fa, hent, fa'⟩ := entry_of_eval10 fz (evalExp_varE_iff.1 fi) ht rfl
    (Sim20.Pure.ifPrem (hp _ (.head _)))
  have hlt : fa.value < s.funcs.length := by
    obtain ⟨ta, -, hta⟩ := frameTable_some ht
    exact hg.2.1.2 t (List.mem_of_getElem? hta) fa (List.mem_of_getElem? hent)
  have hfn : s.funcs[fa.value]? = some s.funcs[fa.value] := List.getElem?_eq_getElem hlt
  have hty : s.funcs[fa.value].type = ft := typeMatch_of_eval10 fz (idx_of_caseE10 h₂ rfl |>
    evalExp_varE_iff.1) fa' hft hfn rfl rfl (Sim20.Pure.ifPrem (hp _ (.tail _ (.head _))))
  have hw : w = adminsToV [.invoke fa] :=
    Value.list.inj (EvalExp.unique hrh (evalExp_list1 (evalExp_case (evalExp_var fa'))))
  exact ⟨_, hw, .callIndirect s f x i t fa _ ft ht hft hent hfn hty⟩

/-- **`Step_read/load-num-trap` backwards**, at a `GoodV1` configuration. -/
theorem bwd10T_loadNumTrap {host : HostSemantics H} {c : Config H} {w : List Value}
    (hg : GoodV1 c) (hf : Fires (simEnv10T B) "Step_read" 8 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ := firesCfg10_invT (hasRuleAt10_loadNumTrap B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨i, rfl, fi⟩ := constI32_of_lhs10 h₁
  obtain ⟨t, ao, ft, fa, hd⟩ := loadNum_decode h₂
  have ew : w = adminsToV [.trap] := Value.list.inj (EvalExp.unique hrh evalExp_trapRhs)
  have hlt : ∀ a m, frameMemory s f = some (a, m) →
      m.data.size < effectiveAddress i ao + t.width / 8 := fun a m hm =>
    trap_of_prem10 fz (evalExp_varE_iff.1 fi) fa (evalExp_size10 t rfl (evalExp_var ft))
      (width_cases t) hm (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  rcases hd with ⟨t', rfl, rfl⟩ | ⟨t', rfl, rfl⟩
  · obtain ⟨a, m, hm⟩ := mem_of_good2 hg (fun h => h)
    exact ⟨_, ew, step_intLoadTrap hm (hlt a m hm)⟩
  · obtain ⟨a, m, hm⟩ := mem_of_good2 hg (fun h => h)
    exact ⟨_, ew, step_floatLoadTrap hm (hlt a m hm)⟩

/-- **`Step_read/load-pack-trap` backwards**, at a `GoodV1` configuration. -/
theorem bwd10T_loadPackTrap {host : HostSemantics H} {c : Config H} {w : List Value}
    (hg : GoodV1 c) (hf : Fires (simEnv10T B) "Step_read" 10 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ := firesCfg10_invT (hasRuleAt10_loadPackTrap B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨i, rfl, fi⟩ := constI32_of_lhs10 h₁
  obtain ⟨t, sz, sx, ao, rfl, fa, fn⟩ := loadPack_decode h₂
  have ew : w = adminsToV [.trap] := Value.list.inj (EvalExp.unique hrh evalExp_trapRhs)
  obtain ⟨a, m, hm⟩ := mem_of_good2 hg (fun h => h)
  have hlt : m.data.size < effectiveAddress i ao + sz.width / 8 :=
    trap_of_prem10 fz (evalExp_varE_iff.1 fi) fa (evalExp_var fn) (packWidth10_cases sz) hm
      (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨_, ew, step_intLoadTrap hm hlt⟩

/-- **`Step_read/load-num-val` backwards** at `bytesB10`, at a `GoodV1` configuration. -/
theorem bwd10T_loadNumVal {P : Profile} {host : HostSemantics H} {c : Config H} {w : List Value}
    (hg : GoodV1 c)
    (hf : Fires (simEnv10T (bytesB10 P)) "Step_read" 9 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes, hrh, hp⟩ := firesCfg10_invT (hasRuleAt10_loadNumVal' _) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨i, rfl, fi⟩ := constI32_of_lhs10 h₁
  obtain ⟨t, ao, ft, fa, hd⟩ := loadNum_decode h₂
  obtain ⟨cv, fc, -⟩ := hq "c" (.varT "val_" [.expA (.varE "t")]) (by simp)
  obtain ⟨b, hval, hread⟩ := loadNumVal_scope fz (evalExp_varE_iff.1 fi) ft fa fc rfl rfl rfl hrh
    (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  rcases hd with ⟨t', rfl, rfl⟩ | ⟨t', rfl, rfl⟩
  · obtain ⟨a, m, hm⟩ := mem_of_good2 hg (fun h => h)
    exact ⟨_, hval, .intLoad s f t' none ao i a m _ hm (loadInt_of_readBytes (hread a m hm))⟩
  · obtain ⟨a, m, hm⟩ := mem_of_good2 hg (fun h => h)
    exact ⟨_, hval, .floatLoad s f t' ao i a m _ hm (loadFloat_of_readBytes (hread a m hm))⟩

/-- **`Step_read/load-pack-val` backwards** at `bytesB10`, at a `GoodV1` configuration. -/
theorem bwd10T_loadPackVal {P : Profile} {host : HostSemantics H} {c : Config H} {w : List Value}
    (hg : GoodV1 c)
    (hf : Fires (simEnv10T (bytesB10 P)) "Step_read" 11 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes, hrh, hp⟩ := firesCfg10_invT (hasRuleAt10_loadPackVal' _) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨i, rfl, fi⟩ := constI32_of_lhs10 h₁
  obtain ⟨t, sz, sx, ao, rfl, fa, fn, fInn, fsx⟩ := loadPack_decode' h₂
  obtain ⟨cv, fc, hty⟩ := hq "c" (.varT "iN" [.expA (.varE "n")]) (by simp)
  obtain ⟨k, rfl, hk⟩ := iN_inv_lt10 (Sim.evalExp_var fn)
    ((hasTyp_off10T _ (Sim.valsOnly_bindVals σ).1 (goodT_of_all (by decide))).1 hty)
  let x : BitVec sz.width := BitVec.ofNat _ k
  have hxk : x.toNat = k := by simp [x, Nat.mod_eq_of_lt hk]
  have fc' : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV x.toNat) := by rw [hxk]; exact fc
  have hrhs : EvalExp (simEnv10 (bytesB10 P)) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [innE10, extendE10])])
      (.list (adminsToV [value ⟨.int t, extPack10 t sx x⟩])) := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
    exact Sim.evalExp_list1 (Sim.evalExp_case (Sim.evalExp_tup2
      (evalExp_subE_iff.2 (Sim.evalExp_var fInn)) (evalExp_extend10 rfl rfl fInn fn fsx fc')))
  have hval : w = adminsToV [value ⟨.int t, extPack10 t sx x⟩] :=
    Value.list.inj (EvalExp.unique hrh hrhs)
  have hprem := Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _))
  obtain ⟨u, hu₁, hu₂⟩ := eq_of_evalExp_eqTrue hprem
  have hub : u = bytesV (Execution.Memory.encodeLE (sz.width / 8) x.toNat) :=
    EvalExp.unique hu₁ (evalExp_ibytesCall10 rfl fn fc')
  obtain ⟨a, m, hm⟩ := mem_of_good2 hg (fun h => h)
  obtain ⟨r, hr, hur⟩ := loadSlice10_inv fz (evalExp_varE_iff.1 fi) fa rfl
    (Sim.evalExp_var fn) (packWidth10_cases sz) hm hu₂
  have hread : Execution.Memory.readBytes m.data (effectiveAddress i ao) (sz.width / 8) =
      some (Execution.Memory.encodeLE (sz.width / 8) x.toNat) := by
    rw [hr, bytesV10_injective (hur.symm.trans hub)]
  exact ⟨_, hval, .intLoad s f t (some (sz, sx)) ao i a m _ hm (loadPack_of_readBytes hread)⟩


/-! ## `Step` -/

/-- **`Step/local.set` backwards**, at a `GoodV1` configuration. -/
theorem bwd10T_localSet {host : HostSemantics H} {c : Config H} {w : Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10T B) "Step" 5 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes, hrh, -⟩ := firesCfg10_invT (hasRuleAt10_localSet B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨v, rfl, fv⟩ := val10_of_varT hq (by simp) h₁
  obtain ⟨x, rfl⟩ := head10_localSet (head10_of_caseE h₂)
  have hr : x.toNat < f.locals.length := by
    have h := hg.1
    simp only [ResOkL10] at h
    exact h.2.1
  have hx := idx_of_caseE10 h₂ rfl
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.callE "with_local" [.expA (.varE "z"), .expA (.varE "x"),
        .expA (.varE "val")], .listE []]))
      (configV hn ⟨s, { f with locals := f.locals.set x.toNat v }, []⟩) :=
    evalExp_case (evalExp_tup2 (evalExp_withLocal10 rfl (evalExp_var fz) hx (evalExp_var fv) hr)
      evalExp_list0)
  obtain ⟨old, hold⟩ : ∃ old, f.locals[x.toNat]? = some old := ⟨_, List.getElem?_eq_getElem hr⟩
  exact ⟨_, EvalExp.unique hrh he, .localSet s f x v old hold⟩

/-- **`Step/global.set` backwards**, at a `GoodV1` configuration. -/
theorem bwd10T_globalSet {host : HostSemantics H} {c : Config H} {w : Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10T B) "Step" 6 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes, hrh, -⟩ := firesCfg10_invT (hasRuleAt10_globalSet B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨v, rfl, fv⟩ := val10_of_varT hq (by simp) h₁
  obtain ⟨x, rfl⟩ := head10_globalSet (head10_of_caseE h₂)
  obtain ⟨ad, g, had, hgl, hmut⟩ : ∃ ad g, f.module.globals[x.toNat]? = some ad ∧
      s.globals[ad.value]? = some g ∧ g.mutability = .var := by
    have h := hg.1
    simp only [ResOkL10, ResOkA10, InstrResOk10] at h
    exact h.2.1
  have ht : v.type = g.value.type := hg.2.2.2 f v x ad g (activeF_self _ _) had hgl
  have hx := idx_of_caseE10 h₂ rfl
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.callE "with_global" [.expA (.varE "z"), .expA (.varE "x"),
        .expA (.varE "val")], .listE []]))
      (configV hn ⟨setGlobal s ad { g with value := v }, f, []⟩) :=
    evalExp_case (evalExp_tup2 (evalExp_withGlobal10 rfl (evalExp_var fz) hx (evalExp_var fv)
      had hgl ht) evalExp_list0)
  exact ⟨_, EvalExp.unique hrh he, .globalSet s f x ad g v had hgl hmut⟩

/-- **`Step/memory.grow-succeed` backwards** at `bytesB10`, at a `GoodV1` configuration: V1's
`memoryGrow` with `Memory.Grow.success`. -/
theorem bwd10T_memGrowSucceed {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodV1 c) (hf : Fires (simEnv10T (bytesB10 P)) "Step" 11 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ := firesCfg10_invT (hasRuleAt10_memGrowSucceed _) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨n, rfl, hn⟩ := constI32_of_lhs10 h₁
  have fn := var_of_pct10 hn
  obtain rfl := head10_memoryGrow (head10_of_caseE h₂)
  obtain ⟨a, m, hfm, -⟩ := memory_of_good hg
  obtain ⟨d, hgr, fmi⟩ := growPrem10_inv (evalExp_mem0_10 rfl fz hfm) fn rfl
    (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  obtain ⟨hal, hlt⟩ := grow_bounds10 hgr
  exact ⟨_, EvalExp.unique hrh (growRhs10 rfl rfl rfl fz fmi hfm hal hlt),
    .memoryGrow s f a m n _ d hfm (.success d hgr)⟩

/-- **`Step/memory.grow-fail` backwards**, at a `GoodV1` configuration: V1's `memoryGrow` with
`Memory.Grow.failure`. -/
theorem bwd10T_memGrowFail {host : HostSemantics H} {c : Config H} {w : Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10T B) "Step" 12 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, -⟩ := firesCfg10_invT (hasRuleAt10_memGrowFail B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨n, rfl, -⟩ := constI32_of_lhs10 h₁
  obtain rfl := head10_memoryGrow (head10_of_caseE h₂)
  obtain ⟨a, m, hfm, hsm⟩ := memory_of_good hg
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) growFailRhs
      (configV hn ⟨s, f, [value ⟨.int .i32, -1⟩]⟩) :=
    evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case (evalExp_tup2
      (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_minusOne10 rfl) evalExps_nil,
        rfl⟩))))))
  exact ⟨_, EvalExp.unique hrh he, step_memGrowFail hfm hsm⟩


end Silmaril.Wasm.SpecTec.Sim10.Whole
