module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMPure.Exits

/-!
# Round 9, rm: `if` and the branch and return exits of `Step_pure` at `adminsToVD` (unrefined)

Round 6's leaves (`Sim.bwd_ifTrue`, `bwd_ifFalse`, `Bwd.bwd_brLabelZero`, `Sim.bwd_brLabelSucc`,
`bwd_brHandler`, `Bwd.bwd_returnFrame`, `Sim.bwd_returnLabel`, `bwd_returnHandler`), re-run at
`adminsToVD`. Rules 5, 6, 8, 9, 10, 22, 23, 24.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMPure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat valsPat valsNPat evalExp_iterPat
  evalExp_valsPat)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round7.MemSimd (adminsToVD adminToVD instrsToVD adminsToVD_eq_single adminsToVD_eq_pair
  adminsToVD_append adminsToVD_vals)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- `CONST I32 c` at `adminToVD`. -/
theorem constI32D_of (B : Builtins) {a : Admin} {c' : Value}
    (h : adminToVD a = .case "CONST" (.tuple [caseNilV "I32", c'])) :
    ∃ c : BitVec 32, a = constI32 c ∧ c' = pctV c.toNat := by
  have h' := toV_of_atomD h rfl
  obtain ⟨c, rfl⟩ := (Typing.ctrlDecode_simEnv B).constI32 a c' h'
  exact ⟨c, rfl, constI32_imm h'⟩

/-- `BR l` at `adminToVD`. -/
theorem brD_of (B : Builtins) {a : Admin} {x : Value} (h : adminToVD a = .case "BR" x) :
    ∃ l, a = .plain (.br l) ∧ adminToV a = .case "BR" x := by
  have h' := toV_of_atomD h rfl
  obtain ⟨l, rfl⟩ := (Typing.ctrlDecode_simEnv B).br a x h'
  exact ⟨l, rfl, h'⟩

/-- `RETURN` at `adminToVD`. -/
theorem retD_of (B : Builtins) {a : Admin} (h : adminToVD a = caseNilV "RETURN") :
    a = .plain .return_ :=
  (Typing.ctrlDecode_simEnv B).ret a (toV_of_atomD (op := "RETURN") h rfl)

theorem bwdD_ifTrue (B : Builtins) : LeafD B P host 5 := by
  intro s f is w hf
  obtain ⟨σ, -, he, hp⟩ := ruleBody_scope (fires_body (simEnv_execRules B).ifTrue hf)
  have hc : ∃ c' bt' v₁ v₂ v₁', adminsToVD is = [.case "CONST" (.tuple [caseNilV "I32", c']),
      .case "IF%%ELSE%" (.tuple [bt', v₁, v₂])] ∧ w = .list [.case "BLOCK" (.tuple [bt', v₁'])] ∧
      (VarEnv.empty.bindVals σ).findVal? "c" = some c' ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (iterPat "instr_1" "instr_1*") v₁ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (iterPat "instr_1" "instr_1*") v₁' := by
    concl_inv he
  obtain ⟨c', bt', v₁, v₂, v₁', his, rfl, hcv, e₁, e₁'⟩ := hc
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToVD_eq_pair his
  obtain ⟨c, rfl, hc'⟩ := constI32D_of B h₁
  obtain ⟨bt, b₁, b₂, rfl, hbt, hb₁, -⟩ := ifD_of h₂
  have hv : v₁' = v₁ := EvalExp.unique e₁' e₁
  have hne : c.toNat ≠ 0 := immNe_of_eval (hc' ▸ hcv) (ifPrem (hp _ (by simp)))
  refine ⟨[.plain (.block bt b₁)], ?_, .ifTrue (ne_zero_of_toNat hne)⟩
  rw [hv, hbt, hb₁]
  rfl

theorem bwdD_ifFalse (B : Builtins) : LeafD B P host 6 := by
  intro s f is w hf
  obtain ⟨σ, -, he, hp⟩ := ruleBody_scope (fires_body (simEnv_execRules B).ifFalse hf)
  have hc : ∃ c' bt' v₁ v₂ v₂', adminsToVD is = [.case "CONST" (.tuple [caseNilV "I32", c']),
      .case "IF%%ELSE%" (.tuple [bt', v₁, v₂])] ∧ w = .list [.case "BLOCK" (.tuple [bt', v₂'])] ∧
      (VarEnv.empty.bindVals σ).findVal? "c" = some c' ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (iterPat "instr_2" "instr_2*") v₂ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (iterPat "instr_2" "instr_2*") v₂' := by
    concl_inv he
  obtain ⟨c', bt', v₁, v₂, v₂', his, rfl, hcv, e₂, e₂'⟩ := hc
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToVD_eq_pair his
  obtain ⟨c, rfl, hc'⟩ := constI32D_of B h₁
  obtain ⟨bt, b₁, b₂, rfl, hbt, -, hb₂⟩ := ifD_of h₂
  have hv : v₂' = v₂ := EvalExp.unique e₂' e₂
  have h0 : c.toNat = 0 := immEq_of_eval (hc' ▸ hcv) (ifPrem (hp _ (by simp)))
  obtain rfl := eq_zero_of_toNat h0
  refine ⟨[.plain (.block bt b₂)], ?_, .ifFalse⟩
  rw [hv, hbt, hb₂]
  rfl

/-- A body `val* x instr*` at `adminsToVD`, with the prefix typed. -/
theorem splitD_of (B : Builtins) {σ : List (IL.Id × Value)} {body : List Admin}
    {ws rest : List Value} {x : Value} (h : adminsToVD body = ws ++ [x] ++ rest)
    (ht : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) valsT (.list ws)) :
    ∃ vs b rest', body = vals vs ++ [b] ++ rest' ∧ adminsToV (vals vs) = ws ∧ adminToVD b = x ∧
      ws.length = vs.length := by
  obtain ⟨b₁, b, b₂, rfl, h₁, hb, -⟩ := adminsToVD_eq_split h
  obtain ⟨vs, rfl, hv, hlen⟩ := valsD_of h₁ ht
  exact ⟨vs, b, b₂, rfl, hv, hb, hlen⟩

theorem bwdD_brHandler (B : Builtins) : LeafD B P host 10 := by
  intro s f is w hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).brHandler hf)
  have hc : ∃ n' cs' v₃, adminsToVD is = [.case "HANDLER_%{%}%" (.tuple [n', cs', v₃])] ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (.catE
        (valsPat "val" "val*") (.listE [.caseE "BR" (.varE "l")]))
        (iterPat "instr" "instr*")) v₃ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (valsPat "val" "val*")
        (.listE [.caseE "BR" (.varE "l")])) w := by
    concl_inv he
  obtain ⟨n', cs', v₃, his, h₃, hw⟩ := hc
  obtain ⟨ws, fv, htv⟩ := quant_list hq (x := "val*") (t := .varT "val" []) (by simp)
  obtain ⟨rest, fi, -⟩ := quant_list hq (x := "instr*") (t := .varT "instr" []) (by simp)
  obtain ⟨l', fl, -⟩ := quant_of hq (x := "l") (t := labelidxT) (by simp)
  have ev : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (valsPat "val" "val*") (.list ws) :=
    evalExp_valsPat (by decide) fv
  have eb : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.listE [.caseE "BR" (.varE "l")])
      (.list [.case "BR" l']) := evalExp_list1 (evalExp_case (evalExp_var fl))
  have e₃ : v₃ = .list (ws ++ [.case "BR" l'] ++ rest) :=
    EvalExp.unique h₃ (evalExp_cat (evalExp_cat ev eb) (evalExp_iterPat (by decide) fi))
  have ew : w = .list (ws ++ [.case "BR" l']) := EvalExp.unique hw (evalExp_cat ev eb)
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single his
  obtain ⟨n, cs, body, rfl, -, -, hb⟩ := handlerD_of ha
  have hbody : adminsToVD body = ws ++ [.case "BR" l'] ++ rest := Value.list.inj (hb.symm.trans e₃)
  obtain ⟨vs, b, b₂, rfl, h₁, hbr, -⟩ := splitD_of B hbody htv
  obtain ⟨l, rfl, hbv⟩ := brD_of B hbr
  refine ⟨vals vs ++ [.plain (.br l)], ?_, .brHandler⟩
  rw [ew, adminsToVD_append, adminsToVD_vals, h₁, ← hbr]
  rfl

theorem bwdD_returnLabel (B : Builtins) : LeafD B P host 23 := by
  intro s f is w hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).returnLabel hf)
  have hc : ∃ n' l' v₃, adminsToVD is = [.case "LABEL_%{%}%" (.tuple [n', l', v₃])] ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (.catE
        (valsPat "val" "val*") (.listE [.caseE "RETURN" (.tupE [])]))
        (iterPat "instr" "instr*")) v₃ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (valsPat "val" "val*")
        (.listE [.caseE "RETURN" (.tupE [])])) w := by
    concl_inv he
  obtain ⟨n', l', v₃, his, h₃, hw⟩ := hc
  obtain ⟨ws, fv, htv⟩ := quant_list hq (x := "val*") (t := .varT "val" []) (by simp)
  obtain ⟨rest, fi, -⟩ := quant_list hq (x := "instr*") (t := .varT "instr" []) (by simp)
  have ev : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (valsPat "val" "val*") (.list ws) :=
    evalExp_valsPat (by decide) fv
  have eb : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.listE [.caseE "RETURN" (.tupE [])])
      (.list [caseNilV "RETURN"]) := evalExp_list1 evalExp_caseNil
  have e₃ : v₃ = .list (ws ++ [caseNilV "RETURN"] ++ rest) :=
    EvalExp.unique h₃ (evalExp_cat (evalExp_cat ev eb) (evalExp_iterPat (by decide) fi))
  have ew : w = .list (ws ++ [caseNilV "RETURN"]) := EvalExp.unique hw (evalExp_cat ev eb)
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single his
  obtain ⟨n, cont, body, rfl, -, -, hb⟩ := labelD_of ha
  have hbody : adminsToVD body = ws ++ [caseNilV "RETURN"] ++ rest :=
    Value.list.inj (hb.symm.trans e₃)
  obtain ⟨vs, b, b₂, rfl, h₁, hbr, -⟩ := splitD_of B hbody htv
  obtain rfl := retD_of B hbr
  refine ⟨vals vs ++ [.plain .return_], ?_, .returnLabel⟩
  rw [ew, adminsToVD_append, adminsToVD_vals, h₁]
  rfl

theorem bwdD_returnHandler (B : Builtins) : LeafD B P host 24 := by
  intro s f is w hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).returnHandler hf)
  have hc : ∃ n' cs' v₃, adminsToVD is = [.case "HANDLER_%{%}%" (.tuple [n', cs', v₃])] ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (.catE
        (valsPat "val" "val*") (.listE [.caseE "RETURN" (.tupE [])]))
        (iterPat "instr" "instr*")) v₃ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (valsPat "val" "val*")
        (.listE [.caseE "RETURN" (.tupE [])])) w := by
    concl_inv he
  obtain ⟨n', cs', v₃, his, h₃, hw⟩ := hc
  obtain ⟨ws, fv, htv⟩ := quant_list hq (x := "val*") (t := .varT "val" []) (by simp)
  obtain ⟨rest, fi, -⟩ := quant_list hq (x := "instr*") (t := .varT "instr" []) (by simp)
  have ev : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (valsPat "val" "val*") (.list ws) :=
    evalExp_valsPat (by decide) fv
  have eb : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.listE [.caseE "RETURN" (.tupE [])])
      (.list [caseNilV "RETURN"]) := evalExp_list1 evalExp_caseNil
  have e₃ : v₃ = .list (ws ++ [caseNilV "RETURN"] ++ rest) :=
    EvalExp.unique h₃ (evalExp_cat (evalExp_cat ev eb) (evalExp_iterPat (by decide) fi))
  have ew : w = .list (ws ++ [caseNilV "RETURN"]) := EvalExp.unique hw (evalExp_cat ev eb)
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single his
  obtain ⟨n, cs, body, rfl, -, -, hb⟩ := handlerD_of ha
  have hbody : adminsToVD body = ws ++ [caseNilV "RETURN"] ++ rest :=
    Value.list.inj (hb.symm.trans e₃)
  obtain ⟨vs, b, b₂, rfl, h₁, hbr, -⟩ := splitD_of B hbody htv
  obtain rfl := retD_of B hbr
  refine ⟨vals vs ++ [.plain .return_], ?_, .returnHandler⟩
  rw [ew, adminsToVD_append, adminsToVD_vals, h₁]
  rfl

theorem bwdD_brLabelSucc (B : Builtins) : LeafD B P host 9 := by
  intro s f is w hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (simEnv_execRules B).brLabelSucc hf)
  have hc : ∃ n' l' v₃, adminsToVD is = [.case "LABEL_%{%}%" (.tuple [n', l', v₃])] ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (.catE
        (valsPat "val" "val*") (.listE [.caseE "BR" (.varE "l")]))
        (iterPat "instr" "instr*")) v₃ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (valsPat "val" "val*")
        (.listE [.caseE "BR" brSuccE])) w := by
    concl_inv he
  obtain ⟨n', l', v₃, his, h₃, hw⟩ := hc
  obtain ⟨ws, fv, htv⟩ := quant_list hq (x := "val*") (t := .varT "val" []) (by simp)
  obtain ⟨rest, fi, -⟩ := quant_list hq (x := "instr*") (t := .varT "instr" []) (by simp)
  obtain ⟨lv, fl, -⟩ := quant_of hq (x := "l") (t := labelidxT) (by simp)
  have ev : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (valsPat "val" "val*") (.list ws) :=
    evalExp_valsPat (by decide) fv
  have eb : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.listE [.caseE "BR" (.varE "l")])
      (.list [.case "BR" lv]) := evalExp_list1 (evalExp_case (evalExp_var fl))
  have e₃ : v₃ = .list (ws ++ [.case "BR" lv] ++ rest) :=
    EvalExp.unique h₃ (evalExp_cat (evalExp_cat ev eb) (evalExp_iterPat (by decide) fi))
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single his
  obtain ⟨n, cont, body, rfl, -, -, hb⟩ := labelD_of ha
  have hbody : adminsToVD body = ws ++ [.case "BR" lv] ++ rest := Value.list.inj (hb.symm.trans e₃)
  obtain ⟨vs, b, b₂, rfl, h₁, hbr, -⟩ := splitD_of B hbody htv
  obtain ⟨lab, rfl, hbv⟩ := brD_of B hbr
  have hlv : lv = pctV lab.toNat := (Value.case.inj hbv).2.symm
  have fl' : (VarEnv.empty.bindVals σ).findVal? "l" = some (pctV lab.toNat) := hlv ▸ fl
  have hpos : 0 < lab.toNat := immGt_of_eval fl' (ifPrem (hp _ (by simp)))
  have ew : w = .list (ws ++ [.case "BR" (pctV (lab.toNat - 1))]) :=
    EvalExp.unique hw (evalExp_cat ev (evalExp_list1 (evalExp_case (evalExp_brSuccIdx hpos fl'))))
  refine ⟨vals vs ++ [.plain (.br (labelPred lab))], ?_, .brLabelSucc hpos⟩
  rw [ew, adminsToVD_append, adminsToVD_vals, h₁]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round9.RMPure
