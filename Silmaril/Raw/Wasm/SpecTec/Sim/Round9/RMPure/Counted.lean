module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMPure.Branch

/-!
# Round 9, rm: `br-label-zero` and `return-frame` at `adminsToVD` (unrefined)

Round 6's `Bwd.bwd_brLabelZero` (rule 8) and `Bwd.bwd_returnFrame` (rule 22), re-run at
`adminsToVD`. Both read a body `val'* val^n x instr*`, with `n` bound to the label's or frame's
arity.
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
open Round7.MemSimd (adminsToVD adminToVD instrsToVD adminsToVD_eq_single adminsToVD_append
  adminsToVD_vals adminsToVD_expression)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- A body `val'* val* x instr*` at `adminsToVD`, decoded, with the length of `val*`. -/
theorem split2D_of (B : Builtins) {σ : List (IL.Id × Value)} {body : List Admin}
    {ws₁ ws rest : List Value} {x : Value} (h : adminsToVD body = ws₁ ++ ws ++ [x] ++ rest)
    (ht₁ : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) valsT (.list ws₁))
    (ht : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) valsT (.list ws)) :
    ∃ vs' vs b rest', body = vals vs' ++ vals vs ++ [b] ++ rest' ∧ adminsToV (vals vs) = ws ∧
      ws.length = vs.length ∧ adminToVD b = x ∧ adminsToVD rest' = rest := by
  obtain ⟨l₁₂, b, l₃, rfl, h₁₂, hb, hl₃⟩ := adminsToVD_eq_split h
  obtain ⟨l₁, l₂, l₀, e, h₁, h₂, h₀⟩ := Round7.MemSimd.adminsToVD_split3 (C := [])
    (by rw [h₁₂, List.append_nil])
  have hl₀ : l₀ = [] := by
    rw [Round7.MemSimd.adminsToVD_eq_map] at h₀; exact List.map_eq_nil_iff.1 h₀
  subst hl₀
  rw [List.append_nil] at e
  subst e
  obtain ⟨vs', rfl, -, -⟩ := valsD_of h₁ ht₁
  obtain ⟨vs, rfl, hv, hlen⟩ := valsD_of h₂ ht
  exact ⟨vs', vs, b, l₃, rfl, hv, hlen, hb, hl₃⟩

theorem bwdD_returnFrame (B : Builtins) : LeafD B P host 22 := by
  intro s f is w hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).returnFrame hf)
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  obtain ⟨ws, fv, fn, hw⟩ := Exn.evalExp_valsNPat_inv (by decide) hr
  obtain ⟨fr, ffr, -⟩ := quant_of (x := "f") (t := frameT) hq (.tail _ (.head _))
  obtain ⟨ws₁, fv₁, htv₁⟩ := quant_list (x := "val'*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.head _)))
  have ev₁ : EvalExp (simEnv B) _ (valsPat "val'" "val'*") (.list ws₁) :=
    evalExp_valsPat (by decide) fv₁
  obtain ⟨ws', fv', htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨rest, fr', -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hbody : EvalExp (simEnv B) _ (.catE (.catE (.catE (valsPat "val'" "val'*")
      (valsNPat "val" "val*" "n")) (.listE [.caseE "RETURN" (.tupE [])])) (iterPat "instr" "instr*"))
      (.list (ws₁ ++ ws ++ [caseNilV "RETURN"] ++ rest)) :=
    evalExp_cat (evalExp_cat (evalExp_cat ev₁ (evalExp_valsNPat (by decide) fn fv))
      (evalExp_list1 evalExp_caseNil)) (evalExp_iterPat (by decide) fr')
  have hc : Value.list (adminsToVD is) = .list [.case "FRAME_%{%}%"
      (.tuple [.num (.natN ws.length), fr, .list (ws₁ ++ ws ++ [caseNilV "RETURN"] ++ rest)])] :=
    EvalExp.unique hl (evalExp_list1 (evalExp_case
      (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr) hbody)))
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single (Value.list.inj hc)
  obtain ⟨k, fi, body, rfl, hk, -, hb⟩ := frameD_of ha
  obtain ⟨vs', vs, b, l₃, rfl, h₂, hlen, hbr, -⟩ :=
    split2D_of B (Value.list.inj hb.symm) htv₁ (ew ▸ htv)
  have hret : b = .plain .return_ := retD_of B hbr
  have hk' : vs.length = k := by rw [← hlen]; exact Bwd.natN_inj hk
  have hw' : w = .list (adminsToVD (vals vs)) := by rw [hw, adminsToVD_vals, h₂]
  exact ⟨vals vs, hw', hret ▸ .returnFrame hk'⟩

theorem bwdD_brLabelZero (B : Builtins) : LeafD B P host 8 := by
  intro s f is w hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (simEnv_execRules B).brLabelZero hf)
  obtain ⟨cont, fc, -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq (.tail _ (.head _))
  have ec : EvalExp (simEnv B) _ (iterPat "instr'" "instr'*") (.list cont) :=
    evalExp_iterPat (by decide) fc
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  obtain ⟨ws, fv, fn, hw⟩ := Bwd.valsN_cat hr ec
  obtain ⟨ws₁, fv₁, htv₁⟩ := quant_list (x := "val'*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.head _)))
  have ev₁ : EvalExp (simEnv B) _ (valsPat "val'" "val'*") (.list ws₁) :=
    evalExp_valsPat (by decide) fv₁
  obtain ⟨ws', fv', htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨lv, fl, -⟩ := quant_of (x := "l") (t := labelidxT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨rest, fr, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hbody : EvalExp (simEnv B) _ (.catE (.catE (.catE (valsPat "val'" "val'*")
      (valsNPat "val" "val*" "n")) (.listE [.caseE "BR" (.varE "l")])) (iterPat "instr" "instr*"))
      (.list (ws₁ ++ ws ++ [.case "BR" lv] ++ rest)) :=
    evalExp_cat (evalExp_cat (evalExp_cat ev₁ (evalExp_valsNPat (by decide) fn fv))
      (evalExp_list1 (evalExp_case (evalExp_var fl)))) (evalExp_iterPat (by decide) fr)
  have hc : Value.list (adminsToVD is) = .list [.case "LABEL_%{%}%"
      (.tuple [.num (.natN ws.length), .list cont, .list (ws₁ ++ ws ++ [.case "BR" lv] ++ rest)])] :=
    EvalExp.unique hl (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec hbody)))
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single (Value.list.inj hc)
  obtain ⟨k, cont₀, body, rfl, hk, hcont, hb⟩ := labelD_of ha
  obtain ⟨vs', vs, b, l₃, rfl, h₂, hlen, hbr, -⟩ :=
    split2D_of B (Value.list.inj hb.symm) htv₁ (ew ▸ htv)
  obtain ⟨l, rfl, hbv⟩ := brD_of B hbr
  have hlv : lv = pctV l.toNat := (Value.case.inj hbv).2.symm
  have hl0 : l.toNat = 0 := immEq_of_eval (hlv ▸ fl) (ifPrem (hp _ (.head _)))
  have hk' : vs.length = k := by rw [← hlen]; exact Bwd.natN_inj hk
  have hw' : w = .list (adminsToVD (vals vs ++ expression cont₀)) := by
    rw [hw, adminsToVD_append, adminsToVD_vals, h₂, adminsToVD_expression, Value.list.inj hcont]
  exact ⟨vals vs ++ expression cont₀, hw', .brLabelZero hl0 hk'⟩

end Silmaril.Wasm.SpecTec.Sim.Round9.RMPure
