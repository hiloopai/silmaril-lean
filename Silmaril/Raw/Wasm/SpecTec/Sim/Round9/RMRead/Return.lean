module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMRead.Exits

/-!
# Round 9, rm: `return_call_ref` out of contexts and `throw_ref-instrs` at `configVD` (unrefined)

Round 6's `Bwd.bwd_returnCallRefLabel`, `bwd_returnCallRefHandler`, `bwd_returnCallRefFrameNull`
(rules 8, 9, 10) and `Exn.bwd_read_throwRefInstrs` (rule 13), re-run at `configVD`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMRead

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat valsPat valsNPat evalExp_iterPat
  evalExp_valsPat)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round7.MemSimd (configVD adminsToVD adminToVD instrsToVD adminsToVD_eq_single
  adminsToVD_eq_pair adminsToVD_append adminsToVD_vals configVD_cfgV)
open RMPure (toV_of_atomD labelD_of handlerD_of frameD_of valsD_of splitD_of adminsToVD_eq_split)

variable {H : Type} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H}

theorem bwdRD_returnCallRefLabel (B : Builtins) : LeafRD B hn P host 8 := by
  rintro ⟨s, f, code⟩ w hf
  obtain ⟨σ, hq, he, -⟩ :=
    ruleBody_scope (fires_body (simEnv_readRules B).returnCallRefLabel hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨kv, fk, -⟩ := quant_of (x := "k") (t := nT) hq (.tail _ (.head _))
  obtain ⟨cont, fc, -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.head _)))
  obtain ⟨ws, fv, htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  have ev : EvalExp (simEnv B) _ (valsPat "val" "val*") (.list ws) := evalExp_valsPat (by decide) fv
  obtain ⟨yy, fy, -⟩ := quant_of (x := "yy") (t := typeuseT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨rest, fr, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ey : EvalExp (simEnv B) _ (.listE [.caseE "RETURN_CALL_REF" (.varE "yy")])
      (.list [.case "RETURN_CALL_REF" yy]) := evalExp_list1 (evalExp_case (evalExp_var fy))
  have hc : Value.tuple [configVD hn ⟨s, f, code⟩, w] = .tuple [cfgV z [.case "LABEL_%{%}%"
      (.tuple [kv, .list cont, .list (ws ++ [.case "RETURN_CALL_REF" yy] ++ rest)])],
      .list (ws ++ [.case "RETURN_CALL_REF" yy])] :=
    EvalExp.unique he (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fk) (evalExp_iterPat (by decide) fc)
        (evalExp_cat (evalExp_cat ev ey) (evalExp_iterPat (by decide) fr)))))))
      (evalExp_cat ev ey))
  obtain ⟨a, hcode, ha⟩ := adminsToVD_eq_single (configVD_cfgV (Bwd.tuple2_inj hc).1).2.symm
  subst hcode
  obtain ⟨k, cont₀, body, rfl, -, -, hb⟩ := labelD_of ha
  obtain ⟨vs, b, b₂, rfl, h₁, hbr, -⟩ := splitD_of B (Value.list.inj hb).symm htv
  have hw : w = .list (adminsToVD (vals vs ++ [b])) := by
    rw [(Bwd.tuple2_inj hc).2, adminsToVD_append, adminsToVD_vals, h₁, ← hbr]
    rfl
  exact ⟨vals vs ++ [b], hw, .returnCallRefLabel (retCallRefD_of hbr).1⟩

theorem bwdRD_returnCallRefHandler (B : Builtins) : LeafRD B hn P host 9 := by
  rintro ⟨s, f, code⟩ w hf
  obtain ⟨σ, hq, he, -⟩ :=
    ruleBody_scope (fires_body (simEnv_readRules B).returnCallRefHandler hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨kv, fk, -⟩ := quant_of (x := "k") (t := nT) hq (.tail _ (.head _))
  obtain ⟨cs, fc, -⟩ := quant_list (x := "catch*") (t := .varT "catch" []) hq
    (.tail _ (.tail _ (.head _)))
  obtain ⟨ws, fv, htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  have ev : EvalExp (simEnv B) _ (valsPat "val" "val*") (.list ws) := evalExp_valsPat (by decide) fv
  obtain ⟨yy, fy, -⟩ := quant_of (x := "yy") (t := typeuseT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨rest, fr, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ey : EvalExp (simEnv B) _ (.listE [.caseE "RETURN_CALL_REF" (.varE "yy")])
      (.list [.case "RETURN_CALL_REF" yy]) := evalExp_list1 (evalExp_case (evalExp_var fy))
  have hc : Value.tuple [configVD hn ⟨s, f, code⟩, w] = .tuple [cfgV z [.case "HANDLER_%{%}%"
      (.tuple [kv, .list cs, .list (ws ++ [.case "RETURN_CALL_REF" yy] ++ rest)])],
      .list (ws ++ [.case "RETURN_CALL_REF" yy])] :=
    EvalExp.unique he (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fk) (evalExp_iterPat (by decide) fc)
        (evalExp_cat (evalExp_cat ev ey) (evalExp_iterPat (by decide) fr)))))))
      (evalExp_cat ev ey))
  obtain ⟨a, hcode, ha⟩ := adminsToVD_eq_single (configVD_cfgV (Bwd.tuple2_inj hc).1).2.symm
  subst hcode
  obtain ⟨k, cs₀, body, rfl, -, -, hb⟩ := handlerD_of ha
  obtain ⟨vs, b, b₂, rfl, h₁, hbr, -⟩ := splitD_of B (Value.list.inj hb).symm htv
  have hw : w = .list (adminsToVD (vals vs ++ [b])) := by
    rw [(Bwd.tuple2_inj hc).2, adminsToVD_append, adminsToVD_vals, h₁, ← hbr]
    rfl
  exact ⟨vals vs ++ [b], hw, .returnCallRefHandler (retCallRefD_of hbr).1⟩

/-- A body `val* REF.NULL_ADDR x instr*` at `adminsToVD`, decoded. -/
theorem splitNullD_of (B : Builtins) {σ : List (IL.Id × Value)} {body : List Admin}
    {ws rest : List Value} {x : Value}
    (h : adminsToVD body = ws ++ [caseNilV "REF.NULL_ADDR"] ++ [x] ++ rest)
    (ht : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) valsT (.list ws)) :
    ∃ vs b rest', body = vals vs ++ [.ref .null, b] ++ rest' ∧ adminToVD b = x := by
  obtain ⟨l₁, b, b₂, rfl, h₁, hb, -⟩ := adminsToVD_eq_split h
  obtain ⟨l₀, n, l₀', e, h₀, hn₀, h₀'⟩ := Round7.MemSimd.adminsToVD_split3 (C := [])
    (A := ws) (B := [caseNilV "REF.NULL_ADDR"]) (by rw [h₁, List.append_nil])
  have hl₀' : l₀' = [] := by
    rw [Round7.MemSimd.adminsToVD_eq_map] at h₀'; exact List.map_eq_nil_iff.1 h₀'
  subst hl₀'
  rw [List.append_nil] at e
  subst e
  obtain ⟨vs, rfl, -, -⟩ := valsD_of h₀ ht
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single hn₀
  obtain rfl := (Typing.ctrlDecode_simEnv B).refNull a (toV_of_atomD (op := "REF.NULL_ADDR") ha rfl)
  exact ⟨vs, b, b₂, by simp only [List.append_assoc, List.singleton_append], hb⟩

theorem bwdRD_returnCallRefFrameNull (B : Builtins) : LeafRD B hn P host 10 := by
  rintro ⟨s, f, code⟩ w hf
  obtain ⟨σ, hq, he, -⟩ :=
    ruleBody_scope (fires_body (simEnv_readRules B).returnCallRefFrameNull hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨kv, fk, -⟩ := quant_of (x := "k") (t := nT) hq (.tail _ (.head _))
  obtain ⟨fr, ffr, -⟩ := quant_of (x := "f") (t := frameT) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨ws, fv, htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  have ev : EvalExp (simEnv B) _ (valsPat "val" "val*") (.list ws) := evalExp_valsPat (by decide) fv
  obtain ⟨yy, fy, -⟩ := quant_of (x := "yy") (t := typeuseT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨rest, fr', -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have hbody : EvalExp (simEnv B) _ (.catE (.catE (.catE (valsPat "val" "val*")
      (.listE [.caseE "REF.NULL_ADDR" (.tupE [])]))
      (.listE [.caseE "RETURN_CALL_REF" (.varE "yy")])) (iterPat "instr" "instr*"))
      (.list (ws ++ [caseNilV "REF.NULL_ADDR"] ++ [.case "RETURN_CALL_REF" yy] ++ rest)) :=
    evalExp_cat (evalExp_cat (evalExp_cat ev (evalExp_list1 evalExp_caseNil))
      (evalExp_list1 (evalExp_case (evalExp_var fy)))) (evalExp_iterPat (by decide) fr')
  have hc : Value.tuple [configVD hn ⟨s, f, code⟩, w] = .tuple [cfgV z [.case "FRAME_%{%}%"
      (.tuple [kv, fr, .list (ws ++ [caseNilV "REF.NULL_ADDR"] ++
        [.case "RETURN_CALL_REF" yy] ++ rest)])], .list [caseNilV "TRAP"]] :=
    EvalExp.unique he (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fk) (evalExp_var ffr) hbody)))))
      (evalExp_list1 evalExp_caseNil))
  obtain ⟨a, hcode, ha⟩ := adminsToVD_eq_single (configVD_cfgV (Bwd.tuple2_inj hc).1).2.symm
  subst hcode
  obtain ⟨k, fi, body, rfl, -, -, hb⟩ := frameD_of ha
  obtain ⟨vs, b, b₂, rfl, hbr⟩ := splitNullD_of B (Value.list.inj hb).symm htv
  have hst : Step P host ⟨s, f, [.frame k fi (vals vs ++ [.ref .null, b] ++ b₂)]⟩
      ⟨s, f, [.trap]⟩ := .returnCallRefFrameNull (retCallRefD_of hbr).1
  exact ⟨[.trap], (Bwd.tuple2_inj hc).2, hst⟩

theorem bwdRD_throwRefInstrs (B : Builtins) : LeafRD B hn P host 13 := by
  rintro ⟨s, f, code⟩ w hf
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ :=
    Exn.fires_body (Exn.hasReadRules_simEnv B).throwRefInstrs hf
  obtain rfl : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨-, hce, hre⟩ := Exn.evalExp_concl_inv (Round7.MemSimd.configVD_eq hn _ ▸ he)
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁⟩ := Exn.evalExp_cat_inv hce
  obtain ⟨c₁, d₁, hc₁, hd₁, hcd₁⟩ := Exn.evalExp_cat_inv hb₁
  obtain ⟨g₁, r₁, hg₁, hr₁, hgr₁⟩ := Exn.evalExp_cat_inv hd₁
  obtain ⟨x, rfl, hx⟩ := Exn.evalExp_list1_inv' hc₁
  obtain ⟨y, rfl, hy⟩ := Exn.evalExp_list1_inv' hg₁
  obtain ⟨av, hav, rfl⟩ := evalExp_caseE_iff.1 hx
  obtain rfl := Exn.evalExp_caseNil_inv hy
  have hsplit : adminsToVD code = a₁ ++ [.case "REF.EXN_ADDR" av, caseNilV "THROW_REF"] ++ r₁ := by
    rw [hab₁, hcd₁, hgr₁]; simp
  obtain ⟨l₁, m, l₃, rfl, h₁, hm, h₃⟩ := Round7.MemSimd.adminsToVD_split3 hsplit
  obtain ⟨k, rfl, rfl⟩ := throwingD_of hm
  obtain ⟨vs, hvs, hvs', ht⟩ := Exn.vals_quant hq (by simp)
  have e₁ : adminsToVD l₁ = vs := h₁.trans (Value.list.inj (EvalExp.unique ha₁ hvs))
  obtain ⟨vs', rfl, e₁', -⟩ := valsD_of e₁ ht
  have hne : vs ≠ [] ∨ r₁ ≠ [] := by
    cases hp _ (List.mem_singleton_self _) with
    | ifPr h =>
        have hor := evalExp_or (t := .boolT) (evalExp_ne_nil (t := .boolT) hvs')
          (evalExp_ne_nil (t := .boolT) hr₁)
        exact of_decide_eq_true (Value.bool.inj (EvalExp.unique hor h))
  have hne' : vs' ≠ [] ∨ l₃ ≠ [] := by
    rcases hne with h | h
    · exact .inl fun h' => h (by rw [← e₁']; simp [h', vals])
    · exact .inr fun h' => h (by rw [← h₃, h']; rfl)
  refine ⟨throwing k, EvalExp.unique hre (Exn.evalExp_throwExn (evalExp_varE_iff.1 hav)), ?_⟩
  simpa only [List.append_assoc] using
    (Step.throwRefInstrs (P := P) (host := host) (s := s) (f := f) (a := k) hne')

end Silmaril.Wasm.SpecTec.Sim.Round9.RMRead
