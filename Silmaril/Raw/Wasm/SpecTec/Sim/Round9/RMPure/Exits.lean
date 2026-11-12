module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMPure.Decode

/-!
# Round 9, rm: the exit and trap rules of `Step_pure` backward at `adminsToVD` (unrefined)

Round 6's leaves (`Sim.bwd_trapLabel`, … `Bwd.bwd_frameVals`, `Exn.bwd_pure_handlerVals`,
`Sim.bwd_trapInstrs`), re-run at `adminsToVD`: the code may hold memory SIMD instructions in the
parts the rule carries or discards. No typing hypothesis is used.

Rules: 7 (`label-vals`), 21 (`frame-vals`), 25 (`handler-vals`), 26 (`trap-instrs`),
27 (`trap-label`), 28 (`trap-handler`), 29 (`trap-frame`).
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
open Round7.MemSimd (adminsToVD adminToVD instrsToVD adminsToVD_eq_single)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}


/-- **The backward obligation of a `Step_pure` rule at `adminsToVD`.** -/
def LeafD (B : Builtins) (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (i : Nat) : Prop :=
  ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Fires (simEnv B) "Step_pure" i (.tuple [.list (adminsToVD is), w]) →
    ∃ is', w = .list (adminsToVD is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩

/-- `TRAP` at `adminToVD`. -/
theorem trapD_of (B : Builtins) {a : Admin} (h : adminToVD a = caseNilV "TRAP") : a = .trap :=
  (Typing.ctrlDecode_simEnv B).trap a (toV_of_atomD (op := "TRAP") h rfl)

theorem bwdD_trapLabel (B : Builtins) : LeafD B P host 27 := by
  intro s f is w hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).trapLabel hf)
  have hc : ∃ n' l', adminsToVD is =
      [.case "LABEL_%{%}%" (.tuple [n', l', .list [caseNilV "TRAP"]])] ∧
        w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨n', l', his, rfl⟩ := hc
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single his
  obtain ⟨n, cont, body, rfl, -, -, hb⟩ := labelD_of ha
  obtain ⟨b, rfl, hb'⟩ := adminsToVD_eq_single (Value.list.inj hb).symm
  obtain rfl := trapD_of B hb'
  exact ⟨[.trap], rfl, .trapLabel⟩

theorem bwdD_trapHandler (B : Builtins) : LeafD B P host 28 := by
  intro s f is w hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).trapHandler hf)
  have hc : ∃ n' l', adminsToVD is =
      [.case "HANDLER_%{%}%" (.tuple [n', l', .list [caseNilV "TRAP"]])] ∧
        w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨n', l', his, rfl⟩ := hc
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single his
  obtain ⟨n, cs, body, rfl, -, -, hb⟩ := handlerD_of ha
  obtain ⟨b, rfl, hb'⟩ := adminsToVD_eq_single (Value.list.inj hb).symm
  obtain rfl := trapD_of B hb'
  exact ⟨[.trap], rfl, .trapHandler⟩

theorem bwdD_trapFrame (B : Builtins) : LeafD B P host 29 := by
  intro s f is w hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).trapFrame hf)
  have hc : ∃ n' f', adminsToVD is =
      [.case "FRAME_%{%}%" (.tuple [n', f', .list [caseNilV "TRAP"]])] ∧
        w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨n', f', his, rfl⟩ := hc
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single his
  obtain ⟨n, fi, body, rfl, -, -, hb⟩ := frameD_of ha
  obtain ⟨b, rfl, hb'⟩ := adminsToVD_eq_single (Value.list.inj hb).symm
  obtain rfl := trapD_of B hb'
  exact ⟨[.trap], rfl, .trapFrame⟩

theorem bwdD_labelVals (B : Builtins) : LeafD B P host 7 := by
  intro s f is w hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).labelVals hf)
  have hc : ∃ n' l' v₃, adminsToVD is = [.case "LABEL_%{%}%" (.tuple [n', l', v₃])] ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (valsPat "val" "val*") v₃ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (valsPat "val" "val*") w := by
    concl_inv he
  obtain ⟨n', l', v₃, his, h₃, hw⟩ := hc
  obtain ⟨v₀, hv₀, ht₀⟩ := quant_of hq (x := "val*") (t := valsT) (by simp)
  obtain ⟨ws, rfl⟩ := hasTyp_list_isList ht₀
  have e₀ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (valsPat "val" "val*") (.list ws) :=
    evalExp_valsPat (by decide) hv₀
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single his
  obtain ⟨n, cont, body, rfl, -, -, hb⟩ := labelD_of ha
  have hbody : adminsToVD body = ws := Value.list.inj (hb.symm.trans (EvalExp.unique h₃ e₀))
  obtain ⟨vs, rfl, -, -⟩ := valsD_of hbody ht₀
  exact ⟨vals vs, by rw [EvalExp.unique hw e₀, hbody], .labelVals⟩

theorem bwdD_handlerVals (B : Builtins) : LeafD B P host 25 := by
  intro s f is w hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).handlerVals hf)
  have hc : ∃ n' l' v₃, adminsToVD is = [.case "HANDLER_%{%}%" (.tuple [n', l', v₃])] ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (valsPat "val" "val*") v₃ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (valsPat "val" "val*") w := by
    concl_inv he
  obtain ⟨n', l', v₃, his, h₃, hw⟩ := hc
  obtain ⟨v₀, hv₀, ht₀⟩ := quant_of hq (x := "val*") (t := valsT) (by simp)
  obtain ⟨ws, rfl⟩ := hasTyp_list_isList ht₀
  have e₀ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (valsPat "val" "val*") (.list ws) :=
    evalExp_valsPat (by decide) hv₀
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single his
  obtain ⟨n, cs, body, rfl, -, -, hb⟩ := handlerD_of ha
  have hbody : adminsToVD body = ws := Value.list.inj (hb.symm.trans (EvalExp.unique h₃ e₀))
  obtain ⟨vs, rfl, -, -⟩ := valsD_of hbody ht₀
  exact ⟨vals vs, by rw [EvalExp.unique hw e₀, hbody], .handlerVals⟩

theorem bwdD_frameVals (B : Builtins) : LeafD B P host 21 := by
  intro s f is w hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).frameVals hf)
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  obtain ⟨ws, fv, fn, hw⟩ := Exn.evalExp_valsNPat_inv (by decide) hr
  obtain ⟨fr, ffr, -⟩ := quant_of (x := "f") (t := frameT) hq (.tail _ (.head _))
  obtain ⟨ws', fv', htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.head _)))
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hvn : EvalExp (simEnv B) _ (valsNPat "val" "val*" "n") (.list ws) :=
    evalExp_valsNPat (by decide) fn fv
  have hc : Value.list (adminsToVD is) =
      .list [.case "FRAME_%{%}%" (.tuple [.num (.natN ws.length), fr, .list ws])] :=
    EvalExp.unique hl (evalExp_list1 (evalExp_case
      (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr) hvn)))
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single (Value.list.inj hc)
  obtain ⟨k, fi, body, rfl, hk, -, hb⟩ := frameD_of ha
  have hbody : adminsToVD body = ws := (Value.list.inj hb).symm
  obtain ⟨vs, rfl, -, hlen⟩ := valsD_of hbody (ew ▸ htv)
  have hk' : vs.length = k := by rw [← hlen]; exact Bwd.natN_inj hk
  have hw' : w = .list (adminsToVD (vals vs)) := by rw [hw, hbody]
  exact ⟨vals vs, hw', .frameVals hk'⟩

theorem bwdD_trapInstrs (B : Builtins) : LeafD B P host 26 := by
  intro s f is w hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (simEnv_execRules B).trapInstrs hf)
  have hc : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE
      (valsPat "val" "val*") (.catE (.listE [.caseE "TRAP" (.tupE [])])
        (iterPat "instr" "instr*"))) (.list (adminsToVD is)) ∧
      w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨hlhs, rfl⟩ := hc
  obtain ⟨ws, fv, htv⟩ := quant_list hq (x := "val*") (t := .varT "val" []) (by simp)
  obtain ⟨rest, fi, -⟩ := quant_list hq (x := "instr*") (t := .varT "instr" []) (by simp)
  have e₀ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE
      (valsPat "val" "val*") (.catE (.listE [.caseE "TRAP" (.tupE [])])
        (iterPat "instr" "instr*"))) (.list (ws ++ ([caseNilV "TRAP"] ++ rest))) :=
    evalExp_cat (evalExp_valsPat (by decide) fv)
      (evalExp_cat (evalExp_list1 evalExp_caseNil) (evalExp_iterPat (by decide) fi))
  have his : adminsToVD is = ws ++ [caseNilV "TRAP"] ++ rest := by
    simpa using Value.list.inj (EvalExp.unique hlhs e₀)
  have hne : ws ≠ [] ∨ rest ≠ [] :=
    or_of_eval fv fi (ifPrem (hp _ (by simp [iterPat])))
  obtain ⟨b₁, b, b₂, rfl, h₁, hb, h₂⟩ := adminsToVD_eq_split his
  obtain ⟨vs, rfl, -, -⟩ := valsD_of h₁ htv
  obtain rfl := trapD_of B hb
  have hne' : vs ≠ [] ∨ b₂ ≠ [] := by
    rcases hne with h | h
    · exact .inl fun hv => h (by rw [← h₁, hv]; rfl)
    · exact .inr fun hv => h (by rw [← h₂, hv]; rfl)
  exact ⟨[.trap], rfl, .trapInstrs hne'⟩

end Silmaril.Wasm.SpecTec.Sim.Round9.RMPure
