module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.Otherwise

/-!
# Family C: backward lemmas (SpecTec → Core) for the structural `Step_pure` rules

Each `bwd_*` is the `Backward.pure i` field at one index `i`, at `env := simEnv B`, under the
decoders `CtrlDecode`: whatever rule `i` derives from the image of a configuration's code is the
image of a Core successor. The proofs read the rule's conclusion backwards
(`evalExp_*_iff`), decode the left-hand side into Core code, and rebuild the right-hand side as
the image of Core's result; premises are read back into Core's side conditions.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV evalExp_imm_iff)

/-! ## Reading a firing rule -/

/-- A firing rule is the rule its provenance names. -/
theorem fires_body {env : Env} {x : IL.Id} {i : Nat} {v : Value} {r₀ : Rule}
    (h₀ : HasRuleAt env x "%~>%" i r₀) (hf : Fires env x i v) :
    RuleBody env (DDerives env (otherwise env)) (otherwise env x [] i v) [] [] "%~>%" r₀ v := by
  obtain ⟨t, rules, r, hrel, hr, hb⟩ := hf
  have e : r = r₀ := Option.some.inj (hr.symm.trans (ruleAt_get h₀ hrel))
  exact e ▸ hb

/-- `x!%.0 =/= 0` read back. -/
theorem immNe_of_eval {env : Env} {ρ : VarEnv} {x : IL.Id} {k : Nat}
    (hx : ρ.findVal? x = some (pctV k))
    (h : EvalExp env ρ (.cmpE .neOp .boolT (.projE (.uncaseE (.varE x) "%") 0) (.numE (.natN 0)))
      (.bool true)) : k ≠ 0 := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have e₁ : v₁ = .num (.natN k) := EvalExp.unique h₁ ((evalExp_imm_iff hx).2 ⟨[], rfl⟩)
  have e₂ : v₂ = .num (.natN 0) := evalExp_numE_iff.1 h₂
  subst e₁ e₂
  intro hk
  subst hk
  simp [cmpValues] at hc

/-- `x!%.0 = 0` read back. -/
theorem immEq_of_eval {env : Env} {ρ : VarEnv} {x : IL.Id} {k : Nat}
    (hx : ρ.findVal? x = some (pctV k))
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.projE (.uncaseE (.varE x) "%") 0) (.numE (.natN 0)))
      (.bool true)) : k = 0 := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have e₁ : v₁ = .num (.natN k) := EvalExp.unique h₁ ((evalExp_imm_iff hx).2 ⟨[], rfl⟩)
  have e₂ : v₂ = .num (.natN 0) := evalExp_numE_iff.1 h₂
  subst e₁ e₂
  simpa [cmpValues] using hc

/-- The single `if` premise of a rule body. -/
theorem ifPrem {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {e : Exp}
    (h : PremW env D els ρ (.ifPr e)) : EvalExp env ρ e (.bool true) := by
  cases h with
  | ifPr h => exact h

/-- Unfold a rule body with its scope. -/
theorem ruleBody_scope {env : Env} {D : Interp} {els : Prop} {op : MixopS} {nm : IL.Id}
    {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem} {w : Value}
    (h : RuleBody env D els [] [] op (.ruleD nm qs op' e prems) w) :
    ∃ σ, QuantsOk env (VarEnv.empty.bindVals σ) qs ∧ EvalExp env (VarEnv.empty.bindVals σ) e w ∧
      ∀ pr ∈ prems, PremW env D els (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := h
  have e₀ : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  subst e₀
  exact ⟨σ, hq, he, hp⟩

/-- A value of a `*` type is a list. -/
theorem hasTyp_list_isList {env : Env} {ρ : VarEnv} {t : Typ} {v : Value}
    (h : HasTyp env ρ (.iterT t .list) v) : ∃ l, v = .list l := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [hasTyp] at hn
  | succ n => cases v <;> simp_all [hasTyp, Value.asList?]

/-- A quantified variable of the scope, with its type. -/
theorem quant_of {env : Env} {ρ : VarEnv} {qs : List Param} {x : IL.Id} {t : Typ}
    (hq : QuantsOk env ρ qs) (hm : Param.expP x t ∈ qs) :
    ∃ v, ρ.findVal? x = some v ∧ HasTyp env ρ t v :=
  hq x t hm

/-- A quantified `*` variable is bound to a list of its type. -/
theorem quant_list {env : Env} {ρ : VarEnv} {qs : List Param} {x : IL.Id} {t : Typ}
    (hq : QuantsOk env ρ qs) (hm : Param.expP x (.iterT t .list) ∈ qs) :
    ∃ l, ρ.findVal? x = some (.list l) ∧ HasTyp env ρ (.iterT t .list) (.list l) := by
  obtain ⟨v, hv, ht⟩ := hq x _ hm
  obtain ⟨l, rfl⟩ := hasTyp_list_isList ht
  exact ⟨l, hv, ht⟩

/-- Every rule scope binds term variables only. -/
theorem valsOnly_bindVals (σ : List (IL.Id × Value)) : ValsOnly (VarEnv.empty.bindVals σ) :=
  ⟨rfl, rfl, rfl⟩

/-- Invert a conclusion by evaluation, to a stated shape. -/
macro "concl_inv " h:ident : tactic => `(tactic| (
  simp [evalExp_tupE_iff, Equiv.Validation.evalExps_cons_iff,
    Equiv.Validation.evalExps_nil_iff, evalExp_listE_iff, evalExp_caseE_iff, evalExp_varE_iff,
    evalExp_subE_iff, evalExp_optE_some_iff, caseNilV] at $h:ident ⊢
  aesop))

section Bwd

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H}
variable (B : Builtins) (D : CtrlDecode (simEnv B))

/-- The image of a one-instruction sequence. -/
theorem adminsToV_eq_single {is : List Admin} {v : Value} (h : adminsToV is = [v]) :
    ∃ a, is = [a] ∧ adminToV a = v := by
  match is, h with
  | [a], h => exact ⟨a, rfl, (List.cons.inj h).1⟩
  | [], h => simp [adminsToV] at h
  | _ :: _ :: _, h => simp [adminsToV] at h

/-- The image of a two-instruction sequence. -/
theorem adminsToV_eq_pair {is : List Admin} {v₁ v₂ : Value} (h : adminsToV is = [v₁, v₂]) :
    ∃ a₁ a₂, is = [a₁, a₂] ∧ adminToV a₁ = v₁ ∧ adminToV a₂ = v₂ := by
  match is, h with
  | [a₁, a₂], h => exact ⟨a₁, a₂, rfl, (List.cons.inj h).1, (List.cons.inj (List.cons.inj h).2).1⟩
  | [], h => simp [adminsToV] at h
  | [_], h => simp [adminsToV] at h
  | _ :: _ :: _ :: _, h => simp [adminsToV] at h


include D in
/-- `Backward.pure 27` (`trap-label`). -/
theorem bwd_trapLabel : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 27 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).trapLabel hf)
  have hc : ∃ n' l', adminsToV is =
      [.case "LABEL_%{%}%" (.tuple [n', l', .list [caseNilV "TRAP"]])] ∧ w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨n', l', his, rfl⟩ := hc
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single his
  obtain ⟨n, cont, body, rfl⟩ := D.label a _ ha
  have hbody : adminsToV body = [caseNilV "TRAP"] := by
    simp only [adminToV_label, Value.case.injEq, Value.tuple.injEq, List.cons.injEq] at ha
    exact Value.list.inj ha.2.2.2.1
  obtain ⟨b, rfl, hb⟩ := adminsToV_eq_single hbody
  obtain rfl := D.trap b hb
  exact ⟨[.trap], rfl, .trapLabel⟩

include D in
/-- `Backward.pure 28` (`trap-handler`). -/
theorem bwd_trapHandler : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 28 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).trapHandler hf)
  have hc : ∃ n' l', adminsToV is =
      [.case "HANDLER_%{%}%" (.tuple [n', l', .list [caseNilV "TRAP"]])] ∧
        w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨n', l', his, rfl⟩ := hc
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single his
  obtain ⟨n, cs, body, rfl⟩ := D.handler a _ ha
  have hbody : adminsToV body = [caseNilV "TRAP"] := by
    simp only [adminToV_handler, Value.case.injEq, Value.tuple.injEq, List.cons.injEq] at ha
    exact Value.list.inj ha.2.2.2.1
  obtain ⟨b, rfl, hb⟩ := adminsToV_eq_single hbody
  obtain rfl := D.trap b hb
  exact ⟨[.trap], rfl, .trapHandler⟩

include D in
/-- `Backward.pure 29` (`trap-frame`). -/
theorem bwd_trapFrame : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 29 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).trapFrame hf)
  have hc : ∃ n' f', adminsToV is =
      [.case "FRAME_%{%}%" (.tuple [n', f', .list [caseNilV "TRAP"]])] ∧
        w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨n', f', his, rfl⟩ := hc
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single his
  obtain ⟨n, fi, body, rfl⟩ := D.frame a _ ha
  have hbody : adminsToV body = [caseNilV "TRAP"] := by
    simp only [adminToV_frame, Value.case.injEq, Value.tuple.injEq, List.cons.injEq] at ha
    exact Value.list.inj ha.2.2.2.1
  obtain ⟨b, rfl, hb⟩ := adminsToV_eq_single hbody
  obtain rfl := D.trap b hb
  exact ⟨[.trap], rfl, .trapFrame⟩

include D in
/-- `Backward.pure 7` (`label-vals`): the declarative reading types `val*`, so the body is a value
sequence (the evaluator reading fires on any body, `Equiv.Execution.ruleFires_labelVals_nonvalue`). -/
theorem bwd_labelVals : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 7 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).labelVals hf)
  have hc : ∃ n' l' v₃, adminsToV is = [.case "LABEL_%{%}%" (.tuple [n', l', v₃])] ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
        (Equiv.Execution.valsPat "val" "val*") v₃ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (Equiv.Execution.valsPat "val" "val*") w := by
    concl_inv he
  obtain ⟨n', l', v₃, his, h₃, hw⟩ := hc
  obtain ⟨v₀, hv₀, ht₀⟩ := quant_of hq (x := "val*") (t := valsT) (by simp)
  obtain ⟨ws, rfl⟩ := hasTyp_list_isList ht₀
  have e₀ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (Equiv.Execution.valsPat "val" "val*")
      (.list ws) := Equiv.Execution.evalExp_valsPat (by decide) hv₀
  have e₃ : v₃ = .list ws := EvalExp.unique h₃ e₀
  have ew : w = .list ws := EvalExp.unique hw e₀
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single his
  obtain ⟨n, cont, body, rfl⟩ := D.label a _ ha
  have hbody : adminsToV body = ws := by
    simp only [adminToV_label, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, e₃] at ha
    exact Value.list.inj ha.2.2.2.1
  obtain ⟨vs, rfl⟩ := D.vals _ body (valsOnly_bindVals σ) (hbody ▸ ht₀)
  exact ⟨vals vs, by rw [ew, hbody], .labelVals⟩

/-- Split the image of a code sequence around one instruction. -/
theorem adminsToV_eq_split {l : List Admin} {A C : List Value} {x : Value}
    (h : adminsToV l = A ++ [x] ++ C) :
    ∃ l₁ a l₂, l = l₁ ++ [a] ++ l₂ ∧ adminsToV l₁ = A ∧ adminToV a = x ∧ adminsToV l₂ = C := by
  rw [adminsToV_eq_map, List.append_assoc, List.map_eq_append_iff] at h
  obtain ⟨l₁, r, rfl, h₁, hr⟩ := h
  rw [List.map_eq_append_iff] at hr
  obtain ⟨m, l₂, rfl, hm, h₂⟩ := hr
  obtain ⟨a, rfl, ha⟩ : ∃ a, m = [a] ∧ adminToV a = x := by
    match m, hm with
    | [a], hm => exact ⟨a, rfl, (List.cons.inj hm).1⟩
  exact ⟨l₁, a, l₂, by simp, by rw [adminsToV_eq_map, h₁], ha, by rw [adminsToV_eq_map, h₂]⟩

/-- The immediate of a decoded `CONST I32 c`. -/
theorem constI32_imm {c : BitVec 32} {c' : Value}
    (h : adminToV (constI32 c) = .case "CONST" (.tuple [caseNilV "I32", c'])) :
    c' = pctV c.toNat := by
  rw [adminToV_constI32] at h
  simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at h
  exact h.symm

/-- `c.toNat ≠ 0` gives `c ≠ 0`. -/
theorem ne_zero_of_toNat {c : BitVec 32} (h : c.toNat ≠ 0) : c ≠ 0 :=
  fun h' => h (by simp [h'])

/-- `c.toNat = 0` gives `c = 0`. -/
theorem eq_zero_of_toNat {c : BitVec 32} (h : c.toNat = 0) : c = 0 :=
  BitVec.eq_of_toNat_eq (by simpa using h)

include D in
/-- `Backward.pure 5` (`if-true`). -/
theorem bwd_ifTrue : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 5 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, -, he, hp⟩ := ruleBody_scope (fires_body (simEnv_execRules B).ifTrue hf)
  have hc : ∃ c' bt' v₁ v₂ v₁', adminsToV is = [.case "CONST" (.tuple [caseNilV "I32", c']),
      .case "IF%%ELSE%" (.tuple [bt', v₁, v₂])] ∧ w = .list [.case "BLOCK" (.tuple [bt', v₁'])] ∧
      (VarEnv.empty.bindVals σ).findVal? "c" = some c' ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (Equiv.Execution.iterPat "instr_1" "instr_1*") v₁ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (Equiv.Execution.iterPat "instr_1" "instr_1*") v₁' := by
    concl_inv he
  obtain ⟨c', bt', v₁, v₂, v₁', his, rfl, hcv, e₁, e₁'⟩ := hc
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair his
  obtain ⟨c, rfl⟩ := D.constI32 a₁ c' h₁
  obtain ⟨bt, b₁, b₂, rfl⟩ := D.ifElse a₂ _ h₂
  have hc' : c' = pctV c.toNat := constI32_imm h₁
  have hv : v₁' = v₁ := EvalExp.unique e₁' e₁
  have hcomp : bt' = Encode.toValue bt ∧ v₁ = .list (instrsToV b₁) := by
    have h₂' : Value.case "IF%%ELSE%" (.tuple [Encode.toValue bt, .list (instrsToV b₁),
        .list (instrsToV b₂)]) = .case "IF%%ELSE%" (.tuple [bt', v₁, v₂]) := h₂
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at h₂'
    exact ⟨h₂'.1.symm, h₂'.2.1.symm⟩
  have hne : c.toNat ≠ 0 := immNe_of_eval (hc' ▸ hcv) (ifPrem (hp _ (by simp)))
  refine ⟨[.plain (.block bt b₁)], ?_, .ifTrue (ne_zero_of_toNat hne)⟩
  rw [hv, hcomp.1, hcomp.2]
  rfl

include D in
/-- `Backward.pure 6` (`if-false`). -/
theorem bwd_ifFalse : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 6 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, -, he, hp⟩ := ruleBody_scope (fires_body (simEnv_execRules B).ifFalse hf)
  have hc : ∃ c' bt' v₁ v₂ v₂', adminsToV is = [.case "CONST" (.tuple [caseNilV "I32", c']),
      .case "IF%%ELSE%" (.tuple [bt', v₁, v₂])] ∧ w = .list [.case "BLOCK" (.tuple [bt', v₂'])] ∧
      (VarEnv.empty.bindVals σ).findVal? "c" = some c' ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (Equiv.Execution.iterPat "instr_2" "instr_2*") v₂ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (Equiv.Execution.iterPat "instr_2" "instr_2*") v₂' := by
    concl_inv he
  obtain ⟨c', bt', v₁, v₂, v₂', his, rfl, hcv, e₂, e₂'⟩ := hc
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair his
  obtain ⟨c, rfl⟩ := D.constI32 a₁ c' h₁
  obtain ⟨bt, b₁, b₂, rfl⟩ := D.ifElse a₂ _ h₂
  have hc' : c' = pctV c.toNat := constI32_imm h₁
  have hv : v₂' = v₂ := EvalExp.unique e₂' e₂
  have hcomp : bt' = Encode.toValue bt ∧ v₂ = .list (instrsToV b₂) := by
    have h₂' : Value.case "IF%%ELSE%" (.tuple [Encode.toValue bt, .list (instrsToV b₁),
        .list (instrsToV b₂)]) = .case "IF%%ELSE%" (.tuple [bt', v₁, v₂]) := h₂
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at h₂'
    exact ⟨h₂'.1.symm, h₂'.2.2.1.symm⟩
  have h0 : c.toNat = 0 := immEq_of_eval (hc' ▸ hcv) (ifPrem (hp _ (by simp)))
  obtain rfl := eq_zero_of_toNat h0
  refine ⟨[.plain (.block bt b₂)], ?_, .ifFalse⟩
  rw [hv, hcomp.1, hcomp.2]
  rfl

include D in
/-- `Backward.pure 11` (`br_if-true`). -/
theorem bwd_brIfTrue : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 11 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, -, he, hp⟩ := ruleBody_scope (fires_body (simEnv_execRules B).brIfTrue hf)
  have hc : ∃ c' l', adminsToV is = [.case "CONST" (.tuple [caseNilV "I32", c']),
      .case "BR_IF" l'] ∧ w = .list [.case "BR" l'] ∧
      (VarEnv.empty.bindVals σ).findVal? "c" = some c' := by
    concl_inv he
  obtain ⟨c', l', his, rfl, hcv⟩ := hc
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair his
  obtain ⟨c, rfl⟩ := D.constI32 a₁ c' h₁
  obtain ⟨l, rfl⟩ := D.brIf a₂ _ h₂
  have hc' : c' = pctV c.toNat := constI32_imm h₁
  have hl : l' = Encode.toValue l := (Value.case.inj h₂).2.symm
  have hne : c.toNat ≠ 0 := immNe_of_eval (hc' ▸ hcv) (ifPrem (hp _ (by simp)))
  refine ⟨[.plain (.br l)], ?_, .brIfTrue (ne_zero_of_toNat hne)⟩
  rw [hl]
  rfl

include D in
/-- `Backward.pure 12` (`br_if-false`). -/
theorem bwd_brIfFalse : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 12 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, -, he, hp⟩ := ruleBody_scope (fires_body (simEnv_execRules B).brIfFalse hf)
  have hc : ∃ c' l', adminsToV is = [.case "CONST" (.tuple [caseNilV "I32", c']),
      .case "BR_IF" l'] ∧ w = .list [] ∧
      (VarEnv.empty.bindVals σ).findVal? "c" = some c' := by
    concl_inv he
  obtain ⟨c', l', his, rfl, hcv⟩ := hc
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair his
  obtain ⟨c, rfl⟩ := D.constI32 a₁ c' h₁
  obtain ⟨l, rfl⟩ := D.brIf a₂ _ h₂
  have hc' : c' = pctV c.toNat := constI32_imm h₁
  have h0 : c.toNat = 0 := immEq_of_eval (hc' ▸ hcv) (ifPrem (hp _ (by simp)))
  obtain rfl := eq_zero_of_toNat h0
  exact ⟨[], rfl, .brIfFalse⟩

include D in
/-- `Backward.pure 19` (`call_indirect`). -/
theorem bwd_callIndirect : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 19 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (simEnv_refRules B).callIndirect hf)
  have hc : ∃ x' yy, adminsToV is = [.case "CALL_INDIRECT" (.tuple [x', yy])] ∧
      w = .list [.case "TABLE.GET" x',
        .case "REF.CAST" (.case "REF" (.tuple [.opt (some (caseNilV "NULL")), yy])),
        .case "CALL_REF" yy] := by
    concl_inv he
  obtain ⟨x', yy, his, rfl⟩ := hc
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single his
  obtain ⟨t, y, rfl⟩ := D.callIndirect a _ ha
  have hcomp : x' = Encode.toValue t ∧ yy = .case "_IDX" (Encode.toValue y) := by
    have ha' : Value.case "CALL_INDIRECT" (.tuple [Encode.toValue t,
        .case "_IDX" (Encode.toValue y)]) = .case "CALL_INDIRECT" (.tuple [x', yy]) := ha
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at ha'
    exact ⟨ha'.1.symm, ha'.2.symm⟩
  refine ⟨[.plain (.tableGet t), .plain (.refCast ⟨true, .typeIdx y⟩), .plain (.callRef y)], ?_,
    .callIndirect⟩
  rw [hcomp.1, hcomp.2]
  rfl

include D in
/-- `Backward.pure 20` (`return_call_indirect`). -/
theorem bwd_returnCallIndirect : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 20 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (simEnv_refRules B).returnCallIndirect hf)
  have hc : ∃ x' yy, adminsToV is = [.case "RETURN_CALL_INDIRECT" (.tuple [x', yy])] ∧
      w = .list [.case "TABLE.GET" x',
        .case "REF.CAST" (.case "REF" (.tuple [.opt (some (caseNilV "NULL")), yy])),
        .case "RETURN_CALL_REF" yy] := by
    concl_inv he
  obtain ⟨x', yy, his, rfl⟩ := hc
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single his
  obtain ⟨t, y, rfl⟩ := D.returnCallIndirect a _ ha
  have hcomp : x' = Encode.toValue t ∧ yy = .case "_IDX" (Encode.toValue y) := by
    have ha' : Value.case "RETURN_CALL_INDIRECT" (.tuple [Encode.toValue t,
        .case "_IDX" (Encode.toValue y)]) = .case "RETURN_CALL_INDIRECT" (.tuple [x', yy]) := ha
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at ha'
    exact ⟨ha'.1.symm, ha'.2.symm⟩
  refine ⟨[.plain (.tableGet t), .plain (.refCast ⟨true, .typeIdx y⟩),
    .plain (.returnCallRef y)], ?_, .returnCallIndirect⟩
  rw [hcomp.1, hcomp.2]
  rfl

include D in
/-- `Backward.pure 10` (`br-handler`). -/
theorem bwd_brHandler : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 10 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).brHandler hf)
  have hc : ∃ n' cs' v₃, adminsToV is = [.case "HANDLER_%{%}%" (.tuple [n', cs', v₃])] ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (.catE
        (Equiv.Execution.valsPat "val" "val*") (.listE [.caseE "BR" (.varE "l")]))
        (Equiv.Execution.iterPat "instr" "instr*")) v₃ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (Equiv.Execution.valsPat "val" "val*")
        (.listE [.caseE "BR" (.varE "l")])) w := by
    concl_inv he
  obtain ⟨n', cs', v₃, his, h₃, hw⟩ := hc
  obtain ⟨ws, fv, htv⟩ := quant_list hq (x := "val*") (t := .varT "val" []) (by simp)
  obtain ⟨rest, fi, -⟩ := quant_list hq (x := "instr*") (t := .varT "instr" []) (by simp)
  obtain ⟨l', fl, -⟩ := quant_of hq (x := "l") (t := labelidxT) (by simp)
  have ev : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (Equiv.Execution.valsPat "val" "val*")
      (.list ws) := Equiv.Execution.evalExp_valsPat (by decide) fv
  have eb : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.listE [.caseE "BR" (.varE "l")])
      (.list [.case "BR" l']) := evalExp_list1 (evalExp_case (evalExp_var fl))
  have e₃ : v₃ = .list (ws ++ [.case "BR" l'] ++ rest) :=
    EvalExp.unique h₃ (evalExp_cat (evalExp_cat ev eb) (Equiv.Execution.evalExp_iterPat (by decide) fi))
  have ew : w = .list (ws ++ [.case "BR" l']) := EvalExp.unique hw (evalExp_cat ev eb)
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single his
  obtain ⟨n, cs, body, rfl⟩ := D.handler a _ ha
  have hbody : adminsToV body = ws ++ [.case "BR" l'] ++ rest := by
    simp only [adminToV_handler, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, e₃] at ha
    exact Value.list.inj ha.2.2.2.1
  obtain ⟨b₁, b, b₂, rfl, h₁, hb, -⟩ := adminsToV_eq_split hbody
  obtain ⟨vs, rfl⟩ := D.vals _ b₁ (valsOnly_bindVals σ) (h₁ ▸ htv)
  obtain ⟨l, rfl⟩ := D.br b _ hb
  refine ⟨vals vs ++ [.plain (.br l)], ?_, .brHandler⟩
  rw [ew, adminsToV_append, h₁, ← hb]
  rfl

include D in
/-- `Backward.pure 23` (`return-label`). -/
theorem bwd_returnLabel : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 23 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).returnLabel hf)
  have hc : ∃ n' l' v₃, adminsToV is = [.case "LABEL_%{%}%" (.tuple [n', l', v₃])] ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (.catE
        (Equiv.Execution.valsPat "val" "val*") (.listE [.caseE "RETURN" (.tupE [])]))
        (Equiv.Execution.iterPat "instr" "instr*")) v₃ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (Equiv.Execution.valsPat "val" "val*")
        (.listE [.caseE "RETURN" (.tupE [])])) w := by
    concl_inv he
  obtain ⟨n', l', v₃, his, h₃, hw⟩ := hc
  obtain ⟨ws, fv, htv⟩ := quant_list hq (x := "val*") (t := .varT "val" []) (by simp)
  obtain ⟨rest, fi, -⟩ := quant_list hq (x := "instr*") (t := .varT "instr" []) (by simp)
  have ev : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (Equiv.Execution.valsPat "val" "val*")
      (.list ws) := Equiv.Execution.evalExp_valsPat (by decide) fv
  have eb : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.listE [.caseE "RETURN" (.tupE [])])
      (.list [caseNilV "RETURN"]) := evalExp_list1 evalExp_caseNil
  have e₃ : v₃ = .list (ws ++ [caseNilV "RETURN"] ++ rest) :=
    EvalExp.unique h₃ (evalExp_cat (evalExp_cat ev eb) (Equiv.Execution.evalExp_iterPat (by decide) fi))
  have ew : w = .list (ws ++ [caseNilV "RETURN"]) := EvalExp.unique hw (evalExp_cat ev eb)
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single his
  obtain ⟨n, cont, body, rfl⟩ := D.label a _ ha
  have hbody : adminsToV body = ws ++ [caseNilV "RETURN"] ++ rest := by
    simp only [adminToV_label, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, e₃] at ha
    exact Value.list.inj ha.2.2.2.1
  obtain ⟨b₁, b, b₂, rfl, h₁, hb, -⟩ := adminsToV_eq_split hbody
  obtain ⟨vs, rfl⟩ := D.vals _ b₁ (valsOnly_bindVals σ) (h₁ ▸ htv)
  obtain rfl := D.ret b hb
  refine ⟨vals vs ++ [.plain .return_], ?_, .returnLabel⟩
  rw [ew, adminsToV_append, h₁]
  rfl

include D in
/-- `Backward.pure 24` (`return-handler`). -/
theorem bwd_returnHandler : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 24 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).returnHandler hf)
  have hc : ∃ n' cs' v₃, adminsToV is = [.case "HANDLER_%{%}%" (.tuple [n', cs', v₃])] ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (.catE
        (Equiv.Execution.valsPat "val" "val*") (.listE [.caseE "RETURN" (.tupE [])]))
        (Equiv.Execution.iterPat "instr" "instr*")) v₃ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (Equiv.Execution.valsPat "val" "val*")
        (.listE [.caseE "RETURN" (.tupE [])])) w := by
    concl_inv he
  obtain ⟨n', cs', v₃, his, h₃, hw⟩ := hc
  obtain ⟨ws, fv, htv⟩ := quant_list hq (x := "val*") (t := .varT "val" []) (by simp)
  obtain ⟨rest, fi, -⟩ := quant_list hq (x := "instr*") (t := .varT "instr" []) (by simp)
  have ev : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (Equiv.Execution.valsPat "val" "val*")
      (.list ws) := Equiv.Execution.evalExp_valsPat (by decide) fv
  have eb : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.listE [.caseE "RETURN" (.tupE [])])
      (.list [caseNilV "RETURN"]) := evalExp_list1 evalExp_caseNil
  have e₃ : v₃ = .list (ws ++ [caseNilV "RETURN"] ++ rest) :=
    EvalExp.unique h₃ (evalExp_cat (evalExp_cat ev eb) (Equiv.Execution.evalExp_iterPat (by decide) fi))
  have ew : w = .list (ws ++ [caseNilV "RETURN"]) := EvalExp.unique hw (evalExp_cat ev eb)
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single his
  obtain ⟨n, cs, body, rfl⟩ := D.handler a _ ha
  have hbody : adminsToV body = ws ++ [caseNilV "RETURN"] ++ rest := by
    simp only [adminToV_handler, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, e₃] at ha
    exact Value.list.inj ha.2.2.2.1
  obtain ⟨b₁, b, b₂, rfl, h₁, hb, -⟩ := adminsToV_eq_split hbody
  obtain ⟨vs, rfl⟩ := D.vals _ b₁ (valsOnly_bindVals σ) (h₁ ▸ htv)
  obtain rfl := D.ret b hb
  refine ⟨vals vs ++ [.plain .return_], ?_, .returnHandler⟩
  rw [ew, adminsToV_append, h₁]
  rfl

include D in
/-- `Backward.pure 15` (`br_on_null-null`). -/
theorem bwd_brOnNullNull : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 15 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, -, he, hp⟩ := ruleBody_scope (fires_body (simEnv_refRules B).brOnNullNull hf)
  have hc : ∃ x l', adminsToV is = [x, .case "BR_ON_NULL" l'] ∧ w = .list [.case "BR" l'] ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
        (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) x := by
    concl_inv he
  obtain ⟨x, l', his, rfl, hx⟩ := hc
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair his
  have hnull : x = caseNilV "REF.NULL_ADDR" := nullPrem hx (hp _ (by simp))
  obtain rfl := D.refNull a₁ (h₁.trans hnull)
  obtain ⟨l, rfl⟩ := D.brOnNull a₂ _ h₂
  have hl : l' = Encode.toValue l := (Value.case.inj h₂).2.symm
  refine ⟨[.plain (.br l)], ?_, .brOnNullNull⟩
  rw [hl]
  rfl

include D in
/-- `Backward.pure 17` (`br_on_non_null-null`). -/
theorem bwd_brOnNonNullNull : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 17 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, -, he, hp⟩ := ruleBody_scope (fires_body (simEnv_refRules B).brOnNonNullNull hf)
  have hc : ∃ x l', adminsToV is = [x, .case "BR_ON_NON_NULL" l'] ∧ w = .list [] ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
        (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) x := by
    concl_inv he
  obtain ⟨x, l', his, rfl, hx⟩ := hc
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair his
  have hnull : x = caseNilV "REF.NULL_ADDR" := nullPrem hx (hp _ (by simp))
  obtain rfl := D.refNull a₁ (h₁.trans hnull)
  obtain ⟨l, rfl⟩ := D.brOnNonNull a₂ _ h₂
  exact ⟨[], rfl, .brOnNonNullNull⟩

/-- `p \/ q` on booleans, read back. -/
theorem or_of_eval {env : Env} {ρ : VarEnv} {ws is : List Value}
    (fv : ρ.findVal? "val*" = some (.list ws)) (fi : ρ.findVal? "instr*" = some (.list is))
    (h : EvalExp env ρ (.binE .orOp .boolT
      (.cmpE .neOp .boolT (Equiv.Execution.iterPat "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (Equiv.Execution.iterPat "instr" "instr*") (.listE []))) (.bool true)) :
    ws ≠ [] ∨ is ≠ [] := by
  have e : EvalExp env ρ (.binE .orOp .boolT
      (.cmpE .neOp .boolT (Equiv.Execution.iterPat "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (Equiv.Execution.iterPat "instr" "instr*") (.listE [])))
      (.bool (decide (ws ≠ [] ∨ is ≠ []))) :=
    evalExp_or (evalExp_ne_nil (Equiv.Execution.evalExp_iterPat (by decide) fv))
      (evalExp_ne_nil (Equiv.Execution.evalExp_iterPat (by decide) fi))
  have hb : decide (ws ≠ [] ∨ is ≠ []) = true := Value.bool.inj (EvalExp.unique e h)
  exact of_decide_eq_true hb

include D in
/-- `Backward.pure 26` (`trap-instrs`). -/
theorem bwd_trapInstrs : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 26 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (simEnv_execRules B).trapInstrs hf)
  have hc : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE
      (Equiv.Execution.valsPat "val" "val*") (.catE (.listE [.caseE "TRAP" (.tupE [])])
        (Equiv.Execution.iterPat "instr" "instr*"))) (.list (adminsToV is)) ∧
      w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨hlhs, rfl⟩ := hc
  obtain ⟨ws, fv, htv⟩ := quant_list hq (x := "val*") (t := .varT "val" []) (by simp)
  obtain ⟨rest, fi, -⟩ := quant_list hq (x := "instr*") (t := .varT "instr" []) (by simp)
  have e₀ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE
      (Equiv.Execution.valsPat "val" "val*") (.catE (.listE [.caseE "TRAP" (.tupE [])])
        (Equiv.Execution.iterPat "instr" "instr*"))) (.list (ws ++ ([caseNilV "TRAP"] ++ rest))) :=
    evalExp_cat (Equiv.Execution.evalExp_valsPat (by decide) fv)
      (evalExp_cat (evalExp_list1 evalExp_caseNil) (Equiv.Execution.evalExp_iterPat (by decide) fi))
  have his : adminsToV is = ws ++ [caseNilV "TRAP"] ++ rest := by
    simpa using Value.list.inj (EvalExp.unique hlhs e₀)
  have hne : ws ≠ [] ∨ rest ≠ [] :=
    or_of_eval fv fi (ifPrem (hp _ (by simp [Equiv.Execution.iterPat])))
  obtain ⟨b₁, b, b₂, rfl, h₁, hb, h₂⟩ := adminsToV_eq_split his
  obtain ⟨vs, rfl⟩ := D.vals _ b₁ (valsOnly_bindVals σ) (h₁ ▸ htv)
  obtain rfl := D.trap b hb
  have hne' : vs ≠ [] ∨ b₂ ≠ [] := by
    rcases hne with h | h
    · exact .inl fun hv => h (by rw [← h₁, hv]; rfl)
    · exact .inr fun hv => h (by rw [← h₂, hv]; rfl)
  exact ⟨[.trap], rfl, .trapInstrs hne'⟩

include D in
/-- `Backward.step 6` (`call_ref-null`). -/
theorem bwd_callRefNull : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step" 6 (.tuple [configV hn c, w]) → BwdP hn P host c w := by
  intro c w _ hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (hasStepRules_simEnv B).callRefNull hf)
  have hc : ∃ z yy, configV hn c = .case "%;%" (.tuple [z, .list [caseNilV "REF.NULL_ADDR",
      .case "CALL_REF" yy]]) ∧ w = .case "%;%" (.tuple [z, .list [caseNilV "TRAP"]]) := by
    concl_inv he
  obtain ⟨z, yy, hcfg, rfl⟩ := hc
  obtain ⟨s, f, is⟩ := c
  have hz : stateV hn s f = z ∧ adminsToV is = [caseNilV "REF.NULL_ADDR", .case "CALL_REF" yy] := by
    simpa [configV] using hcfg
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair hz.2
  obtain rfl := D.refNull a₁ h₁
  refine ⟨⟨s, f, [.trap]⟩, ?_, .callRefNull (D.callRef a₂ _ h₂)⟩
  rw [← hz.1]
  rfl

/-- `x!%.0 > 0` read back. -/
theorem immGt_of_eval {env : Env} {ρ : VarEnv} {x : IL.Id} {k : Nat}
    (hx : ρ.findVal? x = some (pctV k))
    (h : EvalExp env ρ (.cmpE .gtOp (.numT .natT) (.projE (.uncaseE (.varE x) "%") 0)
      (.numE (.natN 0))) (.bool true)) : 0 < k := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have e₁ : v₁ = .num (.natN k) := EvalExp.unique h₁ ((evalExp_imm_iff hx).2 ⟨[], rfl⟩)
  have e₂ : v₂ = .num (.natN 0) := evalExp_numE_iff.1 h₂
  subst e₁ e₂
  simpa [cmpValues, Num.cmp, Res.ofOption] using hc

/-- The successor branch's index expression. -/
abbrev brSuccE : Exp := .caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT)
  (.cvtE (.projE (.uncaseE (.varE "l") "%") 0) .natT .intT)
  (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT])

include D in
/-- `Backward.pure 9` (`br-label-succ`). -/
theorem bwd_brLabelSucc : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 9 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (simEnv_execRules B).brLabelSucc hf)
  have hc : ∃ n' l' v₃, adminsToV is = [.case "LABEL_%{%}%" (.tuple [n', l', v₃])] ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (.catE
        (Equiv.Execution.valsPat "val" "val*") (.listE [.caseE "BR" (.varE "l")]))
        (Equiv.Execution.iterPat "instr" "instr*")) v₃ ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.catE (Equiv.Execution.valsPat "val" "val*")
        (.listE [.caseE "BR" brSuccE])) w := by
    concl_inv he
  obtain ⟨n', l', v₃, his, h₃, hw⟩ := hc
  obtain ⟨ws, fv, htv⟩ := quant_list hq (x := "val*") (t := .varT "val" []) (by simp)
  obtain ⟨rest, fi, -⟩ := quant_list hq (x := "instr*") (t := .varT "instr" []) (by simp)
  obtain ⟨lv, fl, -⟩ := quant_of hq (x := "l") (t := labelidxT) (by simp)
  have ev : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (Equiv.Execution.valsPat "val" "val*")
      (.list ws) := Equiv.Execution.evalExp_valsPat (by decide) fv
  have eb : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.listE [.caseE "BR" (.varE "l")])
      (.list [.case "BR" lv]) := evalExp_list1 (evalExp_case (evalExp_var fl))
  have e₃ : v₃ = .list (ws ++ [.case "BR" lv] ++ rest) :=
    EvalExp.unique h₃ (evalExp_cat (evalExp_cat ev eb) (Equiv.Execution.evalExp_iterPat (by decide) fi))
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single his
  obtain ⟨n, cont, body, rfl⟩ := D.label a _ ha
  have hbody : adminsToV body = ws ++ [.case "BR" lv] ++ rest := by
    simp only [adminToV_label, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, e₃] at ha
    exact Value.list.inj ha.2.2.2.1
  obtain ⟨b₁, b, b₂, rfl, h₁, hb, -⟩ := adminsToV_eq_split hbody
  obtain ⟨vs, rfl⟩ := D.vals _ b₁ (valsOnly_bindVals σ) (h₁ ▸ htv)
  obtain ⟨lab, rfl⟩ := D.br b _ hb
  have hlv : lv = pctV lab.toNat := (Value.case.inj hb).2.symm
  have fl' : (VarEnv.empty.bindVals σ).findVal? "l" = some (pctV lab.toNat) := hlv ▸ fl
  have hpos : 0 < lab.toNat := immGt_of_eval fl' (ifPrem (hp _ (by simp)))
  have ew : w = .list (ws ++ [.case "BR" (pctV (lab.toNat - 1))]) :=
    EvalExp.unique hw (evalExp_cat ev (evalExp_list1 (evalExp_case (evalExp_brSuccIdx hpos fl'))))
  refine ⟨vals vs ++ [.plain (.br (labelPred lab))], ?_, .brLabelSucc hpos⟩
  rw [ew, adminsToV_append, h₁]
  rfl

/-- `i!%.0 op |l*|` read back. -/
theorem immLen_of_eval {env : Env} {ρ : VarEnv} {k : Nat} {L : List Value} {op : CmpOp}
    (hx : ρ.findVal? "i" = some (pctV k)) (hl : ρ.findVal? "l*" = some (.list L))
    (h : EvalExp env ρ (.cmpE op (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
      (.lenE (Equiv.Execution.iterPat "l" "l*"))) (.bool true)) :
    cmpValues op (.num (.natN k)) (.num (.natN L.length)) = .ok (.bool true) := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have e₁ : v₁ = .num (.natN k) := EvalExp.unique h₁ ((evalExp_imm_iff hx).2 ⟨[], rfl⟩)
  have e₂ : v₂ = .num (.natN L.length) := EvalExp.unique h₂
    (evalExp_lenE_iff.2 ⟨L, Equiv.Execution.evalExp_iterPat (by decide) hl, rfl⟩)
  rw [e₁, e₂] at hc
  exact hc

/-- The `br_table` left-hand side, read back. -/
theorem brTable_lhs (D : CtrlDecode (simEnv B)) {is : List Admin} {i' L l'' : Value}
    (his : adminsToV is = [.case "CONST" (.tuple [caseNilV "I32", i']),
      .case "BR_TABLE" (.tuple [L, l''])]) :
    ∃ (c : BitVec 32) (ls : List LabelIdx) (l' : LabelIdx),
      is = [constI32 c, .plain (.brTable ls l')] ∧ i' = pctV c.toNat ∧
        L = .list (ls.map Encode.toValue) ∧ l'' = Encode.toValue l' := by
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair his
  obtain ⟨c, rfl⟩ := D.constI32 a₁ _ h₁
  obtain ⟨ls, l', rfl⟩ := D.brTable a₂ _ h₂
  have h₂' : Value.case "BR_TABLE" (.tuple [.list (ls.map Encode.toValue), Encode.toValue l']) =
      .case "BR_TABLE" (.tuple [L, l'']) := h₂
  simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at h₂'
  exact ⟨c, ls, l', rfl, constI32_imm h₁, h₂'.1.symm, h₂'.2.symm⟩

include D in
/-- `Backward.pure 13` (`br_table-lt`). -/
theorem bwd_brTableLt : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 13 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (simEnv_brTableRules B).brTableLt hf)
  have hc : ∃ i' L l'' v, adminsToV is = [.case "CONST" (.tuple [caseNilV "I32", i']),
      .case "BR_TABLE" (.tuple [L, l''])] ∧ w = .list [.case "BR" v] ∧
      (VarEnv.empty.bindVals σ).findVal? "i" = some i' ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (Equiv.Execution.iterPat "l" "l*") L ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.idxE (Equiv.Execution.iterPat "l" "l*")
        (.projE (.uncaseE (.varE "i") "%") 0)) v := by
    concl_inv he
  obtain ⟨i', L, l'', v, his, rfl, fi, hL, hv⟩ := hc
  obtain ⟨c, ls, l', rfl, rfl, rfl, rfl⟩ := brTable_lhs B D his
  obtain ⟨L₀, fL, -⟩ := quant_list hq (x := "l*") (t := labelidxT) (by simp)
  have eL : Value.list (ls.map Encode.toValue) = .list L₀ :=
    EvalExp.unique hL (Equiv.Execution.evalExp_iterPat (by decide) fL)
  have fL' : (VarEnv.empty.bindVals σ).findVal? "l*" = some (.list (ls.map Encode.toValue)) :=
    eL ▸ fL
  have hlt : c.toNat < ls.length := by
    have hcmp := immLen_of_eval (op := .ltOp) fi fL'
      (ifPrem (hp _ (by simp [Equiv.Execution.iterPat])))
    simpa [cmpValues, Num.cmp, Res.ofOption] using hcmp
  obtain ⟨l, hl⟩ : ∃ l, ls[c.toNat]? = some l := ⟨ls[c.toNat], List.getElem?_eq_getElem hlt⟩
  have ev : v = Encode.toValue l := by
    obtain ⟨w', k, hw', hk, hidx⟩ := evalExp_idxE_iff.1 hv
    have ew : w' = .list (ls.map Encode.toValue) :=
      EvalExp.unique hw' (Equiv.Execution.evalExp_iterPat (by decide) fL')
    have ek : Value.num (.natN k) = .num (.natN c.toNat) :=
      EvalExp.unique hk ((evalExp_imm_iff fi).2 ⟨[], rfl⟩)
    subst ew
    cases ek
    simpa [Value.idx?, hl] using hidx.symm
  refine ⟨[.plain (.br l)], ?_, .brTableLt hl⟩
  rw [ev]
  rfl

include D in
/-- `Backward.pure 14` (`br_table-ge`). -/
theorem bwd_brTableGe : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 14 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (simEnv_brTableRules B).brTableGe hf)
  have hc : ∃ i' L l'', adminsToV is = [.case "CONST" (.tuple [caseNilV "I32", i']),
      .case "BR_TABLE" (.tuple [L, l''])] ∧ w = .list [.case "BR" l''] ∧
      (VarEnv.empty.bindVals σ).findVal? "i" = some i' ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (Equiv.Execution.iterPat "l" "l*") L := by
    concl_inv he
  obtain ⟨i', L, l'', his, rfl, fi, hL⟩ := hc
  obtain ⟨c, ls, l', rfl, rfl, rfl, rfl⟩ := brTable_lhs B D his
  obtain ⟨L₀, fL, -⟩ := quant_list hq (x := "l*") (t := labelidxT) (by simp)
  have eL : Value.list (ls.map Encode.toValue) = .list L₀ :=
    EvalExp.unique hL (Equiv.Execution.evalExp_iterPat (by decide) fL)
  have fL' : (VarEnv.empty.bindVals σ).findVal? "l*" = some (.list (ls.map Encode.toValue)) :=
    eL ▸ fL
  have hge : ls.length ≤ c.toNat := by
    have hcmp := immLen_of_eval (op := .geOp) fi fL'
      (ifPrem (hp _ (by simp [Equiv.Execution.iterPat])))
    simpa [cmpValues, Num.cmp, Res.ofOption] using hcmp
  exact ⟨[.plain (.br l')], rfl, .brTableGe hge⟩

end Bwd

end Silmaril.Wasm.SpecTec.Sim
