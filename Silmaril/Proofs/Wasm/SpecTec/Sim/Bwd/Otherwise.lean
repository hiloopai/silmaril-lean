module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Block

/-!
# The two `otherwise` rules (`Step_pure` 16, 18)

`br_on_null-addr` (16) and `br_on_non_null-addr` (18) fire only when no earlier rule fires on the
same left-hand side. Backwards, the value must therefore be non-null: were it `REF.NULL_ADDR`,
rule 15 (`br_on_null-null`), resp. 17 (`br_on_non_null-null`), would fire on the same left-hand
side, at the *same* assignment (the rules share their quantifiers and left-hand side), against
the `otherwise` premise (`not_otherwise_null`, `not_otherwise_nonNull`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-- The quantifiers of rules 15–18 of `Step_pure`. -/
abbrev nullQuants : List Param := [.expP "val" (.varT "val" []), .expP "l" (.varT "labelidx" [])]

/-- `val = REF.NULL_ADDR`, at a null value. -/
theorem nullPrem_true {env : Env} {ρ : VarEnv} {D : Interp} {els : Prop}
    (fx : ρ.findVal? "val" = some (caseNilV "REF.NULL_ADDR")) :
    ∀ pr ∈ [Prem.ifPr (.cmpE .eqOp .boolT (.varE "val") (.caseE "REF.NULL_ADDR" (.tupE [])))],
      PremW env D els ρ pr := by
  intro pr hpr
  rw [List.mem_singleton.1 hpr]
  exact .ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_var fx, evalExp_caseNil, by simp [cmpValues]⟩)

/-- Unfold `otherwise`. -/
theorem otherwise_elim {env : Env} {x : IL.Id} {i : Nat} {v : Value}
    (h : otherwise env x [] i v) :
    ∀ j, j < i → ∀ ps op t rules r, env.findRel? x = some (ps, op, t, rules) →
      rules[j]? = some r → ∀ w, SameLhs v w →
        ¬ RuleBody env (DDerives env noElse) (otherwiseAt env x [] j w) ps [] op r w := by
  unfold otherwise at h
  rw [otherwiseAt] at h
  exact h

/-- `br_on_null-addr`'s `otherwise` excludes a null value. -/
theorem not_otherwise_null {env : Env} (RR : Equiv.ExecRef.HasRefRules env) {σ : List (IL.Id × Value)}
    {lv c : Value} (hq : QuantsOk env (VarEnv.empty.bindVals σ) nullQuants)
    (fx : (VarEnv.empty.bindVals σ).findVal? "val" = some (caseNilV "REF.NULL_ADDR"))
    (fl : (VarEnv.empty.bindVals σ).findVal? "l" = some lv)
    (ho : otherwise env "Step_pure" [] 16
      (.tuple [.list [caseNilV "REF.NULL_ADDR", .case "BR_ON_NULL" lv], c])) : False := by
  obtain ⟨t, rules, hrel⟩ := findRel_of_ruleAt RR.brOnNullNull
  have hr : rules[15]? = some Equiv.ExecRef.brOnNullNullRule := ruleAt_get RR.brOnNullNull hrel
  have ex : EvalExp env _ (.subE (.varE "val") (.varT "val" []) (.varT "instr" []))
      (caseNilV "REF.NULL_ADDR") := evalExp_subE_iff.2 (evalExp_var fx)
  refine otherwise_elim ho 15 (by decide) [] "%~>%" t rules _ hrel hr
    (.tuple [.list [caseNilV "REF.NULL_ADDR", .case "BR_ON_NULL" lv], .list [.case "BR" lv]])
    ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl, hq, ?_, nullPrem_true fx⟩
  exact evalExp_tup2 (evalExp_list2 ex (evalExp_case (evalExp_var fl)))
    (evalExp_list1 (evalExp_case (evalExp_var fl)))

/-- `br_on_non_null-addr`'s `otherwise` excludes a null value. -/
theorem not_otherwise_nonNull {env : Env} (RR : Equiv.ExecRef.HasRefRules env)
    {σ : List (IL.Id × Value)} {lv c : Value}
    (hq : QuantsOk env (VarEnv.empty.bindVals σ) nullQuants)
    (fx : (VarEnv.empty.bindVals σ).findVal? "val" = some (caseNilV "REF.NULL_ADDR"))
    (fl : (VarEnv.empty.bindVals σ).findVal? "l" = some lv)
    (ho : otherwise env "Step_pure" [] 18
      (.tuple [.list [caseNilV "REF.NULL_ADDR", .case "BR_ON_NON_NULL" lv], c])) : False := by
  obtain ⟨t, rules, hrel⟩ := findRel_of_ruleAt RR.brOnNonNullNull
  have hr : rules[17]? = some Equiv.ExecRef.brOnNonNullNullRule :=
    ruleAt_get RR.brOnNonNullNull hrel
  have ex : EvalExp env _ (.subE (.varE "val") (.varT "val" []) (.varT "instr" []))
      (caseNilV "REF.NULL_ADDR") := evalExp_subE_iff.2 (evalExp_var fx)
  refine otherwise_elim ho 17 (by decide) [] "%~>%" t rules _ hrel hr
    (.tuple [.list [caseNilV "REF.NULL_ADDR", .case "BR_ON_NON_NULL" lv], .list []])
    ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl, hq, ?_, nullPrem_true fx⟩
  exact evalExp_tup2 (evalExp_list2 ex (evalExp_case (evalExp_var fl))) evalExp_listNil

/-- A one-value code sequence, decoded. -/
theorem decode_val1 {env : Env} (D : CtrlDecode env) {σ : List (IL.Id × Value)} {a : Admin}
    {x : Value} (ha : adminToV a = x) (ht : HasTyp env (VarEnv.empty.bindVals σ) (.varT "val" []) x) :
    ∃ v : Val, a = v.toAdmin := by
  have hl : adminsToV [a] = [x] := by rw [← ha]; rfl
  obtain ⟨vs, hvs⟩ := D.vals _ [a] (valsOnly_bindVals σ)
    (hl ▸ hasTyp_list_cons_iff.2 ⟨ht, hasTyp_list_nil⟩)
  match vs, hvs with
  | [v], h => exact ⟨v, (List.cons.inj h).1⟩

section Bwd

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
variable (B : Builtins) (D : CtrlDecode (simEnv B))

include D in
/-- `Backward.pure 16` (`br_on_null-addr`). -/
theorem bwd_brOnNullAddr : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 16 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  have RR := simEnv_refRules B
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := fires_body RR.brOnNullAddr hf
  have e₀ : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  obtain ⟨xv, fx, tx⟩ := quant_of (x := "val") (t := .varT "val" []) (e₀ ▸ hq) (.head _)
  obtain ⟨lv, fl, -⟩ := quant_of (x := "l") (t := labelidxT) (e₀ ▸ hq) (.tail _ (.head _))
  have ex : EvalExp (simEnv B) _ (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) xv :=
    evalExp_subE_iff.2 (evalExp_var fx)
  have hc : Value.tuple [.list (adminsToV is), w] =
      .tuple [.list [xv, .case "BR_ON_NULL" lv], .list [xv]] :=
    EvalExp.unique (e₀ ▸ he) (evalExp_tup2 (evalExp_list2 ex (evalExp_case (evalExp_var fl)))
      (evalExp_list1 ex))
  have ho : otherwise (simEnv B) "Step_pure" [] 16
      (.tuple [.list [xv, .case "BR_ON_NULL" lv], .list [xv]]) := by
    have h₀ := hp _ (.head _)
    cases h₀ with
    | elsePr h => exact hc ▸ h
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair (Value.list.inj (tuple2_inj hc).1)
  obtain ⟨v, rfl⟩ := decode_val1 D h₁ tx
  obtain ⟨l, rfl⟩ := D.brOnNull a₂ _ h₂
  have hv : v ≠ .ref .null := fun hnull => by
    have hx : xv = caseNilV "REF.NULL_ADDR" := by rw [← h₁, hnull]; rfl
    exact not_otherwise_null RR (e₀ ▸ hq) (hx ▸ fx) fl (hx ▸ ho)
  have hw : w = .list (adminsToV [v.toAdmin]) := by rw [(tuple2_inj hc).2, ← h₁]; rfl
  exact ⟨_, hw, .brOnNullAddr hv⟩

include D in
/-- `Backward.pure 18` (`br_on_non_null-addr`). -/
theorem bwd_brOnNonNullAddr : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 18 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  have RR := simEnv_refRules B
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := fires_body RR.brOnNonNullAddr hf
  have e₀ : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  obtain ⟨xv, fx, tx⟩ := quant_of (x := "val") (t := .varT "val" []) (e₀ ▸ hq) (.head _)
  obtain ⟨lv, fl, -⟩ := quant_of (x := "l") (t := labelidxT) (e₀ ▸ hq) (.tail _ (.head _))
  have ex : EvalExp (simEnv B) _ (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) xv :=
    evalExp_subE_iff.2 (evalExp_var fx)
  have hc : Value.tuple [.list (adminsToV is), w] =
      .tuple [.list [xv, .case "BR_ON_NON_NULL" lv], .list [xv, .case "BR" lv]] :=
    EvalExp.unique (e₀ ▸ he) (evalExp_tup2 (evalExp_list2 ex (evalExp_case (evalExp_var fl)))
      (evalExp_list2 ex (evalExp_case (evalExp_var fl))))
  have ho : otherwise (simEnv B) "Step_pure" [] 18
      (.tuple [.list [xv, .case "BR_ON_NON_NULL" lv], .list [xv, .case "BR" lv]]) := by
    have h₀ := hp _ (.head _)
    cases h₀ with
    | elsePr h => exact hc ▸ h
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair (Value.list.inj (tuple2_inj hc).1)
  obtain ⟨v, rfl⟩ := decode_val1 D h₁ tx
  obtain ⟨l, rfl⟩ := D.brOnNonNull a₂ _ h₂
  have hv : v ≠ .ref .null := fun hnull => by
    have hx : xv = caseNilV "REF.NULL_ADDR" := by rw [← h₁, hnull]; rfl
    exact not_otherwise_nonNull RR (e₀ ▸ hq) (hx ▸ fx) fl (hx ▸ ho)
  have hlv : lv = pctV l.toNat := (Value.case.inj h₂).2.symm
  have hw : w = .list (adminsToV [v.toAdmin, .plain (.br l)]) := by
    rw [(tuple2_inj hc).2, ← h₁, hlv]
    rfl
  exact ⟨_, hw, .brOnNonNullAddr hv⟩

end Bwd

end Silmaril.Wasm.SpecTec.Sim.Bwd
