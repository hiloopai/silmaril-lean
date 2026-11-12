module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.Forward

/-!
# Family C: the two `otherwise` rules, `br_on_null-addr` and `br_on_non_null-addr`

Under SpecTec's `else` reading (`Sim.otherwise`), `br_on_null-addr` (rule 16 of `Step_pure`) may
fire on `[val, BR_ON_NULL l]` only if no earlier rule fires on the same left-hand side. Rules 0–14
cannot match that shape at all: each one's left-hand side is a list literal of a different length,
or with a different constructor in second position (`lhs_refute`). Rule 15, `br_on_null-null`,
has the same shape, and is excluded by its premise `val = REF.NULL_ADDR` (`nullPrem`). The same
argument, over rules 0–17, gives `br_on_non_null-addr`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecRef (brOnNullAddrRule brOnNonNullAddrRule)

/-! ## Reading a rule body -/

/-- A rule body evaluates its conclusion, and its premises hold, in one scope. -/
theorem ruleBody_concl {env : Env} {D : Interp} {els : Prop} {op : MixopS} {nm : IL.Id}
    {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem} {w : Value}
    (h : RuleBody env D els [] [] op (.ruleD nm qs op' e prems) w) :
    ∃ ρ, EvalExp env ρ e w ∧ ∀ pr ∈ prems, PremW env D els ρ pr := by
  obtain ⟨-, ρ₀, σ, -, -, he, hp⟩ := h
  exact ⟨_, he, hp⟩

/-- The left component of a pair conclusion. -/
theorem lhs_of_tup {env : Env} {ρ : VarEnv} {L R : Exp} {a c : Value}
    (h : EvalExp env ρ (.tupE [L, R]) (.tuple [a, c])) : EvalExp env ρ L a := by
  obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 h
  obtain ⟨w, ws, rfl, hw, -⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  cases hv
  exact hw

/-- Two rule facts about one relation give the second rule's index in the first's rule list. -/
theorem ruleAt_get {env : Env} {x : IL.Id} {k : Nat} {r : Rule} {ps : List Param} {op : MixopS}
    {t : Typ} {rules : List Rule} (h : HasRuleAt env x "%~>%" k r)
    (hrel : env.findRel? x = some (ps, op, t, rules)) : rules[k]? = some r := by
  obtain ⟨ps', t', rules', hrel', -, hk⟩ := h
  rw [hrel] at hrel'
  simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
  rw [hrel'.2.2.2]
  exact hk

/-- Refute a rule body whose left-hand side cannot have the given shape. -/
macro "lhs_refute " h:ident : tactic => `(tactic| (
  obtain ⟨ρ, he, -⟩ := ruleBody_concl $h
  have hL := lhs_of_tup he
  simp [evalExp_listE_iff, Equiv.Validation.evalExps_cons_iff, Equiv.Validation.evalExps_nil_iff, evalExp_caseE_iff] at hL))

/-- The premise `val = REF.NULL_ADDR` of `br_on_null-null` and `br_on_non_null-null`. -/
theorem nullPrem {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {x : Value}
    (hx : EvalExp env ρ (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) x)
    (hp : PremW env D els ρ (.ifPr (.cmpE .eqOp .boolT (.varE "val")
      (.caseE "REF.NULL_ADDR" (.tupE []))))) : x = caseNilV "REF.NULL_ADDR" := by
  have hv : EvalExp env ρ (.varE "val") x := evalExp_subE_iff.1 hx
  cases hp with
  | ifPr h =>
    obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
    have e₁ : v₁ = x := EvalExp.unique h₁ hv
    have e₂ : v₂ = caseNilV "REF.NULL_ADDR" := EvalExp.unique h₂ evalExp_caseNil
    subst e₁ e₂
    simpa [cmpValues] using hc

/-- `br_on_null-null` cannot fire on a non-null value. -/
theorem not_brOnNullNull {env : Env} {D : Interp} {els : Prop} {x l c : Value}
    (hx : x ≠ caseNilV "REF.NULL_ADDR")
    (h : RuleBody env D els [] [] "%~>%" Equiv.ExecRef.brOnNullNullRule
      (.tuple [.list [x, .case "BR_ON_NULL" l], c])) : False := by
  obtain ⟨ρ, he, hp⟩ := ruleBody_concl h
  have hL := lhs_of_tup he
  obtain ⟨vs, hvs, hv⟩ := evalExp_listE_iff.1 hL
  obtain ⟨w, ws, rfl, hw, -⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  have hwx : w = x := by injection hv with hv; exact (List.cons.inj hv).1.symm
  subst hwx
  exact hx (nullPrem hw (hp _ (by simp)))

/-- `br_on_non_null-null` cannot fire on a non-null value. -/
theorem not_brOnNonNullNull {env : Env} {D : Interp} {els : Prop} {x l c : Value}
    (hx : x ≠ caseNilV "REF.NULL_ADDR")
    (h : RuleBody env D els [] [] "%~>%" Equiv.ExecRef.brOnNonNullNullRule
      (.tuple [.list [x, .case "BR_ON_NON_NULL" l], c])) : False := by
  obtain ⟨ρ, he, hp⟩ := ruleBody_concl h
  have hL := lhs_of_tup he
  obtain ⟨vs, hvs, hv⟩ := evalExp_listE_iff.1 hL
  obtain ⟨w, ws, rfl, hw, -⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  have hwx : w = x := by injection hv with hv; exact (List.cons.inj hv).1.symm
  subst hwx
  exact hx (nullPrem hw (hp _ (by simp)))

/-! ## The two `otherwise` premises in `simEnv B` -/

/-- Unfold `otherwise` at a rule of `Step_pure`. -/
theorem otherwise_intro {env : Env} {i : Nat} {v : Value}
    (h : ∀ j, j < i → ∀ ps op t rules r, env.findRel? "Step_pure" = some (ps, op, t, rules) →
      rules[j]? = some r → ∀ w, SameLhs v w →
        ¬ RuleBody env (DDerives env noElse) (otherwiseAt env "Step_pure" [] j w) ps [] op r w) :
    otherwise env "Step_pure" [] i v := by
  unfold otherwise
  rw [otherwiseAt]
  exact h

/-- The relation lookup of `Step_pure` has no parameters and operator `%~>%`. -/
theorem stepPure_rel {env : Env} (R : Equiv.Execution.HasStepRules env) {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule}
    (hrel : env.findRel? "Step_pure" = some (ps, op, t, rules)) : ps = [] ∧ op = "%~>%" := by
  obtain ⟨ps', t', rules', hrel', hps, -⟩ := R.nop
  rw [hrel] at hrel'
  simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
  exact ⟨hrel'.1.trans hps, hrel'.2.1⟩

/-- `otherwise` at a left-hand side `a₀`, from a refutation of every earlier rule at `a₀`, each
rule given by its provenance. -/
theorem otherwise_simEnv (B : Builtins) {i : Nat} {a₀ b₀ : Value}
    (h : ∀ j, j < i → ∀ r, (∀ {k r'}, HasRuleAt (simEnv B) "Step_pure" "%~>%" k r' → k = j →
      r = r') → ∀ c, ¬ RuleBody (simEnv B) (DDerives (simEnv B) noElse)
        (otherwiseAt (simEnv B) "Step_pure" [] j (.tuple [a₀, c])) [] [] "%~>%" r (.tuple [a₀, c])) :
    otherwise (simEnv B) "Step_pure" [] i (.tuple [a₀, b₀]) := by
  have R : Equiv.Execution.HasStepRules (simEnv B) := simEnv_execRules B
  refine otherwise_intro fun j hj ps op t rules r hrel hr w hw => ?_
  have hpo : ps = [] ∧ op = "%~>%" := stepPure_rel R hrel
  obtain ⟨a, b, d, hv, hwd⟩ := hw
  have ha : a = a₀ := (List.cons.inj (Value.tuple.inj hv)).1.symm
  have hget : ∀ {k r'}, HasRuleAt (simEnv B) "Step_pure" "%~>%" k r' → k = j → r = r' :=
    fun h hk => Option.some.inj (hr.symm.trans (hk ▸ ruleAt_get h hrel))
  have hn := h j hj r hget d
  rw [hwd, ha, hpo.1, hpo.2]
  exact hn

/-- **`otherwise` holds for `br_on_null-addr` at a non-null value.** -/
theorem otherwise_brOnNullAddr (B : Builtins) {x l c : Value} (hx : x ≠ caseNilV "REF.NULL_ADDR") :
    otherwise (simEnv B) "Step_pure" [] 16 (.tuple [.list [x, .case "BR_ON_NULL" l], c]) :=
  otherwise_simEnv B fun j hj r get d hb =>
    have R : Equiv.Execution.HasStepRules (simEnv B) := simEnv_execRules B
    have RD : Equiv.ExecDefault.HasBrTableRules (simEnv B) := simEnv_brTableRules B
    have RR : Equiv.ExecRef.HasRefRules (simEnv B) := simEnv_refRules B
    match j, hj with
    | 0, _ => by cases get R.unreachable rfl; lhs_refute hb
    | 1, _ => by cases get R.nop rfl; lhs_refute hb
    | 2, _ => by cases get R.drop rfl; lhs_refute hb
    | 3, _ => by cases get R.selectTrue rfl; lhs_refute hb
    | 4, _ => by cases get R.selectFalse rfl; lhs_refute hb
    | 5, _ => by cases get R.ifTrue rfl; lhs_refute hb
    | 6, _ => by cases get R.ifFalse rfl; lhs_refute hb
    | 7, _ => by cases get R.labelVals rfl; lhs_refute hb
    | 8, _ => by cases get R.brLabelZero rfl; lhs_refute hb
    | 9, _ => by cases get R.brLabelSucc rfl; lhs_refute hb
    | 10, _ => by cases get R.brHandler rfl; lhs_refute hb
    | 11, _ => by cases get R.brIfTrue rfl; lhs_refute hb
    | 12, _ => by cases get R.brIfFalse rfl; lhs_refute hb
    | 13, _ => by cases get RD.brTableLt rfl; lhs_refute hb
    | 14, _ => by cases get RD.brTableGe rfl; lhs_refute hb
    | 15, _ => by cases get RR.brOnNullNull rfl; exact not_brOnNullNull hx hb
    | _ + 16, hj => absurd hj (by omega)

/-- **`otherwise` holds for `br_on_non_null-addr` at a non-null value.** -/
theorem otherwise_brOnNonNullAddr (B : Builtins) {x l c : Value}
    (hx : x ≠ caseNilV "REF.NULL_ADDR") :
    otherwise (simEnv B) "Step_pure" [] 18 (.tuple [.list [x, .case "BR_ON_NON_NULL" l], c]) :=
  otherwise_simEnv B fun j hj r get d hb =>
    have R : Equiv.Execution.HasStepRules (simEnv B) := simEnv_execRules B
    have RD : Equiv.ExecDefault.HasBrTableRules (simEnv B) := simEnv_brTableRules B
    have RR : Equiv.ExecRef.HasRefRules (simEnv B) := simEnv_refRules B
    match j, hj with
    | 0, _ => by cases get R.unreachable rfl; lhs_refute hb
    | 1, _ => by cases get R.nop rfl; lhs_refute hb
    | 2, _ => by cases get R.drop rfl; lhs_refute hb
    | 3, _ => by cases get R.selectTrue rfl; lhs_refute hb
    | 4, _ => by cases get R.selectFalse rfl; lhs_refute hb
    | 5, _ => by cases get R.ifTrue rfl; lhs_refute hb
    | 6, _ => by cases get R.ifFalse rfl; lhs_refute hb
    | 7, _ => by cases get R.labelVals rfl; lhs_refute hb
    | 8, _ => by cases get R.brLabelZero rfl; lhs_refute hb
    | 9, _ => by cases get R.brLabelSucc rfl; lhs_refute hb
    | 10, _ => by cases get R.brHandler rfl; lhs_refute hb
    | 11, _ => by cases get R.brIfTrue rfl; lhs_refute hb
    | 12, _ => by cases get R.brIfFalse rfl; lhs_refute hb
    | 13, _ => by cases get RD.brTableLt rfl; lhs_refute hb
    | 14, _ => by cases get RD.brTableGe rfl; lhs_refute hb
    | 15, _ => by cases get RR.brOnNullNull rfl; lhs_refute hb
    | 16, _ => by cases get RR.brOnNullAddr rfl; lhs_refute hb
    | 17, _ => by cases get RR.brOnNonNullNull rfl; exact not_brOnNonNullNull hx hb
    | _ + 18, hj => absurd hj (by omega)

/-! ## The constructions and the forward fields -/

/-- `Step_pure/br_on_null-addr`, at a value its `otherwise` admits. -/
theorem spure_brOnNullAddr {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 16 brOnNullAddrRule)
    {x l : Value} (hx : TypedV env valT x) (hl : TypedV env labelidxT l)
    (ho : otherwise env "Step_pure" [] 16 (.tuple [.list [x, .case "BR_ON_NULL" l], .list [x]])) :
    SPure env [x, .case "BR_ON_NULL" l] [x] := by
  let ρ := VarEnv.empty.bindVals [("val", x), ("l", l)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fv : ρ.findVal? "val" = some x := rfl
  have fl : ρ.findVal? "l" = some l := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fv (hx ρ hρ) (QuantsOk.cons fl (hl ρ hρ) QuantsOk.nil))
    (evalExp_tup2
      (evalExp_list2 (evalExp_sub (evalExp_var fv)) (evalExp_case (evalExp_var fl)))
      (evalExp_list1 (evalExp_sub (evalExp_var fv))))
    (prems_one (.elsePr ho))

/-- `Step_pure/br_on_non_null-addr`, at a value its `otherwise` admits. -/
theorem spure_brOnNonNullAddr {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 18 brOnNonNullAddrRule)
    {x l : Value} (hx : TypedV env valT x) (hl : TypedV env labelidxT l)
    (ho : otherwise env "Step_pure" [] 18
      (.tuple [.list [x, .case "BR_ON_NON_NULL" l], .list [x, .case "BR" l]])) :
    SPure env [x, .case "BR_ON_NON_NULL" l] [x, .case "BR" l] := by
  let ρ := VarEnv.empty.bindVals [("val", x), ("l", l)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fv : ρ.findVal? "val" = some x := rfl
  have fl : ρ.findVal? "l" = some l := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fv (hx ρ hρ) (QuantsOk.cons fl (hl ρ hρ) QuantsOk.nil))
    (evalExp_tup2
      (evalExp_list2 (evalExp_sub (evalExp_var fv)) (evalExp_case (evalExp_var fl)))
      (evalExp_list2 (evalExp_sub (evalExp_var fv)) (evalExp_case (evalExp_var fl))))
    (prems_one (.elsePr ho))

section Fwd

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-- Only the null reference is encoded as `REF.NULL_ADDR`. -/
theorem valV_ne_null {v : Val} (h : v ≠ .ref .null) : valV v ≠ caseNilV "REF.NULL_ADDR" := by
  intro he
  cases v with
  | num n => simp [valV, caseNilV] at he
  | vec b => simp [valV, caseNilV] at he
  | ref r => cases r <;> simp_all [valV, Equiv.RuntimeBridge.refToValue, caseNilV]

variable {H : Type} {hn : H → String}
variable (B : Builtins) (T : TypingFacts (simEnv B) hn) (Tg : CtrlTyping (simEnv B))

include T Tg in
/-- `Forward.brOnNullAddr`. -/
theorem fwd_brOnNullAddr : ∀ {s : Store H} {f : Frame} {v : Val} {l : LabelIdx}
    (_ : v ≠ .ref .null),
    FwdP (simEnv B) hn ⟨s, f, [v.toAdmin, .plain (.brOnNull l)]⟩ ⟨s, f, [v.toAdmin]⟩ := by
  intro s f v l hv
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  have hvs := typedV_vals_prefix T (vs := [v]) (b := [.plain (.brOnNull l)]) h
  have hx : TypedV (simEnv B) valT (valV v) := by
    simpa [adminsToV_vals] using typedV_list_single.1 (by simpa [adminsToV_vals] using hvs)
  have key := spure_brOnNullAddr (simEnv_refRules B).brOnNullAddr hx (Tg.labelidx l)
    (otherwise_brOnNullAddr B (valV_ne_null hv))
  have e : adminToV (.plain (.brOnNull l)) = .case "BR_ON_NULL" (Encode.toValue l) := rfl
  simpa [adminToV_toAdmin, e] using key

include T Tg in
/-- `Forward.brOnNonNullAddr`. -/
theorem fwd_brOnNonNullAddr : ∀ {s : Store H} {f : Frame} {v : Val} {l : LabelIdx}
    (_ : v ≠ .ref .null),
    FwdP (simEnv B) hn ⟨s, f, [v.toAdmin, .plain (.brOnNonNull l)]⟩
      ⟨s, f, [v.toAdmin, .plain (.br l)]⟩ := by
  intro s f v l hv
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  have hvs := typedV_vals_prefix T (vs := [v]) (b := [.plain (.brOnNonNull l)]) h
  have hx : TypedV (simEnv B) valT (valV v) := by
    simpa [adminsToV_vals] using typedV_list_single.1 (by simpa [adminsToV_vals] using hvs)
  have key := spure_brOnNonNullAddr (simEnv_refRules B).brOnNonNullAddr hx (Tg.labelidx l)
    (otherwise_brOnNonNullAddr B (valV_ne_null hv))
  have e : adminToV (.plain (.brOnNonNull l)) = .case "BR_ON_NON_NULL" (pctV l.toNat) := rfl
  simpa [adminToV_toAdmin, toValue_idx, e] using key

end Fwd

end Silmaril.Wasm.SpecTec.Sim
