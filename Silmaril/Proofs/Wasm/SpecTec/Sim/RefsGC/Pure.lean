module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefsGC.Common

/-!
# Family R: the reference rules of `Step_pure`, forward

Core's pure reference steps (`RefStep`'s `refI31`, `isNull*`, `asNonNull*`, `eq*`, `i31Get*`,
`externConvert*`, `anyConvert*`) as `Step_pure` steps of their images, rules 31–45 except 41
(`array.new`, see `Aggregate`). The `otherwise` rules (33, 35, 37, 38, 43) are discharged by
`otherwise_of_ruleAt`: every earlier rule of `Step_pure` names an opcode foreign to the
instruction, except the rules of the same instruction, which are refuted by hand (`not_*`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefsGC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.SpecTec.Equiv.ExecRef
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {env : Env}

/-- The null reference, as SpecTec writes it. -/
theorem refToValue_null : refToValue .null = .case "REF.NULL_ADDR" (.tuple []) := rfl

/-- Only the null reference is encoded as `REF.NULL_ADDR`. -/
theorem eq_null_of_refToValue {r : Ref} (h : refToValue r = .case "REF.NULL_ADDR" (.tuple [])) :
    r = .null := by
  cases r <;> simp_all [refToValue]

/-- An `if ref = REF.NULL_ADDR` premise that holds, with `ref` bound to `refToValue r`, gives
`r = null`. -/
theorem null_of_ifPr {D : Interp} {els : Prop} {ρ : VarEnv} {x : IL.Id} {r : Ref}
    (hx : EvalExp env ρ (.varE x) (refToValue r))
    (h : PremW env D els ρ
      (.ifPr (.cmpE .eqOp .boolT (.varE x) (.caseE "REF.NULL_ADDR" (.tupE []))))) :
    r = .null := by
  have hn : EvalExp env ρ (.caseE "REF.NULL_ADDR" (.tupE [])) (.case "REF.NULL_ADDR" (.tuple [])) :=
    by eval_tac
  exact eq_null_of_refToValue (eq_of_evalExp_eq (premW_if h) hx hn)

/-- The first element of a two-element left-hand side `[subE (varE x) …, _]`. -/
theorem var_of_lhs2 {ρ : VarEnv} {x : IL.Id} {t₁ t₂ : Typ} {e₂ rh : Exp} {a b c : Value}
    (he : EvalExp env ρ (.tupE [.listE [.subE (.varE x) t₁ t₂, e₂], rh]) (.tuple [.list [a, b], c])) :
    EvalExp env ρ (.varE x) a :=
  evalExp_subE_iff.1 (evalExps_cons_inv (elems_of_list (lhs_of_concl he))).1

/-- The first two elements of a three-element left-hand side `[subE (varE x) …, subE (varE y) …, _]`. -/
theorem vars_of_lhs3 {ρ : VarEnv} {x y : IL.Id} {t₁ t₂ t₃ t₄ : Typ} {e₃ rh : Exp}
    {a b d c : Value}
    (he : EvalExp env ρ (.tupE [.listE [.subE (.varE x) t₁ t₂, .subE (.varE y) t₃ t₄, e₃], rh])
      (.tuple [.list [a, b, d], c])) :
    EvalExp env ρ (.varE x) a ∧ EvalExp env ρ (.varE y) b := by
  have hs := elems_of_list (lhs_of_concl he)
  have h₁ := evalExps_cons_inv hs
  have h₂ := evalExps_cons_inv h₁.2
  exact ⟨evalExp_subE_iff.1 h₁.1, evalExp_subE_iff.1 h₂.1⟩

/-! ## The rules that need no `otherwise` -/

/-- `ref.is_null-true` (rule 32). -/
theorem spure_isNullTrue (h : HasRuleAt env "Step_pure" "%~>%" 32 refIsNullTrueRule)
    (ht : TypedV env refT (refToValue .null)) :
    SPure env (adminsToV [.ref .null, .plain .refIsNull]) (adminsToV [constI32 1]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals [("ref", refToValue .null)]) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt h [("ref", refToValue .null)]
    (QuantsOk.cons rfl (ht _ hρ) QuantsOk.nil) (by eval_tac) (prems_one (.ifPr ?_))
  exact evalExp_eq_true (by eval_tac) (by eval_tac)

/-- `ref.as_non_null-null` (rule 34). -/
theorem spure_asNonNullNull (h : HasRuleAt env "Step_pure" "%~>%" 34 refAsNonNullNullRule)
    (ht : TypedV env refT (refToValue .null)) :
    SPure env (adminsToV [.ref .null, .plain .refAsNonNull]) (adminsToV [.trap]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals [("ref", refToValue .null)]) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt h [("ref", refToValue .null)]
    (QuantsOk.cons rfl (ht _ hρ) QuantsOk.nil) (by eval_tac) (prems_one (.ifPr ?_))
  exact evalExp_eq_true (by eval_tac) (by eval_tac)

/-- `ref.eq-null` (rule 36). -/
theorem spure_eqNull (h : HasRuleAt env "Step_pure" "%~>%" 36 refEqNullRule)
    (ht : TypedV env refT (refToValue .null)) :
    SPure env (adminsToV [.ref .null, .ref .null, .plain .refEq]) (adminsToV [constI32 1]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals
    [("ref_1", refToValue .null), ("ref_2", refToValue .null)]) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt h [("ref_1", refToValue .null), ("ref_2", refToValue .null)]
    (QuantsOk.cons rfl (ht _ hρ) (QuantsOk.cons rfl (ht _ hρ) QuantsOk.nil)) (by eval_tac)
    (prems_one (.ifPr ?_))
  exact evalExp_and_true (evalExp_eq_true (by eval_tac) (by eval_tac))
    (evalExp_eq_true (by eval_tac) (by eval_tac))

/-- `i31.get-null` (rule 39). -/
theorem spure_i31GetNull (h : HasRuleAt env "Step_pure" "%~>%" 39 i31GetNullRule)
    (R : RTyping env) (s : Signedness) :
    SPure env (adminsToV [.ref .null, .plain (.i31Get s)]) (adminsToV [.trap]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals [("sx", sxV s)]) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h [("sx", sxV s)] (QuantsOk.cons rfl (R.sx s _ hρ) QuantsOk.nil)
    (by eval_tac) (fun _ hp => nomatch hp)

/-- `i31.get-num` (rule 40), given `$extend__`. -/
theorem spure_i31GetNum (h : HasRuleAt env "Step_pure" "%~>%" 40 i31GetNumRule)
    (R : RTyping env) (F : RFuns env) (s : Signedness) (i : BitVec 31) :
    SPure env (adminsToV [.ref (.i31 i), .plain (.i31Get s)])
      (adminsToV [constI32 (match s with | .signed => i.signExtend 32 | .unsigned => i.setWidth 32)]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals [("i", pctV i.toNat), ("sx", sxV s)]) :=
    ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt h [("i", pctV i.toNat), ("sx", sxV s)]
    (QuantsOk.cons rfl (R.u31 i _ hρ) (QuantsOk.cons rfl (R.sx s _ hρ) QuantsOk.nil))
    (evalExp_tup2 (by eval_tac) ?_) (fun _ hp => nomatch hp)
  have hx := F.extend (VarEnv.empty.bindVals [("i", pctV i.toNat), ("sx", sxV s)]) (.varE "sx")
    (.varE "i") s i ⟨rfl, rfl, rfl⟩ (by eval_tac) (by eval_tac)
  cases s <;>
    exact evalExp_listE_of (evalExps_cons' (evalExp_case (evalExp_tupE_of
      (evalExps_cons' (by eval_tac) (evalExps_cons' hx evalExps_nil')))) evalExps_nil')

/-- `ref.i31` (rule 31), given `$wrap__`. -/
theorem spure_refI31 (h : HasRuleAt env "Step_pure" "%~>%" 31 refI31Rule) (R : RTyping env)
    (F : RFuns env) (i : BitVec 32) :
    SPure env (adminsToV [constI32 i, .plain .refI31]) (adminsToV [.ref (.i31 (i.setWidth 31))]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals [("i", pctV i.toNat)]) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt h [("i", pctV i.toNat)] (QuantsOk.cons rfl (R.i32 i _ hρ) QuantsOk.nil)
    (evalExp_tup2 (by eval_tac) ?_) (fun _ hp => nomatch hp)
  have hw := F.wrap (VarEnv.empty.bindVals [("i", pctV i.toNat)]) (.varE "i") i ⟨rfl, rfl, rfl⟩ (by eval_tac)
  exact evalExp_listE_of (evalExps_cons' (evalExp_case hw) evalExps_nil')

/-- `extern.convert_any-null` (rule 42). -/
theorem spure_externConvertNull (h : HasRuleAt env "Step_pure" "%~>%" 42 externConvertAnyNullRule)
    (ht : TypedV env refT (refToValue .null)) :
    SPure env (adminsToV [.ref .null, .plain .externConvertAny]) (adminsToV [.ref .null]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals [("ref", refToValue .null)]) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt h [("ref", refToValue .null)]
    (QuantsOk.cons rfl (ht _ hρ) QuantsOk.nil) (by eval_tac) (prems_one (.ifPr ?_))
  exact evalExp_eq_true (by eval_tac) (by eval_tac)

/-- `any.convert_extern-null` (rule 44). -/
theorem spure_anyConvertNull (h : HasRuleAt env "Step_pure" "%~>%" 44 anyConvertExternNullRule) :
    SPure env (adminsToV [.ref .null, .plain .anyConvertExtern]) (adminsToV [.ref .null]) :=
  dderives_of_ruleAt h [] QuantsOk.nil (by eval_tac) (fun _ hp => nomatch hp)

/-- `any.convert_extern-addr` (rule 45). -/
theorem spure_anyConvertAddr (h : HasRuleAt env "Step_pure" "%~>%" 45 anyConvertExternAddrRule)
    {r : Ref} (ht : TypedV env refT (refToValue r)) :
    SPure env (adminsToV [.ref (.extern r), .plain .anyConvertExtern]) (adminsToV [.ref r]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals [("ref", refToValue r)]) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h [("ref", refToValue r)] (QuantsOk.cons rfl (ht _ hρ) QuantsOk.nil)
    (by eval_tac) (fun _ hp => nomatch hp)

/-! ## The `otherwise` rules -/

/-- `ref.is_null-true` does not fire on a non-null reference. -/
theorem not_isNullTrue {D : Interp} {els : Prop} {r : Ref} (hr : r ≠ .null) {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" refIsNullTrueRule
      (.tuple [.list (adminsToV [.ref r, .plain .refIsNull]), c]) := by
  rintro ⟨-, ρ₀, σ, -, -, he, hp⟩
  exact hr (null_of_ifPr (var_of_lhs2 he) (hp _ (List.mem_singleton_self _)))

/-- `ref.is_null-false` (rule 33). -/
theorem spure_isNullFalse (h : HasRuleAt env "Step_pure" "%~>%" 33 refIsNullFalseRule)
    (h₃₂ : HasRuleAt env "Step_pure" "%~>%" 32 refIsNullTrueRule)
    (hT : ((relRules env "Step_pure").map ruleTags).take 46 = pureTagTable) {r : Ref}
    (hr : r ≠ .null) (ht : TypedV env refT (refToValue r)) :
    SPure env (adminsToV [.ref r, .plain .refIsNull]) (adminsToV [constI32 0]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals [("ref", refToValue r)]) := ⟨rfl, rfl, rfl⟩
  have ha : LhsIn (["REF.IS_NULL"] ++ valTags) (.list (adminsToV [.ref r, .plain .refIsNull])) :=
    .inl ⟨_, rfl, tagsIn_cons (tag_ref (refTags_sub _) r)
      (tagsIn_cons (tag_case (by decide)) tagsIn_nil)⟩
  have hel := otherwise_of_ruleAt h hT (i := 33) (b := .list (adminsToV [constI32 0])) (by decide)
    (exc := [32]) ha (by decide) (by
    intro j hj _ r' hr' w hw
    obtain rfl : j = 32 := by simpa using hj
    rw [relRules_of_ruleAt h₃₂ hr']
    obtain ⟨c, rfl⟩ := sameLhs_inv hw
    exact not_isNullTrue hr)
  exact dderives_of_ruleAt h [("ref", refToValue r)] (QuantsOk.cons rfl (ht _ hρ) QuantsOk.nil)
    (by eval_tac) (prems_one (.elsePr hel))

/-- `ref.as_non_null-null` does not fire on a non-null reference. -/
theorem not_asNonNullNull {D : Interp} {els : Prop} {r : Ref} (hr : r ≠ .null) {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" refAsNonNullNullRule
      (.tuple [.list (adminsToV [.ref r, .plain .refAsNonNull]), c]) := by
  rintro ⟨-, ρ₀, σ, -, -, he, hp⟩
  exact hr (null_of_ifPr (var_of_lhs2 he) (hp _ (List.mem_singleton_self _)))

/-- `ref.as_non_null-addr` (rule 35). -/
theorem spure_asNonNullAddr (h : HasRuleAt env "Step_pure" "%~>%" 35 refAsNonNullAddrRule)
    (h₃₄ : HasRuleAt env "Step_pure" "%~>%" 34 refAsNonNullNullRule)
    (hT : ((relRules env "Step_pure").map ruleTags).take 46 = pureTagTable) {r : Ref}
    (hr : r ≠ .null) (ht : TypedV env refT (refToValue r)) :
    SPure env (adminsToV [.ref r, .plain .refAsNonNull]) (adminsToV [.ref r]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals [("ref", refToValue r)]) := ⟨rfl, rfl, rfl⟩
  have ha : LhsIn (["REF.AS_NON_NULL"] ++ valTags)
      (.list (adminsToV [.ref r, .plain .refAsNonNull])) :=
    .inl ⟨_, rfl, tagsIn_cons (tag_ref (refTags_sub _) r)
      (tagsIn_cons (tag_case (by decide)) tagsIn_nil)⟩
  have hel := otherwise_of_ruleAt h hT (i := 35) (b := .list (adminsToV [.ref r])) (by decide)
    (exc := [34]) ha (by decide) (by
    intro j hj _ r' hr' w hw
    obtain rfl : j = 34 := by simpa using hj
    rw [relRules_of_ruleAt h₃₄ hr']
    obtain ⟨c, rfl⟩ := sameLhs_inv hw
    exact not_asNonNullNull hr)
  exact dderives_of_ruleAt h [("ref", refToValue r)] (QuantsOk.cons rfl (ht _ hρ) QuantsOk.nil)
    (by eval_tac) (prems_one (.elsePr hel))

/-- `extern.convert_any-null` does not fire on a non-null reference. -/
theorem not_externConvertNull {D : Interp} {els : Prop} {r : Ref} (hr : r ≠ .null) {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" externConvertAnyNullRule
      (.tuple [.list (adminsToV [.ref r, .plain .externConvertAny]), c]) := by
  rintro ⟨-, ρ₀, σ, -, -, he, hp⟩
  exact hr (null_of_ifPr (var_of_lhs2 he) (hp _ (List.mem_singleton_self _)))

/-- `extern.convert_any-addr` (rule 43). -/
theorem spure_externConvertAddr (h : HasRuleAt env "Step_pure" "%~>%" 43 externConvertAnyAddrRule)
    (h₄₂ : HasRuleAt env "Step_pure" "%~>%" 42 externConvertAnyNullRule)
    (hT : ((relRules env "Step_pure").map ruleTags).take 46 = pureTagTable) {r : Ref}
    (hr : r ≠ .null) (ht : TypedV env refT (refToValue r)) :
    SPure env (adminsToV [.ref r, .plain .externConvertAny]) (adminsToV [.ref (.extern r)]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals [("ref", refToValue r)]) := ⟨rfl, rfl, rfl⟩
  have ha : LhsIn (["EXTERN.CONVERT_ANY"] ++ valTags)
      (.list (adminsToV [.ref r, .plain .externConvertAny])) :=
    .inl ⟨_, rfl, tagsIn_cons (tag_ref (refTags_sub _) r)
      (tagsIn_cons (tag_case (by decide)) tagsIn_nil)⟩
  have hel := otherwise_of_ruleAt h hT (i := 43) (b := .list (adminsToV [.ref (.extern r)])) (by decide)
    (exc := [42]) ha (by decide) (by
    intro j hj _ r' hr' w hw
    obtain rfl : j = 42 := by simpa using hj
    rw [relRules_of_ruleAt h₄₂ hr']
    obtain ⟨c, rfl⟩ := sameLhs_inv hw
    exact not_externConvertNull hr)
  exact dderives_of_ruleAt h [("ref", refToValue r)] (QuantsOk.cons rfl (ht _ hρ) QuantsOk.nil)
    (by eval_tac) (prems_one (.elsePr hel))

/-- `ref.eq-null` does not fire when the two references differ or one is not null. -/
theorem not_eqNull {D : Interp} {els : Prop} {r₁ r₂ : Ref} (hr : ¬ (r₁ = .null ∧ r₂ = .null))
    {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" refEqNullRule
      (.tuple [.list (adminsToV [.ref r₁, .ref r₂, .plain .refEq]), c]) := by
  rintro ⟨-, ρ₀, σ, -, -, he, hp⟩
  obtain ⟨h₁, h₂⟩ := vars_of_lhs3 he
  have hif := premW_if (hp _ (List.mem_singleton_self _))
  have hn : EvalExp env (ρ₀.bindVals σ) (.caseE "REF.NULL_ADDR" (.tupE []))
      (.case "REF.NULL_ADDR" (.tuple [])) := by eval_tac
  have hb := EvalExp.unique hif (evalExp_and (evalExp_eq h₁ hn) (evalExp_eq h₂ hn))
  simp only [Value.bool.injEq, Bool.true_eq, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact hr ⟨eq_null_of_refToValue hb.1, eq_null_of_refToValue hb.2⟩

/-- `ref.eq-true` (rule 37). -/
theorem spure_eqTrue (h : HasRuleAt env "Step_pure" "%~>%" 37 refEqTrueRule)
    (h₃₆ : HasRuleAt env "Step_pure" "%~>%" 36 refEqNullRule)
    (hT : ((relRules env "Step_pure").map ruleTags).take 46 = pureTagTable) {r : Ref}
    (hr : r ≠ .null) (ht : TypedV env refT (refToValue r)) :
    SPure env (adminsToV [.ref r, .ref r, .plain .refEq]) (adminsToV [constI32 1]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals [("ref_1", refToValue r), ("ref_2", refToValue r)]) :=
    ⟨rfl, rfl, rfl⟩
  have ha : LhsIn (["REF.EQ"] ++ valTags) (.list (adminsToV [.ref r, .ref r, .plain .refEq])) :=
    .inl ⟨_, rfl, tagsIn_cons (tag_ref (refTags_sub _) r) (tagsIn_cons (tag_ref (refTags_sub _) r)
      (tagsIn_cons (tag_case (by decide)) tagsIn_nil))⟩
  have hel := otherwise_of_ruleAt h hT (i := 37) (b := .list (adminsToV [constI32 1])) (by decide)
    (exc := [36]) ha (by decide) (by
    intro j hj _ r' hr' w hw
    obtain rfl : j = 36 := by simpa using hj
    rw [relRules_of_ruleAt h₃₆ hr']
    obtain ⟨c, rfl⟩ := sameLhs_inv hw
    exact not_eqNull (fun h => hr h.1))
  exact dderives_of_ruleAt h [("ref_1", refToValue r), ("ref_2", refToValue r)]
    (QuantsOk.cons rfl (ht _ hρ) (QuantsOk.cons rfl (ht _ hρ) QuantsOk.nil)) (by eval_tac)
    (prems_two (.elsePr hel) (.ifPr (evalExp_eq_true (by eval_tac) (by eval_tac))))

/-- `ref.eq-true` does not fire on two different references. -/
theorem not_eqTrue {D : Interp} {els : Prop} {r₁ r₂ : Ref} (hr : r₁ ≠ r₂) {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" refEqTrueRule
      (.tuple [.list (adminsToV [.ref r₁, .ref r₂, .plain .refEq]), c]) := by
  rintro ⟨-, ρ₀, σ, -, -, he, hp⟩
  obtain ⟨h₁, h₂⟩ := vars_of_lhs3 he
  have hif := premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have heq : refToValue r₁ = refToValue r₂ := eq_of_evalExp_eq hif h₁ h₂
  exact hr (Equiv.RuntimeBridge.refToValue_inj heq)

/-- `ref.eq-false` (rule 38). -/
theorem spure_eqFalse (h : HasRuleAt env "Step_pure" "%~>%" 38 refEqFalseRule)
    (h₃₆ : HasRuleAt env "Step_pure" "%~>%" 36 refEqNullRule)
    (h₃₇ : HasRuleAt env "Step_pure" "%~>%" 37 refEqTrueRule)
    (hT : ((relRules env "Step_pure").map ruleTags).take 46 = pureTagTable) {r₁ r₂ : Ref}
    (hr : r₁ ≠ r₂) (ht₁ : TypedV env refT (refToValue r₁)) (ht₂ : TypedV env refT (refToValue r₂)) :
    SPure env (adminsToV [.ref r₁, .ref r₂, .plain .refEq]) (adminsToV [constI32 0]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals
    [("ref_1", refToValue r₁), ("ref_2", refToValue r₂)]) := ⟨rfl, rfl, rfl⟩
  have ha : LhsIn (["REF.EQ"] ++ valTags) (.list (adminsToV [.ref r₁, .ref r₂, .plain .refEq])) :=
    .inl ⟨_, rfl, tagsIn_cons (tag_ref (refTags_sub _) r₁)
      (tagsIn_cons (tag_ref (refTags_sub _) r₂) (tagsIn_cons (tag_case (by decide)) tagsIn_nil))⟩
  have hel := otherwise_of_ruleAt h hT (i := 38) (b := .list (adminsToV [constI32 0])) (by decide)
    (exc := [36, 37]) ha (by decide) (by
    intro j hj _ r' hr' w hw
    obtain ⟨c, rfl⟩ := sameLhs_inv hw
    rcases (by simpa using hj : j = 36 ∨ j = 37) with rfl | rfl
    · rw [relRules_of_ruleAt h₃₆ hr']
      exact not_eqNull (fun h => hr (h.1.trans h.2.symm))
    · rw [relRules_of_ruleAt h₃₇ hr']
      exact not_eqTrue hr)
  exact dderives_of_ruleAt h [("ref_1", refToValue r₁), ("ref_2", refToValue r₂)]
    (QuantsOk.cons rfl (ht₁ _ hρ) (QuantsOk.cons rfl (ht₂ _ hρ) QuantsOk.nil)) (by eval_tac)
    (prems_one (.elsePr hel))

end Silmaril.Wasm.SpecTec.Sim.RefsGC
