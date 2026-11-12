module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StateVar
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeTags

/-!
# `ref.is_null-false`: the `otherwise` premise, read

`Step_pure` 29 `ref.is_null-false` (`ref REF.IS_NULL ~> CONST I32 0`) has the single premise
`-- otherwise`. Under the declarative reading (which on `Step_pure` is the backend reading,
`Pure.firesB_pure20_iff`) it holds at a left-hand side when none of rules 0–28 fires there:

* rules 0–27 each force a constructor that `ref REF.IS_NULL` lacks (`pureTags20`, by
  `RefsGC.otherwiseAt_of_table`);
* rule 28 `ref.is_null-true` fires exactly when `ref` is `REF.NULL rt` (`null_of_body28`,
  `body28_of_null`).

`refIsNullFalse_iff`: rule 29 fires at the image of `ref.is_null` on `r`, with right-hand side
`w`, iff `r` is not null and `w` is the image of `i32.const 0`, which is `PureStep.refIsNullFalse`
(`refIsNullFalse_step`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.State

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk TypedV RuleBody DDerives otherwise otherwiseAt noElse
  SameLhs evalExp_tup2 evalExp_list1 evalExp_case ruleBody_scope)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (LhsIn TagsIn otherwiseAt_of_table tags_of_take relRules
  ruleTags)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (FiresB)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_idxPayload)
open Silmaril.Wasm.SpecTec.Sim20.Pure (firesB20_inv firesB20_of quant_val prems_one ifPrem
  evalExp_caseNil evalExp_list2 evalExp_pct)

variable (B : Builtins)

set_option maxRecDepth 100000

/-- `Step_pure/ref.is_null-false` is rule 29. -/
theorem hasRuleAt_refIsNullFalse :
    HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 29 refIsNullFalseRule := ⟨_, _, _, rfl, rfl, rfl⟩

/-- The image of `i32.const 0`. -/
abbrev const0V : Value := .case "CONST" (.tuple [caseNilV "I32", pctV 0])

/-- The conclusion of `ref.is_null-false`, evaluated. -/
theorem eval_refIsNullFalse {env : Env} {ρ : VarEnv} {R : Value} (fr : ρ.findVal? "ref" = some R) :
    EvalExp env ρ (Silmaril.Wasm.SpecTec.Sim.Round6.Reading.ruleConcl refIsNullFalseRule)
      (.tuple [.list [R, caseNilV "REF.IS_NULL"], .list [const0V]]) :=
  evalExp_tup2 (evalExp_list2 (evalExp_subE_iff.2 (evalExp_var fr)) evalExp_caseNil)
    (evalExp_list1 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_pct 0))))

/-! ## Rule 28 at `ref REF.IS_NULL` -/

/-- **`ref.is_null-true` fires only at a null reference**, under any reading of its premises. -/
theorem null_of_body28 {env : Env} {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {r : Ref}
    {c : Value} (h : RuleBody env D els [] [] "%~>%" refIsNullTrueRule
      (.tuple [.list [refV r, caseNilV "REF.IS_NULL"], c])) : ∃ t, r = .null t := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope h
  obtain ⟨R, fr⟩ := quant_val (x := "ref") (t := refT) hq (by simp)
  obtain ⟨T, ft⟩ := quant_val (x := "rt") (t := reftypeT) hq (by simp)
  have hu : Value.tuple [.list [refV r, caseNilV "REF.IS_NULL"], c] =
      .tuple [.list [R, caseNilV "REF.IS_NULL"],
        .list [.case "CONST" (.tuple [caseNilV "I32", pctV 1])]] :=
    EvalExp.unique he (eval_refIsNullTrue fr)
  have hR : refV r = R := by
    simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, and_true] at hu
    exact hu.1
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ (List.mem_singleton_self _)))
  have e₁ : v₁ = refV r := EvalExp.unique h₁ (evalExp_var (hR ▸ fr))
  have e₂ : v₂ = .case "REF.NULL" T := EvalExp.unique h₂ (evalExp_case (evalExp_var ft))
  have heq : refV r = .case "REF.NULL" T := e₁ ▸ e₂ ▸ cmpValues_eq_true_iff.1 hc
  obtain ⟨t, ht, -⟩ := null_of_refV heq
  exact ⟨t, ht⟩

/-- `ref.is_null-true` fires at a null reference, under any reading of its premises. -/
theorem body28_of_null {env : Env} {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop}
    {t : V2.RefType} (hr : TypedV env refT (refV (.null t))) (ht : TypedV env reftypeT (refTypeV t)) :
    RuleBody env D els [] [] "%~>%" refIsNullTrueRule
      (.tuple [.list [refV (.null t), caseNilV "REF.IS_NULL"],
        .list [.case "CONST" (.tuple [caseNilV "I32", pctV 1])]]) := by
  let σ : List (IL.Id × Value) := [("ref", refV (.null t)), ("rt", refTypeV t)]
  have fr : (VarEnv.empty.bindVals σ).findVal? "ref" = some (refV (.null t)) := rfl
  have hc : EvalExp env (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.varE "ref") (.caseE "REF.NULL" (.varE "rt"))) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, evalExp_var fr, evalExp_case (evalExp_var rfl),
      cmpValues_eq_true_iff.2 rfl⟩
  exact ⟨rfl, VarEnv.empty, σ, rfl,
    QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (ht _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil), eval_refIsNullTrue fr, prems_one (.ifPr hc)⟩

/-! ## The `otherwise` premise -/

/-- The constructors of `ref REF.IS_NULL`. -/
def refNullTags : List MixopS := ["REF.NULL", "REF.FUNC_ADDR", "REF.HOST_ADDR", "REF.IS_NULL"]

/-- `ref REF.IS_NULL` has its constructors among `refNullTags`. -/
theorem lhsIn_refIsNull (r : Ref) :
    LhsIn refNullTags (.list [refV r, caseNilV "REF.IS_NULL"]) := by
  refine Or.inl ⟨_, rfl, ?_⟩
  intro x hx op w hxw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · cases r <;> simp_all [refV, refNullTags]
  · simp only [caseNilV, Value.case.injEq] at hxw
    simp [← hxw.1, refNullTags]

/-- **`otherwise` holds for rule 29 at a non-null reference.** -/
theorem otherwise_refIsNullFalse {r : Ref} (hnn : ∀ t, r ≠ .null t) (b : Value) :
    otherwise (simEnv20 B) "Step_pure" [] 29 (.tuple [.list [refV r, caseNilV "REF.IS_NULL"], b]) := by
  obtain ⟨ps, t, rules, hrel, rfl, h28⟩ := hasRuleAt_refIsNullTrue B
  have hT : ((relRules (simEnv20 B) "Step_pure").map ruleTags).take 56 = Whole.pureTags20 := by
    rw [Whole.relRules_simEnv20, Whole.pureTags20_eq]
    rfl
  refine otherwiseAt_of_table hrel (tags_of_take hrel hT) (by decide) (lhsIn_refIsNull r)
    (exc := [28]) (by decide) ?_
  intro j hj _ r' hr' w hw
  obtain rfl : j = 28 := List.mem_singleton.1 hj
  rw [h28] at hr'
  obtain rfl := (Option.some.inj hr').symm
  obtain ⟨a', b', c', h₁, rfl⟩ := hw
  have ha : a' = .list [refV r, caseNilV "REF.IS_NULL"] := by
    simp only [Value.tuple.injEq, List.cons.injEq] at h₁
    exact h₁.1.symm
  subst ha
  intro hb
  obtain ⟨t', ht'⟩ := null_of_body28 hb
  exact hnn t' ht'

/-! ## The rule -/

/-- `ref.is_null-false`, read back. -/
theorem refIsNullFalse_inv {r : Ref} {w : Value}
    (hty : ∀ t, r = .null t → TypedV (simEnv20 B) refT (refV r) ∧
      TypedV (simEnv20 B) reftypeT (refTypeV t))
    (hf : FiresB (simEnv20 B) "Step_pure" 29
      (.tuple [.list [refV r, caseNilV "REF.IS_NULL"], w])) :
    (∀ t, r ≠ .null t) ∧ w = .list [const0V] := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_refIsNullFalse B) hf
  obtain ⟨R, fr⟩ := quant_val (x := "ref") (t := refT) hq (by simp)
  have hu : Value.tuple [.list [refV r, caseNilV "REF.IS_NULL"], w] =
      .tuple [.list [R, caseNilV "REF.IS_NULL"], .list [const0V]] :=
    EvalExp.unique he (eval_refIsNullFalse fr)
  have hw : w = .list [const0V] := by
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hu
    exact hu.2
  have hother : otherwiseAt (simEnv20 B) "Step_pure" [] 29
      (.tuple [.list [refV r, caseNilV "REF.IS_NULL"], w]) := by
    cases hp _ (List.mem_singleton_self _) with
    | elsePr h => exact h
  refine ⟨fun t ht => ?_, hw⟩
  obtain ⟨hr, htt⟩ := hty t ht
  obtain ⟨ps, tt, rules, hrel, rfl, h28⟩ := hasRuleAt_refIsNullTrue B
  rw [otherwiseAt] at hother
  subst ht
  exact hother 28 (by decide) [] "%~>%" tt rules refIsNullTrueRule hrel h28 _
    ⟨_, _, _, rfl, rfl⟩ (body28_of_null hr htt)

/-- `ref.is_null-false`, fired. -/
theorem refIsNullFalse_fires {r : Ref} (hnn : ∀ t, r ≠ .null t)
    (hr : TypedV (simEnv20 B) refT (refV r)) :
    FiresB (simEnv20 B) "Step_pure" 29
      (.tuple [.list [refV r, caseNilV "REF.IS_NULL"], .list [const0V]]) :=
  firesB20_of (hasRuleAt_refIsNullFalse B) [("ref", refV r)]
    (QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil) (eval_refIsNullFalse rfl)
    (prems_one (.elsePr (otherwise_refIsNullFalse B hnn _)))

/-- The image of `i32.const 0`. -/
theorem adminsToV_const0 : adminsToV [constI32 0] = [const0V] := rfl

/-- **`Step_pure/ref.is_null-false` is `PureStep.refIsNullFalse`.** -/
theorem refIsNullFalse_iff {r : Ref} (hr : TypedV (simEnv20 B) refT (refV r))
    (ht : ∀ t, r = .null t → TypedV (simEnv20 B) reftypeT (refTypeV t)) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 29 (.tuple [.list (adminsToV [aref r, .plain .refIsNull]), w]) ↔
      (∀ t, r ≠ .null t) ∧ w = .list (adminsToV [constI32 0]) := by
  rw [(adminsToV_refIsNull r).1, adminsToV_const0]
  refine ⟨refIsNullFalse_inv B (fun t h => ⟨hr, ht t h⟩), ?_⟩
  rintro ⟨hnn, rfl⟩
  exact refIsNullFalse_fires B hnn hr

/-- `PureStep.refIsNullFalse` at the same code. -/
theorem refIsNullFalse_step (P : Silmaril.Wasm.Numerics.Profile) {r : Ref}
    (hnn : ∀ t, r ≠ .null t) : PureStep P [aref r, .plain .refIsNull] [constI32 0] :=
  .refIsNullFalse hnn

/-! ## `call` (`Step_read` 2) -/

theorem hasRuleAt_call : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 2 callRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- **`Step_read/call` is `ReadStep.call`**, where the function address is defined. At the
whole-step level the rule is dead (`Whole.deadRead20`): `CALL_ADDR` is not an `instr`. -/
theorem call_iff {H : Type} (hn : H → String) {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
    (ha : f.module.funcs[x.toNat]? = some a)
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f)) (hx : TypedV (simEnv20 B) idxT (idxV x))
    {w : Value} :
    FiresB (simEnv20 B) "Step_read" 2 (.tuple [configV hn ⟨s, f, [.plain (.call x)]⟩, w]) ↔
      w = .list (adminsToV [.callAddr a]) :=
  read1_iff B hn (hasRuleAt_call B) rfl rfl (fun σ fz fx => evalExp_list1 (evalExp_case
    (evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_funcaddr20 B hn rfl (evalExp_var fz),
      evalExp_idxPayload fx, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩))) hz hx

/-- `ReadStep.call` at the same configuration. -/
theorem call_step {H : Type} {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
    (ha : f.module.funcs[x.toNat]? = some a) :
    ReadStep s f [.plain (.call x)] [.callAddr a] :=
  .call (by simpa [ModuleInst.funcAddr?] using ha)

end Silmaril.Wasm.SpecTec.Sim20.State
