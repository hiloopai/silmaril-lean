module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdPureStep.Refs

/-!
# Track bwd-pure-step: `ref.eq`, backward (`Step_pure` 36–38)

`ref.eq-null` reads its premise back; `ref.eq-true` refutes a null pair with `ref.eq-null`;
`ref.eq-false` refutes an equal pair with `ref.eq-null` (null) or `ref.eq-true` (non-null), the
latter's own `otherwise` by family R's opcode criterion.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdPureStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.SpecTec.Equiv.ExecRef
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-- The premise of `ref.eq-null`, read back. -/
theorem eqNull_of_prem {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {r₁ r₂ : Ref}
    (f₁ : ρ.findVal? "ref_1" = some (refToValue r₁)) (f₂ : ρ.findVal? "ref_2" = some (refToValue r₂))
    (h : PremW env D els ρ (.ifPr (.binE .andOp .boolT
      (.cmpE .eqOp .boolT (.varE "ref_1") (.caseE "REF.NULL_ADDR" (.tupE [])))
      (.cmpE .eqOp .boolT (.varE "ref_2") (.caseE "REF.NULL_ADDR" (.tupE [])))))) :
    r₁ = .null ∧ r₂ = .null := by
  have hn : EvalExp env ρ (.caseE "REF.NULL_ADDR" (.tupE [])) (.case "REF.NULL_ADDR" (.tuple [])) :=
    by beval
  have hb := EvalExp.unique (RefsGC.premW_if h)
    (RefsGC.evalExp_and (RefsGC.evalExp_eq (evalExp_var f₁) hn) (RefsGC.evalExp_eq (evalExp_var f₂) hn))
  simp only [Value.bool.injEq, Bool.true_eq, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact ⟨RefsGC.eq_null_of_refToValue hb.1, RefsGC.eq_null_of_refToValue hb.2⟩

/-- The premise of `ref.eq-null`, at two null references. -/
theorem eqNull_prem {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv}
    (f₁ : ρ.findVal? "ref_1" = some (refToValue .null))
    (f₂ : ρ.findVal? "ref_2" = some (refToValue .null)) :
    ∀ pr ∈ [Prem.ifPr (.binE .andOp .boolT
      (.cmpE .eqOp .boolT (.varE "ref_1") (.caseE "REF.NULL_ADDR" (.tupE [])))
      (.cmpE .eqOp .boolT (.varE "ref_2") (.caseE "REF.NULL_ADDR" (.tupE []))))],
      PremW env D els ρ pr := by
  intro pr hpr
  rw [List.mem_singleton.1 hpr]
  exact .ifPr (RefsGC.evalExp_and_true (RefsGC.evalExp_eq_true (evalExp_var f₁) (by beval))
    (RefsGC.evalExp_eq_true (evalExp_var f₂) (by beval)))

section Bwd

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H} (B : Builtins)
variable {s : Store H} {f : Frame} {is : List Admin} {w : Value}

/-- `Backward.pure 36` (`ref.eq-null`). -/
theorem bwd_eqNull (hf : Fires (simEnv B) "Step_pure" 36 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, a₃, rfl, hq, h₁, h₂, h₃, hr, hp⟩ := fires_three (simEnv_refRules B).refEqNull hf
  obtain ⟨r₁, rfl, f₁⟩ := ref_of_var hq (.head _) h₁
  obtain ⟨r₂, rfl, f₂⟩ := ref_of_var hq (.tail _ (.head _)) h₂
  obtain rfl := head_refEq (head_of_caseE h₃)
  obtain ⟨rfl, rfl⟩ := eqNull_of_prem f₁ f₂ (hp _ (List.mem_singleton_self _))
  exact ⟨[constI32 1], EvalExp.unique hr (by beval), .reference .eqNull⟩

/-- `Backward.pure 37` (`ref.eq-true`). -/
theorem bwd_eqTrue (hf : Fires (simEnv B) "Step_pure" 37 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, a₃, rfl, hq, h₁, h₂, h₃, hr, hp⟩ := fires_three (simEnv_refRules B).refEqTrue hf
  obtain ⟨r₁, rfl, f₁⟩ := ref_of_var hq (.head _) h₁
  obtain ⟨r₂, rfl, f₂⟩ := ref_of_var hq (.tail _ (.head _)) h₂
  obtain rfl := head_refEq (head_of_caseE h₃)
  have he : refToValue r₁ = refToValue r₂ :=
    RefsGC.eq_of_evalExp_eq (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
      (evalExp_var f₁) (evalExp_var f₂)
  obtain rfl := Equiv.RuntimeBridge.refToValue_inj he
  refine ⟨[constI32 1], EvalExp.unique hr (by beval), .reference (.eqTrue fun hn => ?_)⟩
  subst hn
  have ho : otherwise (simEnv B) "Step_pure" [] 37
      (.tuple [.list (adminsToV [.ref .null, .ref .null, .plain .refEq]), w]) := by
    cases hp _ (List.mem_cons_self) with
    | elsePr h => exact h
  exact otherwise_false ho (by decide) (simEnv_refRules B).refEqNull ⟨_, _, _, rfl, rfl⟩
    ⟨rfl, VarEnv.empty, σ, rfl, hq, by beval, eqNull_prem f₁ f₂⟩

/-- `ref.eq-true`'s `otherwise`, at two equal non-null references (family R's criterion). -/
theorem eqTrue_otherwise {r : Ref} (hr : r ≠ .null) :
    otherwise (simEnv B) "Step_pure" [] 37
      (.tuple [.list (adminsToV [.ref r, .ref r, .plain .refEq]), .list (adminsToV [constI32 1])]) := by
  have ha : RefsGC.LhsIn (["REF.EQ"] ++ RefsGC.valTags) (.list (adminsToV [.ref r, .ref r, .plain .refEq])) :=
    .inl ⟨_, rfl, RefsGC.tagsIn_cons (RefsGC.tag_ref (RefsGC.refTags_sub _) r)
      (RefsGC.tagsIn_cons (RefsGC.tag_ref (RefsGC.refTags_sub _) r)
        (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide)) RefsGC.tagsIn_nil))⟩
  exact RefsGC.otherwise_of_ruleAt (simEnv_refRules B).refEqTrue (RefsGC.pureTable_simEnv B)
    (i := 37) (by decide) (exc := [36]) ha (by decide) (by
    intro j hj _ r' hr' w hw
    obtain rfl : j = 36 := by simpa using hj
    rw [RefsGC.relRules_of_ruleAt (simEnv_refRules B).refEqNull hr']
    obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
    exact RefsGC.not_eqNull (fun h => hr h.1))

/-- `Backward.pure 38` (`ref.eq-false`). -/
theorem bwd_eqFalse (hf : Fires (simEnv B) "Step_pure" 38 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, a₃, rfl, hq, h₁, h₂, h₃, hr, hp⟩ := fires_three (simEnv_refRules B).refEqFalse hf
  obtain ⟨r₁, rfl, f₁⟩ := ref_of_var hq (.head _) h₁
  obtain ⟨r₂, rfl, f₂⟩ := ref_of_var hq (.tail _ (.head _)) h₂
  obtain rfl := head_refEq (head_of_caseE h₃)
  have ho := else_of_prems hp
  refine ⟨[constI32 0], EvalExp.unique hr (by beval), .reference (.eqFalse fun he => ?_)⟩
  subst he
  by_cases hn : r₁ = .null
  · subst hn
    exact otherwise_false ho (by decide) (simEnv_refRules B).refEqNull ⟨_, _, _, rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, hq, by beval, eqNull_prem f₁ f₂⟩
  · refine otherwise_false ho (by decide) (simEnv_refRules B).refEqTrue ⟨_, _, _, rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, hq, by beval, fun pr hpr => ?_⟩
    rcases List.mem_cons.1 hpr with rfl | hpr
    · exact .elsePr (eqTrue_otherwise B hn)
    · rw [List.mem_singleton.1 hpr]
      exact .ifPr (RefsGC.evalExp_eq_true (evalExp_var f₁) (evalExp_var f₂))

end Bwd

end Silmaril.Wasm.SpecTec.Sim.BwdPureStep
