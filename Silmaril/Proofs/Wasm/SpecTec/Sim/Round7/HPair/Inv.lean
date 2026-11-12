module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HPair.Pair

/-!
# Round 7, `BD`: `LhsNoAtoms msAtoms ∧ LhsNoPair` is a `StepInvH`

* `lhsNoPair_ctx`: `LhsNoPair` passes from the conclusion of a context rule of `Step` (rules 1–5)
  to its `Step` and `Step_read` premises: the conclusion's left-hand side is in `VInv.LFrag`, so
  its variables are bound to `NoPair` values (`vars_of_evalP`), and the premise's is in `LFragP`
  on those variables (`noPair_of_evalP`, kernel fact `step_pairOk`).
* `not_step8`, `not_step9`: rules 8 and 9 derive no `LhsNoPair` value: their left-hand side code
  ends in `REF.FUNC_ADDR a` followed by `CALL_REF yy`.
* `stepInvH_p`: **`Qp := LhsNoAtoms msAtoms ∧ LhsNoPair` is a `HStep.StepInvH`**: no memory SIMD
  instruction in the source, and no `CALL_REF` right after a `REF.FUNC_ADDR`, in any list. Other
  `CALL_REF`s are allowed.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HPair

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round6.Reading (conclAlts)
open VInv (LhsNoAtoms NoAtoms LFrag lvars lhsExp msAtoms)

/-- **The invariant**: no memory SIMD instruction, and no `CALL_REF` right after a
`REF.FUNC_ADDR`, in the left-hand side. -/
def Qp (v : Value) : Prop := LhsNoAtoms msAtoms v ∧ LhsNoPair v

theorem stepPairOk_of {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} (hrel : (simEnv B).findRel? "Step" = some (ps, op, t, rules)) :
    stepPairOk rules = true := by
  have h₁ := VDecl.onRel_of_find stepPairOk hrel
  rw [step_pairOk] at h₁
  exact (Option.some.inj h₁).symm

/-- A `Step`/`Step_read` premise of a context rule has an `LFragP` left-hand side. -/
theorem premP_facts {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {j : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem}
    {y : IL.Id} {args : List Arg} {op'' : MixopS} {e' : Exp}
    (hrel : (simEnv B).findRel? "Step" = some (ps, op, t, rules)) (hj : j ∈ [1, 2, 3, 4, 5])
    (hr : rules[j]? = some (.ruleD nm qs op' e prems)) (hp : Prem.rulePr y args op'' e' ∈ prems)
    (hy : y = "Step" ∨ y = "Step_read") :
    ∃ l', lhsExp e' = some l' ∧ LFragP l' = true := by
  have hok := stepPairOk_of hrel
  simp only [stepPairOk, Bool.and_eq_true, List.all_eq_true] at hok
  have hj' := hok.1.1 j hj
  simp only [hr, List.all_eq_true] at hj'
  have hpr : premPOk (.rulePr y args op'' e') = true := hj' _ hp
  have hy' : (y == "Step" || y == "Step_read") = true := by
    rcases hy with rfl | rfl <;> rfl
  simp only [premPOk, hy', Bool.not_true, Bool.false_or] at hpr
  split at hpr
  · rename_i l' hl'
    exact ⟨l', hl', hpr⟩
  · cases hpr

/-- **`LhsNoPair` passes from a conclusion alternative of a context rule to its `Step` and
`Step_read` premises.** -/
theorem lhsNoPair_ctx {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {j : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e e₁ : Exp}
    {prems : List Prem} {ρ : VarEnv} {v : Value} {y : IL.Id} {args : List Arg} {op'' : MixopS}
    {e' : Exp} {w : Value}
    (hrel : (simEnv B).findRel? "Step" = some (ps, op, t, rules)) (hj : j ∈ [1, 2, 3, 4, 5])
    (hr : rules[j]? = some (.ruleD nm qs op' e prems)) (he₁ : e₁ ∈ conclAlts e)
    (hev : EvalExp (simEnv B) ρ e₁ v) (hv : LhsNoPair v)
    (hp : Prem.rulePr y args op'' e' ∈ prems) (hy : y = "Step" ∨ y = "Step_read")
    (hw : EvalExp (simEnv B) ρ e' w) : LhsNoPair w := by
  obtain ⟨l, hl, hfl, hprems⟩ := VInv.ctx_facts hrel hj hr he₁
  obtain ⟨m, lv, rv, hlv, rfl⟩ := VInv.evalExp_lhs hl hev
  obtain ⟨l₀, r₀, h₀, hn₀⟩ := hv
  have hlv' : NoPair lv := by
    have := (Value.tuple.inj h₀)
    simp only [List.cons.injEq] at this
    exact this.1 ▸ hn₀
  have hvars : VarsP ρ (lvars l) := vars_of_evalP m hlv hfl hlv'
  obtain ⟨l', hl', -, hsub⟩ := VInv.prem_facts (hprems _ hp) hy
  obtain ⟨l'', hl'', hfP⟩ := premP_facts hrel hj hr hp hy
  have hll : l'' = l' := Option.some.inj (hl''.symm.trans hl')
  subst hll
  obtain ⟨m', lw, rw, hlw, rfl⟩ := VInv.evalExp_lhs hl' hw
  exact ⟨lw, rw, rfl, noPair_of_evalP m' hlw hfP fun x hx => hvars x (hsub x hx)⟩

/-- A conclusion `(z; code) ~> rhs` whose code ends in `a`, `b` evaluates to such a pair. -/
theorem eval_lastPair_lhs {env : Env} {ρ : VarEnv} {nm : IL.Id} {qs : List Param} {op : MixopS}
    {e : Exp} {prems : List Prem} {code : Exp} {a b : MixopS} {w : Value}
    (hcode : VElse.readCode (.ruleD nm qs op e prems) = some code)
    (hlast : lastPair code = some (a, b)) (hev : EvalExp env ρ e w) :
    ∃ c zv pre wa wb rv, w = .tuple [.case c (.tuple [zv, .list (pre ++ [.case a wa,
      .case b wb])]), rv] := by
  obtain ⟨c, z, rhs, rfl⟩ := VDecl.readCode_some hcode
  obtain ⟨n, hn⟩ := hev
  obtain ⟨m, v₁, vr, h₁, -, rfl⟩ := VDecl.evalExp_tupE2 hn
  obtain ⟨m', u, hu, rfl⟩ := VDecl.evalExp_caseE h₁
  obtain ⟨k, zv, cv, -, hcv, rfl⟩ := VDecl.evalExp_tupE2 hu
  obtain ⟨cs, rfl, pre, wa, wb, rfl⟩ := evalExp_lastPair k hlast hcv
  exact ⟨c, zv, pre, wa, wb, vr, rfl⟩

/-- A conclusion alternative of a rule all of whose alternatives end in `REF.FUNC_ADDR`,
`CALL_REF` evaluates to no `LhsNoPair` value. -/
theorem not_eval_pair {env : Env} {ρ : VarEnv} {nm : IL.Id} {qs : List Param} {op : MixopS}
    {e e' : Exp} {prems : List Prem} {w : Value}
    (hk : altPairOk (.ruleD nm qs op e prems) "REF.FUNC_ADDR" "CALL_REF" = true)
    (he' : e' ∈ conclAlts e) (hev : EvalExp env ρ e' w) (hw : LhsNoPair w) : False := by
  have hpair : (VElse.readCode (.ruleD nm qs op e' prems)).bind lastPair =
      some ("REF.FUNC_ADDR", "CALL_REF") := by
    have := List.all_eq_true.1 hk e' he'
    simpa only [beq_iff_eq] using this
  obtain ⟨code, hcode, hlast⟩ := Option.bind_eq_some_iff.1 hpair
  obtain ⟨c, zv, pre, wa, wb, rv, rfl⟩ := eval_lastPair_lhs hcode hlast hev
  obtain ⟨l, r', hlr, hl⟩ := hw
  have hl' : l = .case c (.tuple [zv, .list (pre ++ [.case "REF.FUNC_ADDR" wa,
      .case "CALL_REF" wb])]) := by
    have h₂ := Value.tuple.inj hlr
    simp only [List.cons.injEq] at h₂
    exact h₂.1.symm
  have hpf : PairFreeL (pre ++ [.case "REF.FUNC_ADDR" wa, .case "CALL_REF" wb]) := by
    rw [hl'] at hl
    exact hl.2.1.1
  have hne : pairAt (.case "REF.FUNC_ADDR" wa) (.case "CALL_REF" wb) = false := pairFree_last hpf
  simp [pairAt] at hne

/-- Such a rule derives no `LhsNoPair` value. -/
theorem not_ruleBody_pair {B : Builtins} {D : Interp} {els : Prop} {ps : List Param}
    {r : Rule} {args : List ArgV} {op' : MixopS} {w : Value}
    (hk : altPairOk r "REF.FUNC_ADDR" "CALL_REF" = true) (hw : LhsNoPair w) :
    ¬ RuleBody (simEnv B) D els ps args op' r w := by
  intro hb
  obtain ⟨nm, qs, op'', e, prems⟩ := r
  obtain ⟨-, ρ₀, σ, -, -, hev, -⟩ := hb
  exact not_eval_pair hk List.mem_cons_self hev hw

/-- The same under round 6's backend reading. -/
theorem not_ruleBodyB_pair {B : Builtins} {D : Interp} {els : Prop} {ps : List Param}
    {r : Rule} {args : List ArgV} {op' : MixopS} {w : Value}
    (hk : altPairOk r "REF.FUNC_ADDR" "CALL_REF" = true) (hw : LhsNoPair w) :
    ¬ Round6.Reading.RuleBodyB (simEnv B) D els ps args op' r w := by
  intro hb
  obtain ⟨nm, qs, op'', e, prems⟩ := r
  obtain ⟨e', he', -, ρ₀, σ, -, -, hev, -⟩ := hb
  exact not_eval_pair hk he' hev hw

theorem not_step8 {B : Builtins} {D : Interp} {els : Prop} {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {r : Rule} {args : List ArgV} {op' : MixopS}
    {w : Value} (h : (simEnv B).findRel? "Step" = some (ps, op, t, rules))
    (hr : rules[8]? = some r) (hw : LhsNoPair w) : ¬ RuleBody (simEnv B) D els ps args op' r w := by
  have hok := stepPairOk_of h
  simp only [stepPairOk, Bool.and_eq_true, hr] at hok
  exact not_ruleBody_pair hok.1.2 hw

theorem not_step9 {B : Builtins} {D : Interp} {els : Prop} {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {r : Rule} {args : List ArgV} {op' : MixopS}
    {w : Value} (h : (simEnv B).findRel? "Step" = some (ps, op, t, rules))
    (hr : rules[9]? = some r) (hw : LhsNoPair w) : ¬ RuleBody (simEnv B) D els ps args op' r w := by
  have hok := stepPairOk_of h
  simp only [stepPairOk, Bool.and_eq_true, hr] at hok
  exact not_ruleBody_pair hok.2 hw

/-- **`Qp` is a `StepInvH`.** -/
theorem stepInvH_p : HStep.StepInvH Qp where
  inv := VDecl.stepInv_of_lhsAtom (fun _ hw => VInv.lhsNoAtoms_ne hw.1)
    fun _ _ _ _ _ _ _ _ _ e _ _ _ _ _ _ _ _ hrel hj hr hev hv hp hy hw =>
      ⟨VInv.lhsNoAtoms_ctx hrel hj hr (e₁ := e) List.mem_cons_self hev hv.1 hp hy hw,
        lhsNoPair_ctx hrel hj hr (e₁ := e) List.mem_cons_self hev hv.2 hp hy hw⟩
  step8 _ _ _ _ _ _ _ _ _ _ _ hw hrel hr := not_step8 hrel hr hw.2
  step9 _ _ _ _ _ _ _ _ _ _ _ hw hrel hr := not_step9 hrel hr hw.2

theorem pair8 {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {r : Rule} (h : (simEnv B).findRel? "Step" = some (ps, op, t, rules))
    (hr : rules[8]? = some r) : altPairOk r "REF.FUNC_ADDR" "CALL_REF" = true := by
  have hok := stepPairOk_of h
  simp only [stepPairOk, Bool.and_eq_true, hr] at hok
  exact hok.1.2

theorem pair9 {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {r : Rule} (h : (simEnv B).findRel? "Step" = some (ps, op, t, rules))
    (hr : rules[9]? = some r) : altPairOk r "REF.FUNC_ADDR" "CALL_REF" = true := by
  have hok := stepPairOk_of h
  simp only [stepPairOk, Bool.and_eq_true, hr] at hok
  exact hok.2

/-- **`Qp` is a `HCasts.StepInvBH`**, for round 6's backend reading. -/
theorem stepInvBH_p : HCasts.StepInvBH Qp where
  inv :=
    { read43 := fun _ _ _ _ _ _ _ _ _ _ _ hw hrel hr hb =>
        (VInv.lhsNoAtoms_ne hw.1).1 (VDecl.lhsAtom_of_read43B hrel hr hb)
      step23 := fun _ _ _ _ _ _ _ _ _ _ _ hw hrel hr hb =>
        (VInv.lhsNoAtoms_ne hw.1).2 (VInv.lhsAtom_of_step23B hrel hr hb)
      ctx := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrel hj hr he₁ hev hv hp hy hw =>
        ⟨VInv.lhsNoAtoms_ctx hrel hj hr he₁ hev hv.1 hp hy hw,
          lhsNoPair_ctx hrel hj hr he₁ hev hv.2 hp hy hw⟩ }
  step8 _ _ _ _ _ _ _ _ _ _ _ hw hrel hr := not_ruleBodyB_pair (pair8 hrel hr) hw.2
  step9 _ _ _ _ _ _ _ _ _ _ _ hw hrel hr := not_ruleBodyB_pair (pair9 hrel hr) hw.2

end Silmaril.Wasm.SpecTec.Sim.Round7.HPair
