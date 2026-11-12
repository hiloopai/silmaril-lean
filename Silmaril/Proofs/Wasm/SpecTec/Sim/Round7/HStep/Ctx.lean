module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HStep.Check

/-!
# Round 7, `BD`: the context rules and rules 8, 9 and 23 of `Step`, and the concrete invariant

* `ctxPremOkH_of`: the premises of `Step` rules 1–5 pass `ctxPremOkH` (from `step_ctxOkH`).
* `lhsAtom_of_step8`, `lhsAtom_of_step9`: rules 8 and 9 fire only on left-hand sides ending in
  `CALL_REF`.
* `stepInvH_of_lhsAtom`: a predicate whose values end in none of `VLOAD`, `VSTORE`, `CALL_REF`,
  and which passes through the context rules, is a `StepInvH`.
* `lhsNoAtomsH_ctx`: `LhsNoAtoms hAtoms` passes through the context rules (`VInv`'s argument with
  the kernel fact `ctx_lhsOkH`). `stepInvH_h`: **`LhsNoAtoms hAtoms` is a `StepInvH`**.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round6.Reading (conclAlts)
open Round7.VDecl (lhsAtom lhsAtom_of_eval altAtom altAtomOk)
open Round7.VInv (LhsNoAtoms NoAtoms LFrag ctxPremLhsOk lhsExp lvars ctxLhsOk)

theorem stepCtxOkH_of {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    (hrel : (simEnv B).findRel? "Step" = some (ps, op, t, rules)) : stepCtxOkH rules = true := by
  have h₁ := VDecl.onRel_of_find stepCtxOkH hrel
  rw [step_ctxOkH] at h₁
  exact (Option.some.inj h₁).symm

/-- **The premises of `Step` rules 1–5 pass `ctxPremOkH`.** -/
theorem ctxPremOkH_of {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {j : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem}
    (hrel : (simEnv B).findRel? "Step" = some (ps, op, t, rules)) (hj : j ∈ [1, 2, 3, 4, 5])
    (hr : rules[j]? = some (.ruleD nm qs op' e prems)) : ∀ pr ∈ prems, ctxPremOkH pr = true := by
  have hok := stepCtxOkH_of hrel
  simp only [stepCtxOkH, Bool.and_eq_true, List.all_eq_true] at hok
  have hj' := hok.1.1.1 j hj
  simp only [hr, List.all_eq_true] at hj'
  exact hj'

/-- A rule whose conclusion alternatives all end in `a` fires only on left-hand sides ending in `a`. -/
theorem lhsAtom_of_stepAt {B : Builtins} {D : Interp} {els : Prop} {ps : List Param}
    {r : Rule} {args : List ArgV} {op' : MixopS}
    {w : Value} {a : MixopS} (hk : altAtomOk r a = true)
    (hb : RuleBody (simEnv B) D els ps args op' r w) :
    lhsAtom w = some a := by
  obtain ⟨nm, qs, op'', e, prems⟩ := r
  obtain ⟨-, ρ₀, σ, -, -, hev, -⟩ := hb
  exact lhsAtom_of_eval (altAtom hk List.mem_cons_self) hev

/-- **Rule 8 of `Step` fires only on left-hand sides ending in `CALL_REF`.** -/
theorem lhsAtom_of_step8 {B : Builtins} {D : Interp} {els : Prop} {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {r : Rule} {args : List ArgV} {op' : MixopS}
    {w : Value} (h : (simEnv B).findRel? "Step" = some (ps, op, t, rules))
    (hr : rules[8]? = some r) (hb : RuleBody (simEnv B) D els ps args op' r w) :
    lhsAtom w = some "CALL_REF" := by
  have hok := stepCtxOkH_of h
  simp only [stepCtxOkH, Bool.and_eq_true, hr] at hok
  exact lhsAtom_of_stepAt hok.1.2 hb

/-- **Rule 9 of `Step` fires only on left-hand sides ending in `CALL_REF`.** -/
theorem lhsAtom_of_step9 {B : Builtins} {D : Interp} {els : Prop} {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {r : Rule} {args : List ArgV} {op' : MixopS}
    {w : Value} (h : (simEnv B).findRel? "Step" = some (ps, op, t, rules))
    (hr : rules[9]? = some r) (hb : RuleBody (simEnv B) D els ps args op' r w) :
    lhsAtom w = some "CALL_REF" := by
  have hok := stepCtxOkH_of h
  simp only [stepCtxOkH, Bool.and_eq_true, hr] at hok
  exact lhsAtom_of_stepAt hok.2 hb

/-! ## `LhsNoAtoms hAtoms` -/

theorem ctxLhsOkH_of {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    (hrel : (simEnv B).findRel? "Step" = some (ps, op, t, rules)) :
    ctxLhsOk hAtoms rules = true := by
  have h₁ := VDecl.onRel_of_find (ctxLhsOk hAtoms) hrel
  rw [ctx_lhsOkH] at h₁
  exact (Option.some.inj h₁).symm

/-- The kernel fact at one context rule and one conclusion alternative. -/
theorem ctx_factsH {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {j : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e e₁ : Exp} {prems : List Prem}
    (hrel : (simEnv B).findRel? "Step" = some (ps, op, t, rules)) (hj : j ∈ [1, 2, 3, 4, 5])
    (hr : rules[j]? = some (.ruleD nm qs op' e prems)) (he₁ : e₁ ∈ conclAlts e) :
    ∃ l, lhsExp e₁ = some l ∧ LFrag hAtoms l = true ∧
      ∀ pr ∈ prems, ctxPremLhsOk hAtoms l pr = true := by
  have hok := ctxLhsOkH_of hrel
  simp only [ctxLhsOk, List.all_eq_true] at hok
  have hj' := hok j hj
  simp only [hr, List.all_eq_true] at hj'
  have h₁ := hj' e₁ he₁
  split at h₁
  · rename_i l hl
    simp only [Bool.and_eq_true, List.all_eq_true] at h₁
    exact ⟨l, hl, h₁.1, h₁.2⟩
  · cases h₁

/-- A `Step`/`Step_read` premise's left-hand side, from `ctxPremLhsOk`. -/
theorem prem_factsH {l : Exp} {y : IL.Id} {args : List Arg} {op : MixopS} {e' : Exp}
    (h : ctxPremLhsOk hAtoms l (.rulePr y args op e') = true) (hy : y = "Step" ∨ y = "Step_read") :
    ∃ l', lhsExp e' = some l' ∧ LFrag hAtoms l' = true ∧ ∀ x ∈ lvars l', x ∈ lvars l := by
  have hy' : (y == "Step" || y == "Step_read") = true := by
    rcases hy with rfl | rfl <;> rfl
  simp only [ctxPremLhsOk, hy', Bool.not_true, Bool.false_or] at h
  split at h
  · rename_i l' hl'
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
    exact ⟨l', hl', h.1, h.2⟩
  · cases h

/-- **`LhsNoAtoms hAtoms` passes from a conclusion alternative of a context rule to its `Step`
and `Step_read` premises.** -/
theorem lhsNoAtomsH_ctx {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {j : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e e₁ : Exp}
    {prems : List Prem} {ρ : VarEnv} {v : Value} {y : IL.Id} {args : List Arg} {op'' : MixopS}
    {e' : Exp} {w : Value}
    (hrel : (simEnv B).findRel? "Step" = some (ps, op, t, rules)) (hj : j ∈ [1, 2, 3, 4, 5])
    (hr : rules[j]? = some (.ruleD nm qs op' e prems)) (he₁ : e₁ ∈ conclAlts e)
    (hev : EvalExp (simEnv B) ρ e₁ v) (hv : LhsNoAtoms hAtoms v)
    (hp : Prem.rulePr y args op'' e' ∈ prems) (hy : y = "Step" ∨ y = "Step_read")
    (hw : EvalExp (simEnv B) ρ e' w) : LhsNoAtoms hAtoms w := by
  obtain ⟨l, hl, hfl, hprems⟩ := ctx_factsH hrel hj hr he₁
  obtain ⟨m, lv, rv, hlv, rfl⟩ := VInv.evalExp_lhs hl hev
  obtain ⟨l₀, r₀, h₀, hn₀⟩ := hv
  have hlv' : NoAtoms hAtoms lv := by
    have := (Value.tuple.inj h₀)
    simp only [List.cons.injEq] at this
    exact this.1 ▸ hn₀
  have hvars := VInv.vars_of_eval m hlv hfl hlv'
  obtain ⟨l', hl', hfl', hsub⟩ := prem_factsH (hprems _ hp) hy
  obtain ⟨m', lw, rw, hlw, rfl⟩ := VInv.evalExp_lhs hl' hw
  exact ⟨lw, rw, rfl, VInv.noAtoms_of_eval m' hlw hfl' fun x hx => hvars x (hsub x hx)⟩

/-- **No memory SIMD instruction and no `CALL_REF` in the left-hand side is a `StepInvH`.** -/
theorem stepInvH_h : StepInvH (LhsNoAtoms hAtoms) where
  inv := VDecl.stepInv_of_lhsAtom
    (fun _ hw => ⟨VInv.lhsAtom_ne_of_noAtoms hw (by decide),
      VInv.lhsAtom_ne_of_noAtoms hw (by decide)⟩)
    fun _ _ _ _ _ _ _ _ _ e _ _ _ _ _ _ _ _ hrel hj hr hev hv hp hy hw =>
      lhsNoAtomsH_ctx hrel hj hr (e₁ := e) List.mem_cons_self hev hv hp hy hw
  step8 _ _ _ _ _ _ _ _ _ _ _ hw hrel hr hb :=
    VInv.lhsAtom_ne_of_noAtoms hw (by decide) (lhsAtom_of_step8 hrel hr hb)
  step9 _ _ _ _ _ _ _ _ _ _ _ hw hrel hr hb :=
    VInv.lhsAtom_ne_of_noAtoms hw (by decide) (lhsAtom_of_step9 hrel hr hb)

end Silmaril.Wasm.SpecTec.Sim.Round7.HStep
