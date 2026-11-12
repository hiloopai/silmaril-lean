module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VDecl.FiresB

/-!
# Round 7, memory SIMD: the context rules of `Step`, and rules 43 and 23

What the whole-step transfer (`Raw/…/Round7/VDecl/Step.lean`) needs of the rules of `Step` and
`Step_read`, from the kernel facts:

* `step_elseFree`: no premise of a `Step` rule contains `otherwise`;
* `readP_of_else`: a rule of `Step_read` with an `otherwise` premise derives only values at which
  its `otherwise` reading moves across (`ReadP`);
* `ctxPremOk_of`: the premises of `Step` rules 1–5 pass `ctxPremOk` (`step_ctxOk`);
* `lhsAtom_of_step23`: rule 23 of `Step` fires only on left-hand sides ending in `VSTORE`;
* `stepInv_of_lhsAtom`: a predicate whose values end in neither `VLOAD` nor `VSTORE` keeps
  rules 43 and 23 silent, so it is a `StepInv` as soon as it passes through the context rules.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VDecl

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round6.Reading (conclAlts)

/-- **No premise of a `Step` rule contains `otherwise`.** -/
theorem step_elseFree {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem}
    (hrel : (simEnv B).findRel? "Step" = some (ps, op, t, rules))
    (hr : rules[i]? = some (.ruleD nm qs op' e prems)) : prems.all elseFree = true := by
  by_contra hf
  have hmem : i ∈ elseFreeIdx rules := mem_elseFreeIdx hr (by simpa using hf)
  have hnil : elseFreeIdx rules = [] := by
    have h₁ := onRel_of_find elseFreeIdx hrel
    rw [step_elseDeep] at h₁
    exact (Option.some.inj h₁).symm
  rw [hnil] at hmem
  exact List.not_mem_nil hmem

/-- **A rule of `Step_read` with an `otherwise` premise derives only `ReadP` values.** -/
theorem readP_of_else {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem}
    {ρ : VarEnv} {v : Value} (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hr : rules[i]? = some (.ruleD nm qs op' e prems)) (hf : prems.all elseFree = false)
    (he : EvalExp (simEnv B) ρ e v) : ReadP i v := by
  by_cases hle : i ≤ 43
  · exact .inl hle
  · have hok := elseAltsOk_read' hrel
    have hj := hok i (mem_elseFreeIdx hr hf)
    simp only [Bool.or_eq_true, decide_eq_true_eq, hr] at hj
    rcases hj with hj | hj
    · omega
    · split at hj
      · rename_i b hb
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hj
        exact .inr (by rw [lhsAtom_of_eval hb he]; exact fun h => hj.1 (Option.some.inj h))
      · cases hj
where
  elseAltsOk_read' {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
      (h : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules)) :
      ∀ j ∈ elseFreeIdx rules, (decide (j ≤ 43) || match rules[j]? with
        | some r => match VElse.ruleAtom r with
            | some b => b != "VLOAD" && altAtomOk r b
            | none => false
        | none => false) = true := by
    have h₁ := onRel_of_find elseAltsOk h
    rw [read_elseAltsOk] at h₁
    have hok : elseAltsOk rules = true := (Option.some.inj h₁).symm
    simp only [elseAltsOk, Bool.and_eq_true, List.all_eq_true] at hok
    exact hok.2

theorem stepCtxOk_of {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    (hrel : (simEnv B).findRel? "Step" = some (ps, op, t, rules)) : stepCtxOk rules = true := by
  have h₁ := onRel_of_find stepCtxOk hrel
  rw [step_ctxOk] at h₁
  exact (Option.some.inj h₁).symm

/-- **The premises of `Step` rules 1–5 pass `ctxPremOk`.** -/
theorem ctxPremOk_of {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {j : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem}
    (hrel : (simEnv B).findRel? "Step" = some (ps, op, t, rules)) (hj : j ∈ [1, 2, 3, 4, 5])
    (hr : rules[j]? = some (.ruleD nm qs op' e prems)) : ∀ pr ∈ prems, ctxPremOk pr = true := by
  have hok := stepCtxOk_of hrel
  simp only [stepCtxOk, Bool.and_eq_true, List.all_eq_true] at hok
  have hj' := hok.1 j hj
  simp only [hr, List.all_eq_true] at hj'
  exact hj'

/-- **Rule 23 of `Step` fires only on left-hand sides ending in `VSTORE`.** -/
theorem lhsAtom_of_step23 {B : Builtins} {D : Interp} {els : Prop} {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {r : Rule} {args : List ArgV} {op' : MixopS}
    {w : Value} (h : (simEnv B).findRel? "Step" = some (ps, op, t, rules))
    (hr : rules[23]? = some r) (hb : RuleBody (simEnv B) D els ps args op' r w) :
    lhsAtom w = some "VSTORE" := by
  have hok := stepCtxOk_of h
  simp only [stepCtxOk, Bool.and_eq_true, hr] at hok
  obtain ⟨nm, qs, op'', e, prems⟩ := r
  obtain ⟨-, ρ₀, σ, -, -, hev, -⟩ := hb
  exact lhsAtom_of_eval (altAtom hok.2 List.mem_cons_self) hev

/-- **A predicate whose values end in neither `VLOAD` nor `VSTORE`, and which passes through the
context rules, is a `StepInv`.** -/
theorem stepInv_of_lhsAtom {Q : Value → Prop}
    (hQ : ∀ w, Q w → lhsAtom w ≠ some "VLOAD" ∧ lhsAtom w ≠ some "VSTORE")
    (hctx : ∀ (B : Builtins) (ps : List Param) (op : MixopS) (t : Typ) (rules : List Rule)
      (j : Nat) (nm : IL.Id) (qs : List Param) (op' : MixopS) (e : Exp) (prems : List Prem)
      (ρ : VarEnv) (v : Value) (y : IL.Id) (args : List Arg) (op'' : MixopS) (e' : Exp)
      (w : Value),
      (simEnv B).findRel? "Step" = some (ps, op, t, rules) → j ∈ [1, 2, 3, 4, 5] →
      rules[j]? = some (.ruleD nm qs op' e prems) → EvalExp (simEnv B) ρ e v → Q v →
      Prem.rulePr y args op'' e' ∈ prems → (y = "Step" ∨ y = "Step_read") →
      EvalExp (simEnv B) ρ e' w → Q w) :
    StepInv Q where
  read43 _ _ _ _ _ _ _ _ _ _ w hw hrel hr hb := (hQ w hw).1 (lhsAtom_of_read43 hrel hr hb)
  step23 _ _ _ _ _ _ _ _ _ _ w hw hrel hr hb := (hQ w hw).2 (lhsAtom_of_step23 hrel hr hb)
  ctx := hctx

end Silmaril.Wasm.SpecTec.Sim.Round7.VDecl
