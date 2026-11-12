module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VInv.Atoms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VInv.CheckCtx

/-!
# Round 7, memory SIMD: a concrete step invariant

`Q := LhsNoAtoms msAtoms`: the value is a pair whose left-hand side has no memory SIMD instruction
(no `case` of `VLOAD`, `VLOAD_LANE`, `VSTORE` or `VSTORE_LANE`), at any depth. That is
`Round6.MemSimd.NoMemSimd` read on values: code and store function bodies alike.

* `lhsNoAtoms_ctx`: `Q` passes from a conclusion alternative of `Step` rules 1–5 to the value of
  each `Step`/`Step_read` premise. The conclusion's left-hand side is a fragment expression
  (`ctx_lhsOk`), so a `NoAtoms` value of it binds every variable it reads to `NoAtoms` values
  (`vars_of_eval`); the premise's left-hand side is a fragment expression on those variables, so
  it evaluates to a `NoAtoms` value (`noAtoms_of_eval`).
* `lhsAtom_ne_of_noAtoms`: a `Q` value's last instruction has no atom of `msAtoms`, so it ends in
  neither `VLOAD` nor `VSTORE`.
* `stepInv_noMS`: `Q` is a `VDecl.StepInv` (rules 43 and 23 stay silent by
  `VDecl.stepInv_of_lhsAtom`). `stepInvB_noMS`: it is a `StepInvB` too.
* `sstep_withVBytes_iff_noMS`: on such values the whole step `SStep` reads alike at
  `withVBytes B` and at `B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VInv

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round6.Reading (conclAlts RuleBodyB)
open VDecl (lhsAtom codeAtom)

/-- `ctx_lhsOk` at the rules `simEnv B` finds. -/
theorem ctxLhsOk_of {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    (hrel : (simEnv B).findRel? "Step" = some (ps, op, t, rules)) :
    ctxLhsOk msAtoms rules = true := by
  have h₁ := VDecl.onRel_of_find (ctxLhsOk msAtoms) hrel
  rw [ctx_lhsOk] at h₁
  exact (Option.some.inj h₁).symm

theorem lhsExp_some {e l : Exp} (h : lhsExp e = some l) : ∃ r, e = .tupE [l, r] := by
  unfold lhsExp at h
  split at h
  · rename_i l' r
    exact ⟨r, by rw [Option.some.inj h]⟩
  · cases h

/-- The left-hand side of a pair expression evaluates to the left component of the value. -/
theorem evalExp_lhs {env : Env} {ρ : VarEnv} {e l : Exp} {v : Value} (hl : lhsExp e = some l)
    (he : EvalExp env ρ e v) : ∃ m lv rv, evalExp m env ρ l = .ok lv ∧ v = .tuple [lv, rv] := by
  obtain ⟨r, rfl⟩ := lhsExp_some hl
  obtain ⟨n, hn⟩ := he
  obtain ⟨m, lv, rv, h₁, -, rfl⟩ := VDecl.evalExp_tupE2 hn
  exact ⟨m, lv, rv, h₁, rfl⟩

/-- The kernel fact at one context rule and one conclusion alternative. -/
theorem ctx_facts {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {j : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e e₁ : Exp} {prems : List Prem}
    (hrel : (simEnv B).findRel? "Step" = some (ps, op, t, rules)) (hj : j ∈ [1, 2, 3, 4, 5])
    (hr : rules[j]? = some (.ruleD nm qs op' e prems)) (he₁ : e₁ ∈ conclAlts e) :
    ∃ l, lhsExp e₁ = some l ∧ LFrag msAtoms l = true ∧
      ∀ pr ∈ prems, ctxPremLhsOk msAtoms l pr = true := by
  have hok := ctxLhsOk_of hrel
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
theorem prem_facts {l : Exp} {y : IL.Id} {args : List Arg} {op : MixopS} {e' : Exp}
    (h : ctxPremLhsOk msAtoms l (.rulePr y args op e') = true) (hy : y = "Step" ∨ y = "Step_read") :
    ∃ l', lhsExp e' = some l' ∧ LFrag msAtoms l' = true ∧ ∀ x ∈ lvars l', x ∈ lvars l := by
  have hy' : (y == "Step" || y == "Step_read") = true := by
    rcases hy with rfl | rfl <;> rfl
  simp only [ctxPremLhsOk, hy', Bool.not_true, Bool.false_or] at h
  split at h
  · rename_i l' hl'
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
    exact ⟨l', hl', h.1, h.2⟩
  · cases h

/-- **`LhsNoAtoms msAtoms` passes from a conclusion alternative of a context rule to its `Step`
and `Step_read` premises.** -/
theorem lhsNoAtoms_ctx {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {j : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e e₁ : Exp}
    {prems : List Prem} {ρ : VarEnv} {v : Value} {y : IL.Id} {args : List Arg} {op'' : MixopS}
    {e' : Exp} {w : Value}
    (hrel : (simEnv B).findRel? "Step" = some (ps, op, t, rules)) (hj : j ∈ [1, 2, 3, 4, 5])
    (hr : rules[j]? = some (.ruleD nm qs op' e prems)) (he₁ : e₁ ∈ conclAlts e)
    (hev : EvalExp (simEnv B) ρ e₁ v) (hv : LhsNoAtoms msAtoms v)
    (hp : Prem.rulePr y args op'' e' ∈ prems) (hy : y = "Step" ∨ y = "Step_read")
    (hw : EvalExp (simEnv B) ρ e' w) : LhsNoAtoms msAtoms w := by
  obtain ⟨l, hl, hfl, hprems⟩ := ctx_facts hrel hj hr he₁
  obtain ⟨m, lv, rv, hlv, rfl⟩ := evalExp_lhs hl hev
  obtain ⟨l₀, r₀, h₀, hn₀⟩ := hv
  have hlv' : NoAtoms msAtoms lv := by
    have := (Value.tuple.inj h₀)
    simp only [List.cons.injEq] at this
    exact this.1 ▸ hn₀
  have hvars := vars_of_eval m hlv hfl hlv'
  obtain ⟨l', hl', hfl', hsub⟩ := prem_facts (hprems _ hp) hy
  obtain ⟨m', lw, rw, hlw, rfl⟩ := evalExp_lhs hl' hw
  exact ⟨lw, rw, rfl, noAtoms_of_eval m' hlw hfl' fun x hx => hvars x (hsub x hx)⟩

/-- **A `LhsNoAtoms A` value's last instruction has no atom of `A`.** -/
theorem lhsAtom_ne_of_noAtoms {A : List MixopS} {v : Value} {a : MixopS} (hv : LhsNoAtoms A v)
    (ha : a ∈ A) : lhsAtom v ≠ some a := by
  obtain ⟨l, r, rfl, hl⟩ := hv
  intro h
  simp only [lhsAtom] at h
  unfold codeAtom at h
  split at h
  · rename_i b z cs
    split at h
    · rename_i a' w hlast
      obtain rfl := Option.some.inj h
      simp only [NoAtoms, noAtomsL_iff, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hl
      have hm := hl.2.2 _ (List.mem_of_getLast? hlast)
      simp only [NoAtoms] at hm
      exact hm.1 ha
    · cases h
  · cases h

theorem lhsNoAtoms_ne {w : Value} (hw : LhsNoAtoms msAtoms w) :
    lhsAtom w ≠ some "VLOAD" ∧ lhsAtom w ≠ some "VSTORE" :=
  ⟨lhsAtom_ne_of_noAtoms hw (by decide), lhsAtom_ne_of_noAtoms hw (by decide)⟩

/-- **No memory SIMD instruction in the left-hand side is a `VDecl.StepInv`.** -/
theorem stepInv_noMS : VDecl.StepInv (LhsNoAtoms msAtoms) :=
  VDecl.stepInv_of_lhsAtom (fun _ hw => lhsNoAtoms_ne hw)
    fun _ _ _ _ _ _ _ _ _ e _ _ _ _ _ _ _ _ hrel hj hr hev hv hp hy hw =>
      lhsNoAtoms_ctx hrel hj hr (e₁ := e) List.mem_cons_self hev hv hp hy hw

/-- Rule 23 of `Step` fires, under the backend reading, only on left-hand sides ending in
`VSTORE`. -/
theorem lhsAtom_of_step23B {B : Builtins} {D : Interp} {els : Prop} {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {r : Rule} {args : List ArgV} {op' : MixopS}
    {w : Value} (h : (simEnv B).findRel? "Step" = some (ps, op, t, rules))
    (hr : rules[23]? = some r) (hb : RuleBodyB (simEnv B) D els ps args op' r w) :
    lhsAtom w = some "VSTORE" := by
  have hok := VDecl.stepCtxOk_of h
  simp only [VDecl.stepCtxOk, Bool.and_eq_true, hr] at hok
  obtain ⟨nm, qs, op'', e, prems⟩ := r
  obtain ⟨e', he', -, ρ₀, σ, -, -, hev, -⟩ := hb
  exact VDecl.lhsAtom_of_eval (VDecl.altAtom hok.2 he') hev

/-- **No memory SIMD instruction in the left-hand side is a `StepInvB`.** -/
theorem stepInvB_noMS : StepInvB (LhsNoAtoms msAtoms) where
  read43 _ _ _ _ _ _ _ _ _ _ _ hw hrel hr hb :=
    (lhsNoAtoms_ne hw).1 (VDecl.lhsAtom_of_read43B hrel hr hb)
  step23 _ _ _ _ _ _ _ _ _ _ _ hw hrel hr hb :=
    (lhsNoAtoms_ne hw).2 (lhsAtom_of_step23B hrel hr hb)
  ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrel hj hr he₁ hev hv hp hy hw :=
    lhsNoAtoms_ctx hrel hj hr he₁ hev hv hp hy hw

/-- **On values without memory SIMD instructions in the left-hand side, the whole step reads
alike at `withVBytes B` and at `B`.** -/
theorem sstep_withVBytes_iff_noMS (B : Builtins) {c c' : Value}
    (hq : LhsNoAtoms msAtoms (.tuple [c, c'])) :
    SStep (simEnv (MemSimd.withVBytes B)) c c' ↔ SStep (simEnv B) c c' :=
  VDecl.sstep_withVBytes_iff B stepInv_noMS hq

/-- The same, stated on the source alone: `c` has no memory SIMD instruction. -/
theorem sstep_withVBytes_iff_of_noAtoms (B : Builtins) {c c' : Value} (hc : NoAtoms msAtoms c) :
    SStep (simEnv (MemSimd.withVBytes B)) c c' ↔ SStep (simEnv B) c c' :=
  sstep_withVBytes_iff_noMS B ⟨c, c', rfl, hc⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.VInv
