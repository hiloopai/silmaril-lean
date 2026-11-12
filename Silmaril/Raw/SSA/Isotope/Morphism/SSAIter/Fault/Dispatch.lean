module

public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.RegionReflection
public import Silmaril.Raw.SSA.Isotope.Morphism.CaseSSAFault
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Fault.Structural

/-! Faults of finite dispatchers come only from the scrutinee or selected arm. -/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless LetIter.Semantics

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q} {n k : Nat}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {faults : Φ → Value α → σ → σ → Prop} {free : FreeEnv ν α}

theorem fault_underBinder_iff {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)}
    {payload intermediate : Value α} {s s' : σ} :
    Fault instr faults free (extend (extend bound intermediate) payload) body.underBinder s s' ↔
      Fault instr faults free (extend bound payload) body s s' :=
  Fault.rename_iff (Fin.cases rfl (fun _ => rfl))

theorem inject_fault_iff (i : Fin k) {bound : BoundEnv α n} {a : Tm ν Φ n} {s s' : σ} :
    Fault instr faults free bound (inject i a) s s' ↔ Fault instr faults free bound a s s' := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    cases i using Fin.cases with
    | zero =>
      constructor
      · intro h; cases h with | inl h => exact h
      · exact Fault.inl
    | succ j =>
      constructor
      · intro h; cases h with | inr h => exact (ih j).mp h
      · intro h; exact .inr ((ih j).mpr h)

theorem dispatch_fault_arg {bound : BoundEnv α n} {a : Tm ν Φ n}
    {bs : Fin k → Tm ν Φ (n + 1)} {s s' : σ} (h : Fault instr faults free bound a s s') :
    Fault instr faults free bound (dispatch a bs) s s' := by
  cases k with
  | zero => exact .abort_arg h
  | succ k => exact .case_arg h

theorem dispatch_fault_branch (i : Fin k) {bound : BoundEnv α n} {a : Tm ν Φ n}
    {bs : Fin k → Tm ν Φ (n + 1)} {s mid s' : σ} {payload : Value α}
    (arg : Eval instr free bound a s (tagValue i payload) mid)
    (body : Fault instr faults free (extend bound payload) (bs i) mid s') :
    Fault instr faults free bound (dispatch a bs) s s' := by
  induction k generalizing n s with
  | zero => exact i.elim0
  | succ k ih =>
    cases i using Fin.cases with
    | zero => exact .case_inl arg body
    | succ i =>
      exact .case_inr arg (ih i .bv (fault_underBinder_iff.mpr body))

theorem dispatch_fault_iff {bound : BoundEnv α n} {a : Tm ν Φ n}
    {bs : Fin k → Tm ν Φ (n + 1)} {s s' : σ} :
    Fault instr faults free bound (dispatch a bs) s s' ↔
      Fault instr faults free bound a s s' ∨
      ∃ (i : Fin k) (payload : Value α) (mid : σ),
        Eval instr free bound a s (tagValue i payload) mid ∧
        Fault instr faults free (extend bound payload) (bs i) mid s' := by
  constructor
  · intro h
    induction k generalizing n s with
    | zero => cases h with | abort_arg h => exact .inl h
    | succ k ih =>
      cases h with
      | case_arg h => exact .inl h
      | case_inl arg body => exact .inr ⟨0, _, _, arg, body⟩
      | case_inr arg body =>
        rcases ih body with bad | ⟨i, payload, mid, lookup, chosen⟩
        · cases bad
        · cases lookup
          exact .inr ⟨i.succ, payload, _, arg, fault_underBinder_iff.mp chosen⟩
  · rintro (arg | ⟨i, payload, mid, arg, body⟩)
    · exact dispatch_fault_arg arg
    · exact dispatch_fault_branch i arg body

variable {free : FreeEnv Empty α}

theorem emitCFG_fault_iff {count labels : Nat} (i : Fin (count + labels))
    {bound : BoundEnv α n} {a : Tm Empty Φ n} {s s' : σ} :
    Fault instr faults free bound (emitCFG i a) s s' ↔ Fault instr faults free bound a s s' := by
  cases i using Fin.addCases with
  | left i =>
    simp only [emitCFG, Fin.addCases_left]
    constructor
    · intro h; cases h with | inr h => exact (inject_fault_iff i).mp h
    · intro h; exact .inr ((inject_fault_iff i).mpr h)
  | right i =>
    simp only [emitCFG, Fin.addCases_right]
    constructor
    · intro h; cases h with | inl h => exact (inject_fault_iff i).mp h
    · intro h; exact .inl ((inject_fault_iff i).mpr h)

theorem encodeExpr_fault_iff {arg : LambdaSSA.Tm Φ} (scope : arg.Scoped n)
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n} {s s' : σ}
    (agree : CaseSSA.EnvAgrees env bound) :
    Fault instr faults free bound (encodeExpr arg scope) s s' ↔
      LambdaSSA.Semantics.Tm.Fault instr faults env arg s s' :=
  CaseSSA.ofScoped_fault_iff scope agree

end Silmaril.Isotope.Morphism.SSAIter
