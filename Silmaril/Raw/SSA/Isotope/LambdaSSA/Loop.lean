module

public import Silmaril.SSA.Isotope.LambdaSSA.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
public import Silmaril.Raw.SSA.Isotope.SequentialTrace

/-! # Reusable static iterations and carried-state CFG loops

The signature, runtime values and machine state are arbitrary. Each body
evaluation retains its real effects. The CFG uses pure variable branch
arguments so a completed loop can be composed with later source phases.
-/

@[expose] public section
universe u v w x
namespace Silmaril.Isotope.LambdaSSA

namespace Tm
variable {Φ : Type u}

/-- Statically expanded iterations; body `i` receives the previous result at
slot zero, followed by the original captured environment. -/
def iterate (body : Nat → Tm Φ) (initial : Tm Φ) : Nat → Tm Φ
  | 0 => initial
  | count + 1 => .let₁ (iterate body initial count) (body count)

theorem HasType.iterate {τ : Type v} [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]
    {Γ : VCtx τ} {A : τ} {body : Nat → Tm Φ} {initial : Tm Φ} (count : Nat)
    (start : HasType Γ initial A) (step : ∀ i < count, HasType (A :: Γ) (body i) A) :
    HasType Γ (iterate body initial count) A := by
  induction count with
  | zero => exact start
  | succ count ih => exact .let₁ (ih (fun i hi => step i (by omega))) (step count (by omega))

end Tm

namespace Semantics.Tm.Eval
variable {Φ : Type u} {α : Type v} {σ : Type w}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}

theorem iterate {env : Env α} {body : Nat → LambdaSSA.Tm Φ} {initial : LambdaSSA.Tm Φ}
    (count : Nat) (value : Nat → Value α) (state : Nat → σ) {before : σ}
    (start : Tm.Eval instr env initial before (value 0) (state 0))
    (step : ∀ i < count, Tm.Eval instr (extend env (value i)) (body i)
      (state i) (value (i + 1)) (state (i + 1))) :
    Tm.Eval instr env (LambdaSSA.Tm.iterate body initial count) before (value count) (state count) := by
  induction count with
  | zero => exact start
  | succ count ih => exact .let₁ (ih (fun i hi => step i (by omega))) (step count (by omega))

theorem iterate_of_trace {env : Env α} {body : Nat → LambdaSSA.Tm Φ} {initial : LambdaSSA.Tm Φ}
    (count : Nat) (value : Nat → Value α) {before middle after : σ}
    (start : Tm.Eval instr env initial before (value 0) middle)
    (trace : SequentialTrace (fun index a b =>
      Tm.Eval instr (extend env (value index)) (body index) a (value (index + 1)) b)
      (List.range count) middle after) :
    Tm.Eval instr env (LambdaSSA.Tm.iterate body initial count) before (value count) after := by
  obtain ⟨state, first, last, steps⟩ := trace.range_states
  have initialEval : Tm.Eval instr env initial before (value 0) (state 0) := first.symm ▸ start
  exact last ▸ iterate count value state initialEval steps

end Semantics.Tm.Eval

namespace While
variable {Φ : Type u}

def block (condition body : Tm Φ) : Region Φ :=
  .case condition (.let₁ (body.rename Nat.succ) (.br 0 (.var 0))) (.br 1 (.var 1))

def region (initial condition body : Tm Φ) : Region Φ :=
  .cfg (.let₁ initial (.br 0 (.var 0))) 1 (fun _ => block condition body)

theorem block_typed {τ : Type v} [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]
    {Γ : VCtx τ} {A : τ} {condition body : Tm Φ}
    (test : Tm.HasType (A :: Γ) condition (Silmaril.coprod Silmaril.unit Silmaril.unit))
    (step : Tm.HasType (A :: Γ) body A) :
    Region.HasType (A :: Γ) (block condition body) [A, A] :=
  .case test (.let₁ (step.weaken Silmaril.unit) (.br rfl (.var rfl))) (.br rfl (.var rfl))

theorem region_typed {τ : Type v} [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]
    {Γ : VCtx τ} {A : τ} {initial condition body : Tm Φ}
    (start : Tm.HasType Γ initial A)
    (test : Tm.HasType (A :: Γ) condition (Silmaril.coprod Silmaril.unit Silmaril.unit))
    (step : Tm.HasType (A :: Γ) body A) :
    Region.HasType Γ (region initial condition body) [A] := by
  apply Region.HasType.cfg (fun _ => A)
  · exact .let₁ start (.br rfl (.var rfl))
  · intro i
    exact block_typed test step

open Semantics (extend)
variable {α : Type v} {σ : Type w}

/-- A finite while execution contains the actual test and body transitions,
including the final failed condition. Tests need not be effect-free. -/
inductive Trace (instr : Φ → Value α → σ → Value α → σ → Prop)
    (env : Semantics.Env α) (condition body : Tm Φ) : Value α → σ → Value α → σ → Prop where
  | done {value before after}
      (test : Semantics.Tm.Eval instr (extend env value) condition before (.inr .unit) after) :
      Trace instr env condition body value before value after
  | next {value before tested next middle result after}
      (test : Semantics.Tm.Eval instr (extend env value) condition before (.inl .unit) tested)
      (step : Semantics.Tm.Eval instr (extend env value) body tested next middle)
      (tail : Trace instr env condition body next middle result after) :
      Trace instr env condition body value before result after

theorem follow_of_trace {instr : Φ → Value α → σ → Value α → σ → Prop}
    {env : Semantics.Env α} {condition body : Tm Φ} {value result : Value α} {before after : σ}
    (trace : Trace instr env condition body value before result after) :
    Semantics.Region.Follow instr env (fun _ : Fin 1 => block condition body) 0 value before 0 result after := by
  induction trace with
  | done test => exact .step (by decide) (.case_inr test (.br .var)) (.exit (by decide))
  | next test step _ ih =>
    exact .step (by decide) (.case_inl test (.let₁ (step.rename (ρ := Nat.succ) (fun _ => rfl)) (.br .var))) ih

theorem region_eval {instr : Φ → Value α → σ → Value α → σ → Prop}
    {env : Semantics.Env α} {initial condition body : Tm Φ} {value result : Value α}
    {before middle after : σ}
    (start : Semantics.Tm.Eval instr env initial before value middle)
    (trace : Trace instr env condition body value middle result after) :
    Semantics.Region.Eval instr env (region initial condition body) before 0 result after :=
  .cfg (.let₁ start (.br .var)) (follow_of_trace trace)

end While
end Silmaril.Isotope.LambdaSSA
