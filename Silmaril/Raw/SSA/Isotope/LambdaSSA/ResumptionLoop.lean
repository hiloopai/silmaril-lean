module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Loop
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ResumptionAdequacy

/-! # Resumable fragments of carried-state while loops

These lemmas expose the actual retained CFG continuation at each loop header.
A single iteration requires only its own test and body evaluations. It does
not assume that the loop eventually exits, so another thread may execute
between any two iterations. Tests and bodies retain all their machine effects.

The runs are derived from the ordinary instruction-resumable machine; no new
operational rule executes an entire loop or region as an indivisible step.
-/

@[expose] public section
universe u v w
namespace Silmaril.Isotope.LambdaSSA.Resumption.While
open Semantics
variable {α : Type u} {Φ : Type v} {σ : Type w}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}

/-- The captured environment and outer continuation stay fixed across polls. -/
def continuation (env : Env α) (condition body : Tm Φ) (outer : RegionCont α Φ) :
    RegionCont α Φ :=
  .cfg env 1 (fun _ => LambdaSSA.While.block condition body) outer

/-- An actual branch to the loop's single internal header, carrying its state. -/
def header (env : Env α) (condition body : Tm Φ) (carry : Value α)
    (outer : RegionCont α Φ) : Control α Φ :=
  .branch 0 carry (continuation env condition body outer)

theorem start {env : Env α} {initial condition body : Tm Φ}
    {before after : σ} {carry : Value α}
    (initialEval : Semantics.Tm.Eval instr env initial before carry after)
    (outer : RegionCont α Φ) :
    Run instr (.region env (LambdaSSA.While.region initial condition body) outer) before
      (header env condition body carry outer) after :=
  .head (.admin .cfg) (region_eval_run (.let₁ initialEval (.br .var)) _)

/-- One continuing iteration returns to the same captured continuation with
the body's actual result and final machine state. -/
theorem next {env : Env α} {condition body : Tm Φ}
    {before tested after : σ} {carry nextCarry : Value α}
    (test : Semantics.Tm.Eval instr (extend env carry) condition before (.inl .unit) tested)
    (bodyEval : Semantics.Tm.Eval instr (extend env carry) body tested nextCarry after)
    (outer : RegionCont α Φ) :
    Run instr (header env condition body carry outer) before
      (header env condition body nextCarry outer) after :=
  .head (.admin (.follow (by decide)))
    (region_eval_run (.case_inl test
      (.let₁ (bodyEval.rename (ρ := Nat.succ) (fun _ => rfl)) (.br .var))) _)

/-- A false test exits this CFG scope and passes its unchanged carry to the
surrounding continuation. The test's actual effects are preserved. -/
theorem done {env : Env α} {condition body : Tm Φ}
    {before after : σ} {carry : Value α}
    (test : Semantics.Tm.Eval instr (extend env carry) condition before (.inr .unit) after)
    (outer : RegionCont α Φ) :
    Run instr (header env condition body carry outer) before
      (.branch 0 carry outer) after :=
  .head (.admin (.follow (by decide)))
    ((region_eval_run (.case_inr test (.br .var)) _).trans
      (.single (.admin (.exit (by decide)))))

end Silmaril.Isotope.LambdaSSA.Resumption.While
