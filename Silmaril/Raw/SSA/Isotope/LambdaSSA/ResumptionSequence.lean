module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Sequence
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ResumptionAdequacy

/-! # Resuming source sequencing after an interleaved first region

The first region can stop at any instruction and run alongside other threads.
On its actual return, the retained CFG frame enters the second region with the
returned value and original captured environment. Only the second region's
own evaluation is needed to construct its finite continuation fragment.
-/

@[expose] public section
universe u v w
namespace Silmaril.Isotope.LambdaSSA.Resumption.Sequence
open Semantics
variable {α : Type u} {Φ : Type v} {σ : Type w}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}

def continuation (env : Env α) (next : Region Φ) (outer : RegionCont α Φ) : RegionCont α Φ :=
  .cfg env 1 (fun _ => next.renameLabels Nat.succ) outer

theorem start (env : Env α) (first next : Region Φ) (outer : RegionCont α Φ) (state : σ) :
    Run instr (.region env (Region.sequence first next) outer) state
      (.region env first (continuation env next outer)) state := .single (.admin .cfg)

theorem finish {env : Env α} {next : Region Φ} {carry result : Value α}
    {before after : σ} {label : Nat}
    (execution : Semantics.Region.Eval instr (extend env carry) next before label result after)
    (outer : RegionCont α Φ) :
    Run instr (.branch 0 carry (continuation env next outer)) before (.branch label result outer) after := by
  refine .head (.admin (.follow (by decide))) ?_
  exact (region_eval_run (execution.renameLabels Nat.succ) _).trans (.single (.admin (.exit (by omega))))

end Silmaril.Isotope.LambdaSSA.Resumption.Sequence
