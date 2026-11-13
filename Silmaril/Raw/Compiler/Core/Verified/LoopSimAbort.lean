module

public import Silmaril.Compiler.Core.Verified.LoopSim.Defs
/-! # Loops by productive macro-steps, ending in a return or a trap

`LoopSim` with one more way for an iteration to end: besides undefined behaviour and the Lir
return, the Lir run may stop with any finished behaviour (`Terminal`: a return or a trap, such
as `abort()`'s control-word store followed by `trap`), with a Core final state that allows every
crt0 observation of it. `LoopSim.Iteration` is one instance (`of_loopSim`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.LoopSimAbort

open Silmaril.Cerberus
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Machine
open Spec
open Sim (UBFrom Final BehFrom AllowedFrom)
open Relation

variable {R : Type} [DecidableEq R]

/-- A finished Lir behaviour: a return or a trap. -/
def Terminal : Lir.Behavior → Prop
  | .returned _ _ => True
  | .trapped _ => True
  | _ => False

theorem Terminal.behaves_pre {p : Lir.Prog R} {s s' : Lir.State R} (path : Lir.Steps p s s') :
    {b : Lir.Behavior} → Terminal b → Lir.Behaves p s' b → Lir.Behaves p s b
  | .returned _ _, _, ⟨t, ht, hf⟩ => ⟨t, path.trans ht, hf⟩
  | .trapped _, _, ⟨t, ht, hf⟩ => ⟨t, path.trans ht, hf⟩

/-- One macro-step from related header states `ts` (Lir) and `cs` (Core). -/
def Iteration (p : Lir.Prog R) (file : Program) (labels : Labels)
    (I : Lir.State R → CState → Prop) (ts : Lir.State R) (cs : CState) : Prop :=
  UBFrom file labels cs ∨
    (∃ ts' cs', TransGen (Lir.Step p) ts ts' ∧ TransGen (coreStep file labels) cs cs' ∧
      I ts' cs') ∨
    ∃ b c, Terminal b ∧ Lir.Behaves p ts b ∧
      ReflTransGen (coreStep file labels) cs c ∧ ∀ o, LirObs b o → Final c o

variable {p : Lir.Prog R} {file : Program} {labels : Labels} {I : Lir.State R → CState → Prop}

theorem of_loopSim {ts : Lir.State R} {cs : CState} (h : LoopSim.Iteration p file labels I ts cs) :
    Iteration p file labels I ts cs := by
  rcases h with ub | step | ⟨t, vs, mem, c, path, ret, core, fin⟩
  · exact .inl ub
  · exact .inr (.inl step)
  · exact .inr (.inr ⟨.returned vs mem, c, trivial, ⟨t, path, ret⟩, core, fin⟩)

/-- A finite chain of iterations, ending in undefined behaviour or a finished Lir run. -/
inductive Ends (p : Lir.Prog R) (file : Program) (labels : Labels) :
    Lir.State R → CState → Prop where
  | ub {ts cs} : UBFrom file labels cs → Ends p file labels ts cs
  | stop {ts cs b c} : Terminal b → Lir.Behaves p ts b →
      ReflTransGen (coreStep file labels) cs c → (∀ o, LirObs b o → Final c o) →
      Ends p file labels ts cs
  | loop {ts cs ts' cs'} : TransGen (Lir.Step p) ts ts' → TransGen (coreStep file labels) cs cs' →
      Ends p file labels ts' cs' → Ends p file labels ts cs

/-- Without a finite chain, the iterations go on forever in both machines. -/
theorem ends_or_diverges (step : ∀ ts cs, I ts cs → Iteration p file labels I ts cs)
    {ts : Lir.State R} {cs : CState} (h : I ts cs) :
    Ends p file labels ts cs ∨ Lir.Diverges p ts ∧ InfiniteTrace (coreStep file labels) cs := by
  by_cases e : Ends p file labels ts cs
  · exact .inl e
  right
  have next : ∀ ts cs, I ts cs → ¬ Ends p file labels ts cs → ∃ ts' cs',
      TransGen (Lir.Step p) ts ts' ∧ TransGen (coreStep file labels) cs cs' ∧ I ts' cs' ∧
        ¬ Ends p file labels ts' cs' := by
    intro ts cs h e
    rcases step ts cs h with ub | ⟨ts', cs', lir, core, h'⟩ | ⟨b, c, term, beh, core, fin⟩
    · exact absurd (.ub ub) e
    · exact ⟨ts', cs', lir, core, h', fun e' => e (.loop lir core e')⟩
    · exact absurd (.stop term beh core fin) e
  constructor
  · refine LoopSim.infinite_of_productive (fun ts => ∃ cs, I ts cs ∧ ¬ Ends p file labels ts cs) ?_
      ⟨cs, h, e⟩
    rintro ts ⟨cs, h, e⟩
    obtain ⟨ts', cs', lir, -, h', e'⟩ := next ts cs h e
    exact ⟨ts', lir, cs', h', e'⟩
  · refine LoopSim.infinite_of_productive (fun cs => ∃ ts, I ts cs ∧ ¬ Ends p file labels ts cs) ?_
      ⟨ts, h, e⟩
    rintro cs ⟨ts, h, e⟩
    obtain ⟨ts', cs', -, core, h', e'⟩ := next ts cs h e
    exact ⟨cs', core, ts', h', e'⟩

theorem Ends.allowed {ts : Lir.State R} {cs : CState} (e : Ends p file labels ts cs) :
    ∀ {b : Lir.Behavior} {o : Obs}, Lir.Behaves p ts b → LirObs b o → AllowedFrom file labels cs o := by
  induction e with
  | ub ub => intro b o _ _; exact .inr (.inl ub)
  | stop _ beh₀ core fin =>
    intro b o beh obs
    have same := Lir.Behaves.unique beh beh₀
    subst same
    exact .inr (.inr (.finite core (fin o obs)))
  | loop lir core _ ih =>
    intro b o beh obs
    exact LoopSim.AllowedFrom.prefix core.to_reflTransGen
      (ih (LoopSim.behaves_of_steps lir.to_reflTransGen beh) obs)

theorem Ends.stuck_ub {ts : Lir.State R} {cs : CState} (e : Ends p file labels ts cs) :
    Lir.Behaves p ts .stuck → UBFrom file labels cs := by
  induction e with
  | ub ub => intro _; exact ub
  | stop term beh₀ _ _ =>
    intro beh
    have same := Lir.Behaves.unique beh beh₀
    subst same
    exact term.elim
  | loop lir core _ ih =>
    intro beh
    exact UBFrom.prefix core.to_reflTransGen (ih (LoopSim.behaves_of_steps lir.to_reflTransGen beh))

/-- **Every Lir behaviour from related header states is allowed by Core.** -/
theorem allowed (step : ∀ ts cs, I ts cs → Iteration p file labels I ts cs)
    {ts : Lir.State R} {cs : CState} (h : I ts cs) {b : Lir.Behavior} {o : Obs}
    (beh : Lir.Behaves p ts b) (obs : LirObs b o) : AllowedFrom file labels cs o := by
  rcases ends_or_diverges step h with e | ⟨d, trace⟩
  · exact e.allowed beh obs
  · cases LoopSim.finite_of_diverges d beh
    change o = .diverges at obs
    subst obs
    exact .inr (.inr (.diverges trace))

/-- **A stuck Lir run from related header states means Core reaches undefined behaviour.** -/
theorem stuck_ub (step : ∀ ts cs, I ts cs → Iteration p file labels I ts cs)
    {ts : Lir.State R} {cs : CState} (h : I ts cs) (beh : Lir.Behaves p ts .stuck) :
    UBFrom file labels cs := by
  rcases ends_or_diverges step h with e | ⟨d, -⟩
  · exact e.stuck_ub beh
  · cases LoopSim.finite_of_diverges d beh

end Silmaril.Compile.Core.Verified.LoopSimAbort
