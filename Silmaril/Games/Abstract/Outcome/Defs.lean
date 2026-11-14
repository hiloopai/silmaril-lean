module

public import Silmaril.Games.Abstract.Machine.Defs

/-!
# Outcome-tagged traces: trap, divergence, return, waiting, deadlock

Finite traces alone do not say how a run ended (`Silmaril.Games.Abstract.Testing`:
equal traces, different deadlock and divergence). This module tags each finite
trace with what the run did *at its end*, and adds infinite productive runs.

An `OMachine G R` is a machine together with its terminal states: `Ret x r`
(the run completed normally with result `r`, for example returned values or an
uncaught exception) and `Trap x` (the run trapped). An observation is one of:

| observation | meaning |
|---|---|
| `fin s .run` | `s` is a finite prefix of some run; the run may still be going. This is *only* a prefix, not a claim that the run stops or diverges. |
| `fin s (.ret r)` | after `s` the run completed normally with `r` |
| `fin s .trap` | after `s` the run trapped |
| `fin s .div` | after `s` the run reached a state with an infinite run of silent steps: silent divergence *after* the events `s` (before any event when `s = []`) |
| `fin s .wait` | after `s` the run is quiescent: not terminal, no silent step, no own move, but some environment move is possible. It is blocked waiting for the environment, which is not divergence |
| `fin s .stuck` | after `s` the run reached a non-terminal state with no step at all (deadlock) |
| `inf ω` | an infinite *productive* run performing the infinite sequence of moves `ω` |

Two equivalences of machines, both *defined* here as observational
equivalences (neither is claimed to coincide with some other contextual
equivalence without the hypotheses of `Silmaril.Games.Abstract.Outcome.Thms`):

* **tagged** (`TagEquiv`): equal observation sets, so trap and divergence are
  distinguished;
* **trap ≈ divergence** (`CoarseEquiv`): equal images under `collapse`, which
  merges the tags `trap` and `div` into `abort` and keeps everything else,
  including the trace prefix at which the abort happened and therefore
  whether it happened during startup or after (startup moves are moves).

Plain trace equality (`traces`) is the coarsest of the three.

Divergence here is any infinite silent run, with no fairness assumption: a
machine that may loop silently forever *or* exit has a `div` observation,
although a fair scheduler would never take the infinite branch.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

universe u

/-- A machine with terminal states: normal completion with a result, and trap. -/
structure OMachine (G : Game.{u}) (R : Type u) extends Machine G where
  /-- `Ret x r`: the run completed normally with result `r`. -/
  Ret : State → R → Prop
  /-- `Trap x`: the run trapped. -/
  Trap : State → Prop

/-- How a finite run ended, or that it is just a prefix. -/
inductive Tag (R : Type u) : Type u
  /-- A prefix of a run, possibly still going. -/
  | run
  /-- Normal completion with a result. -/
  | ret (r : R)
  /-- A trap. -/
  | trap
  /-- Silent divergence. -/
  | div
  /-- Quiescent, waiting for the environment. -/
  | wait
  /-- Deadlock: no step at all, not terminal. -/
  | stuck

/-- Tags with trap and divergence merged into `abort`. -/
inductive CTag (R : Type u) : Type u
  | run
  | ret (r : R)
  | abort
  | wait
  | stuck

/-- Merge trap and divergence. -/
def Tag.collapse {R : Type u} : Tag R → CTag R
  | .run => .run
  | .ret r => .ret r
  | .trap => .abort
  | .div => .abort
  | .wait => .wait
  | .stuck => .stuck

/-- An observation: a tagged finite trace, or an infinite productive trace. -/
inductive Obs (G : Game.{u}) (R : Type u) : Type u
  | fin (s : List G.Move) (t : Tag R)
  | inf (ω : Nat → G.Move)

/-- A coarse observation: trap and divergence merged. -/
inductive CObs (G : Game.{u}) (R : Type u) : Type u
  | fin (s : List G.Move) (t : CTag R)
  | inf (ω : Nat → G.Move)

/-- Merge trap and divergence in an observation, keeping its trace. -/
def Obs.collapse {G : Game.{u}} {R : Type u} : Obs G R → CObs G R
  | .fin s t => .fin s t.collapse
  | .inf ω => .inf ω

/-- A trap or a divergence after `s`: the observations that `collapse` merges. -/
def Obs.IsAbortAt {G : Game.{u}} {R : Type u} (s : List G.Move) (o : Obs G R) : Prop :=
  o = .fin s .trap ∨ o = .fin s .div

namespace OMachine

variable {G : Game.{u}} {R : Type u} (M : OMachine G R)

/-- A terminal state. -/
def Terminal (x : M.State) : Prop := (∃ r, M.Ret x r) ∨ M.Trap x

/-- `x` has an infinite run of silent steps. -/
def DivergesFrom (x : M.State) : Prop :=
  ∃ f : Nat → M.State, f 0 = x ∧ ∀ n, M.step (f n) none (f (n + 1))

/-- What a state reached after `s` shows. -/
def Shows (x : M.State) : Tag R → Prop
  | .run => True
  | .ret r => M.Ret x r
  | .trap => M.Trap x
  | .div => M.DivergesFrom x
  | .wait => ¬ M.Terminal x ∧ (∀ y, ¬ M.step x none y) ∧
      (∀ m y, M.step x (some m) y → G.IsO m) ∧ ∃ m y, M.step x (some m) y
  | .stuck => ¬ M.Terminal x ∧ ∀ l y, ¬ M.step x l y

/-- `M` can make the observation. -/
inductive Observes : Obs G R → Prop
  /-- A run over `s` reaching a state that shows `t`. -/
  | fin {s : List G.Move} {t : Tag R} (y : M.State) :
      M.Run M.init s y → M.Shows y t → Observes (.fin s t)
  /-- An infinite run performing the moves `ω`. -/
  | inf {ω : Nat → G.Move} (x : Nat → M.State) :
      x 0 = M.init → (∀ n, M.Run (x n) [ω n] (x (n + 1))) → Observes (.inf ω)

/-- The observations of `M`. -/
def obs : Set (Obs G R) := {o | M.Observes o}

/-- The coarse observations: trap and divergence merged. -/
def cobs : Set (CObs G R) := Obs.collapse '' M.obs

/-- Tagged equivalence: equal observations. -/
def TagEquiv (M N : OMachine G R) : Prop := M.obs = N.obs

/-- Trap ≈ divergence equivalence: equal coarse observations. -/
def CoarseEquiv (M N : OMachine G R) : Prop := M.cobs = N.cobs

/-- Trace equivalence. -/
def TraceEquiv (M N : OMachine G R) : Prop := M.traces = N.traces

end OMachine

/-- May- and must-tests over observations of type `α`: each context succeeds on
a set of observations. -/
structure ObsTests (α : Type u) : Type (u + 1) where
  /-- The contexts. -/
  Ctx : Type u
  /-- The observations on which a context succeeds. -/
  succ : Ctx → Set α

namespace ObsTests

variable {α : Type u}

/-- May-testing: some observation succeeds. -/
def MayPass (X : ObsTests α) (c : X.Ctx) (A : Set α) : Prop := ∃ o ∈ A, o ∈ X.succ c

/-- Must-testing: every *complete* observation succeeds (`complete` selects
the observations that end a run, e.g. everything but `run` prefixes). -/
def MustPass (X : ObsTests α) (complete : α → Prop) (c : X.Ctx) (A : Set α) : Prop :=
  ∀ o ∈ A, complete o → o ∈ X.succ c

/-- May-equivalence. -/
def MayEquiv (X : ObsTests α) (A B : Set α) : Prop := ∀ c, X.MayPass c A ↔ X.MayPass c B

/-- Must-equivalence. -/
def MustEquiv (X : ObsTests α) (complete : α → Prop) (A B : Set α) : Prop :=
  ∀ c, X.MustPass complete c A ↔ X.MustPass complete c B

/-- Every context's success set is a union of fibres of `κ`: the contexts
cannot tell apart observations with the same `κ`-image (for `κ = collapse`:
they cannot tell a trap from a divergence at the same trace). -/
def Saturated {β : Type u} (X : ObsTests α) (κ : α → β) : Prop :=
  ∀ c o o', κ o = κ o' → (o ∈ X.succ c ↔ o' ∈ X.succ c)

/-- Every fibre of `κ` is detected by some may-context: the contexts can
observe every `κ`-class (for `κ = id`: every tagged observation, so they can
observe termination and tell a trap from a divergence). -/
def Separates {β : Type u} (X : ObsTests α) (κ : α → β) : Prop :=
  ∀ b, ∃ c, ∀ o, o ∈ X.succ c ↔ κ o = b

end ObsTests

end Silmaril.Games.Abstract
