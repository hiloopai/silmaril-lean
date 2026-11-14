module

public import Silmaril.Games.Abstract.Machine.Defs

/-!
# Contexts, tests and must-observations

**May-testing.** A family of tests `X : Tests G` has a type of contexts and, for
each context `c`, a set of *successful plays* `X.succ c`. The context succeeds
against a trace model `T` when some successful play is a play of `T`
(`Passes`). This is the may-testing reading: a context interacts with the
component and succeeds when *some* joint run reaches success. Contextual
refinement `X.Le T U` and contextual equivalence `X.Equiv T U` quantify over
the contexts of `X`. They are defined by testing, **not** as trace inclusion or
equality.

`X.Separates s` says that some context of `X` succeeds exactly on the models
containing the play `s` (a *definability* property of the context class), and
`X.Complete` asks it of every legal play. `Silmaril.Games.Abstract.Testing.Thms`
proves the following:

* soundness: trace inclusion implies contextual refinement, for any `X`;
* full abstraction under `Complete`: contextual refinement is trace inclusion,
  and contextual equivalence is trace equality;
* observation through a game morphism `f` (`X.through f`): contextual
  equivalence is equality of pulled-back models, which is strictly coarser
  than equality when `f` forgets moves (e.g. startup erasure).

**What may-testing misses.** Finite traces see neither deadlock, divergence
nor refusals. `Machine.Deadlocks`, `Machine.Diverges` and `Machine.Refuses`
(failures) are the must-side observations. Counterexamples in the theorems
show machines with equal traces that differ in each of them, so trace equality
cannot be contextual equivalence for contexts that observe termination,
time-outs or refusals.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

universe u v w

/-- A family of may-tests: contexts, each with its successful plays. -/
structure Tests (G : Game.{u}) : Type (max u (v + 1)) where
  /-- The contexts. -/
  Ctx : Type v
  /-- The plays on which a context succeeds. -/
  succ : Ctx → Set (List G.Move)

namespace Tests

variable {G : Game.{u}}

/-- The context `c` succeeds against `T`: some successful play of `c` is a play
of `T`. -/
def Passes (X : Tests.{u, v} G) (c : X.Ctx) (T : TraceModel G) : Prop := ∃ s ∈ X.succ c, s ∈ T

/-- Contextual refinement: every context that succeeds against `T` succeeds
against `U`. -/
def Le (X : Tests.{u, v} G) (T U : TraceModel G) : Prop := ∀ c, X.Passes c T → X.Passes c U

/-- Contextual equivalence: contextual refinement both ways. -/
def Equiv (X : Tests.{u, v} G) (T U : TraceModel G) : Prop := X.Le T U ∧ X.Le U T

/-- Some context succeeds exactly against the models containing `s`. -/
def Separates (X : Tests.{u, v} G) (s : List G.Move) : Prop :=
  ∃ c, ∀ T : TraceModel G, X.Passes c T ↔ s ∈ T

/-- Definability: every legal play is separated by a context. -/
def Complete (X : Tests.{u, v} G) : Prop := ∀ s ∈ G.Legal, X.Separates s

/-- The single-play tests: one context per legal play, succeeding on it. -/
def single (G : Game.{u}) : Tests.{u, u} G := ⟨{s // s ∈ G.Legal}, fun s => {s.1}⟩

/-- The tests of `X` run against models of `H`, observed through `f`: a context
succeeds on the images of its legal successful plays. -/
def through {H : Game.{w}} (f : G.Hom H) (X : Tests.{u, v} G) : Tests.{w, v} H :=
  ⟨X.Ctx, fun c => {t | ∃ s ∈ X.succ c, s ∈ G.Legal ∧ t = s.map f.map}⟩

end Tests

namespace Machine

variable {G : Game.{u}}

/-- After `s`, the machine can reach a state with no step at all. -/
def Deadlocks (M : Machine G) (s : List G.Move) : Prop :=
  ∃ y, M.Run M.init s y ∧ ∀ l y', ¬ M.step y l y'

/-- After `s`, the machine can reach a state with an infinite run of silent
steps. -/
def Diverges (M : Machine G) (s : List G.Move) : Prop :=
  ∃ y, M.Run M.init s y ∧ ∃ f : Nat → M.State, f 0 = y ∧ ∀ n, M.step (f n) none (f (n + 1))

/-- After `s`, the machine can reach a stable state (no silent step) that
refuses every move of `X`: the failures of the machine. -/
def Refuses (M : Machine G) (s : List G.Move) (X : Set G.Move) : Prop :=
  ∃ y, M.Run M.init s y ∧ (∀ y', ¬ M.step y none y') ∧ ∀ m ∈ X, ∀ y', ¬ M.step y (some m) y'

end Machine

end Silmaril.Games.Abstract
