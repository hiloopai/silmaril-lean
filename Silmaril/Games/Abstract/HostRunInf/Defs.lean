module

public import Silmaril.Games.Abstract.HostRun.Defs

/-!
# Productive runs against a relational host

`Silmaril.Games.Abstract.HostRun` observes finished behaviours (`AFun`) and pending calls
(`Pending`). Neither can show a **productive** run: one that makes infinitely many answered
import calls. A finite answered log followed by `End.div` would drop those events, and the
set of finite prefixes alone does not determine the run when the function is
nondeterministic (`BodyTrace.union_counterexample`). This module adds them, without changing
the finite API:

* `PInf E S A`: the productive runs of a function, as infinite streams of answered import
  calls, each stream a single coherent run of the function;
* `hostObsInf R q`: the productive runs whose every answer the host `R` allows;
* `hostObsFull R f p q`: the full observation, the finite observations `hostObs R f p` paired
  with the productive ones. For it to observe quiescent divergence, `f` must be a
  divergence-enabled function (one with `End.div` behaviours, such as a `Shape.closeDL`);
* `InfCoherent p q`: every finite prefix of a productive run is a pending prefix of `p`, at
  the run's next call (the projection to the finite observations).
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

/-- **Productive runs**: infinite streams of answered import calls. -/
abbrev PInf (E : Sig.{u}) (S A : Type u) : Type u := S → A → Set (Nat → Call E)

/-- The first `n` calls of a stream. -/
def streamTake {α : Type u} (ω : Nat → α) (n : Nat) : List α := List.ofFn fun i : Fin n => ω i

/-- **Productive runs against a relational host**: every answer allowed. -/
def hostObsInf {E : Sig.{u}} {S A : Type u} (R : HostRel E) (q : PInf E S A) :
    S → A → Set (Nat → Call E) := fun s a =>
  {ω | ω ∈ q s a ∧ ∀ n, R (ω n).1 (.answer (ω n).2)}

/-- **The full observation**: finite observations and productive runs. -/
def hostObsFull {E : Sig.{u}} {S A B : Type u} (R : HostRel E) (f : AFun E S A B)
    (p : Pending E S A) (q : PInf E S A) (s : S) (a : A) :
    Set (HObs E S B) × Set (Nat → Call E) :=
  (hostObs R f p s a, hostObsInf R q s a)

/-- Every finite prefix of a productive run is a pending prefix, at the run's next call. -/
def InfCoherent {E : Sig.{u}} {S A : Type u} (p : Pending E S A) (q : PInf E S A) : Prop :=
  ∀ s a ω, ω ∈ q s a → ∀ n, (streamTake ω n, (ω n).1) ∈ p s a

end Silmaril.Games.Abstract
