module

public import Silmaril.Games.Abstract.Testing.Defs
public import Silmaril.Games.Abstract.Game.Thms
import Silmaril.Proofs.Games.Abstract.Testing.Basic
import Silmaril.Proofs.Games.Abstract.Testing.Counterexample

/-!
# Contexts, tests and must-observations: theorems

**When trace equality is contextual equivalence.** For may-testing contexts
(`Tests`):

* trace inclusion always implies contextual refinement (`Tests.le_of_le`):
  soundness needs no hypothesis;
* if the context class separates every legal play (`Tests.Complete`, a
  definability hypothesis), contextual refinement *is* trace inclusion and
  contextual equivalence *is* trace equality (`Tests.le_iff_of_complete`,
  `Tests.equiv_iff_of_complete`); the single-play tests are complete
  (`Tests.single_complete`);
* contexts that only observe through a game morphism `f` identify exactly the
  models with equal pullbacks (`Tests.equiv_through_iff`), which is coarser
  than trace equality whenever `comap f` is not injective.

**When it is not.** Contexts that observe deadlock, divergence or refusals
distinguish trace-equal machines:

* `exists_traces_eq_refusal`: `a.b + a` against the deterministic `a.b`.
  After `a`, the first may deadlock and refuse `b`; the second cannot.
* `exists_traces_eq_divergence`: deadlock after `a` against silent divergence
  after `a`.

For such contexts (time-outs, termination detection, must-testing),
contextual equivalence needs failures and divergences, not finite traces.
-/

public section

namespace Silmaril.Games.Abstract

universe u v w

namespace Tests

variable {G : Game.{u}}

/-- Trace inclusion implies contextual refinement. -/
theorem le_of_le (X : Tests.{u, v} G) {T U : TraceModel G} (h : T ≤ U) : X.Le T U :=
  Silmaril.Proofs.Games.Abstract.Testing.le_of_le X h

/-- Equal models are contextually equivalent. -/
theorem equiv_of_eq (X : Tests.{u, v} G) {T U : TraceModel G} (h : T = U) : X.Equiv T U :=
  ⟨X.le_of_le h.le, X.le_of_le h.ge⟩

/-- **Full abstraction under definability**: if every legal play is separated
by a context, contextual refinement is trace inclusion. -/
theorem le_iff_of_complete {X : Tests.{u, v} G} (hX : X.Complete) {T U : TraceModel G} :
    X.Le T U ↔ T ≤ U :=
  Silmaril.Proofs.Games.Abstract.Testing.le_iff_of_complete hX

/-- **Full abstraction under definability**: contextual equivalence is trace
equality. -/
theorem equiv_iff_of_complete {X : Tests.{u, v} G} (hX : X.Complete) {T U : TraceModel G} :
    X.Equiv T U ↔ T = U :=
  Silmaril.Proofs.Games.Abstract.Testing.equiv_iff_of_complete hX

/-- The single-play tests separate every legal play. -/
theorem single_complete : (Tests.single G).Complete :=
  Silmaril.Proofs.Games.Abstract.Testing.single_complete

variable {H : Game.{w}}

/-- A test observed through `f` passes when it passes on the pullback. -/
theorem passes_through_iff {X : Tests.{u, v} G} (f : G.Hom H) (c : X.Ctx) (T : TraceModel H) :
    (X.through f).Passes c T ↔ X.Passes c (TraceModel.comap f T) :=
  Silmaril.Proofs.Games.Abstract.Testing.passes_through_iff f c T

/-- Contexts observing through `f` identify exactly the models with equal
pullbacks. -/
theorem equiv_through_iff {X : Tests.{u, v} G} (hX : X.Complete) (f : G.Hom H)
    {T U : TraceModel H} :
    (X.through f).Equiv T U ↔ TraceModel.comap f T = TraceModel.comap f U :=
  Silmaril.Proofs.Games.Abstract.Testing.equiv_through_iff hX f

end Tests

namespace Machine

/-- Equal traces do not determine refusals or deadlocks, even against a
deterministic machine. -/
theorem exists_traces_eq_refusal :
    ∃ (G : Game.{0}) (M N : Machine G) (s : List G.Move) (X : Set G.Move),
      M.traces = N.traces ∧ N.LDet ∧ M.Refuses s X ∧ ¬ N.Refuses s X ∧
      M.Deadlocks s ∧ ¬ N.Deadlocks s :=
  Silmaril.Proofs.Games.Abstract.Testing.Counterexample.refusal_counterexample

/-- Equal traces do not distinguish deadlock from silent divergence. -/
theorem exists_traces_eq_divergence :
    ∃ (G : Game.{0}) (M N : Machine G) (s : List G.Move),
      M.traces = N.traces ∧ M.Deadlocks s ∧ ¬ N.Deadlocks s ∧ N.Diverges s ∧ ¬ M.Diverges s :=
  Silmaril.Proofs.Games.Abstract.Testing.Counterexample.divergence_counterexample

end Machine

end Silmaril.Games.Abstract
