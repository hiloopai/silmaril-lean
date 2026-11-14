module

public import Silmaril.Games.Abstract.Outcome.Defs
public import Silmaril.Games.Abstract.Machine.Thms
import Silmaril.Proofs.Games.Abstract.Outcome.Basic
import Silmaril.Proofs.Games.Abstract.Outcome.Examples

/-!
# Outcome-tagged traces: theorems

**Erasure.** The `run` tag is exactly the trace (`fin_run_mem_iff`), and every
tagged finite observation's trace is a trace (`mem_traces_of_fin`). The three
equivalences form a chain, with inclusions monotone along it:

```
  obs M ⊆ obs N  →  cobs M ⊆ cobs N  →  traces M ⊆ traces N
  TagEquiv       ⇒  CoarseEquiv       ⇒  TraceEquiv
```

(`cobs_mono`, `traces_subset_of_cobs`, `TagEquiv.coarse`, `CoarseEquiv.trace`).

**Exactly what the trap ≈ divergence quotient forgets.** `collapse` identifies
two observations iff they are equal or both are a trap or a divergence after
the same trace (`collapse_eq_iff`). So `coarseEquiv_iff`: two machines are
coarse-equivalent iff they have the same non-abort observations (prefixes,
returns with results, waiting, deadlock, infinite runs) and, for every trace
`s`, one aborts after `s` exactly when the other does. Startup and the trace
before the abort are kept.

**Neither converse holds** (examples in
`Silmaril.Proofs.Games.Abstract.Outcome.Examples`):

* `exists_coarse_not_tag`: trap after `a` against a silent loop after `a`;
* `exists_startup_coarse_not_tag` and `exists_startup_trap_distinct`: trap
  and divergence during startup are coarse-equivalent, but a trap during
  startup is not coarse-equivalent to a trap after `ready`;
* the trace-only collapse is coarser again (`Silmaril.Games.Abstract.Machine.exists_traces_eq_divergence`);
* `exists_prefix_not_div`: a prefix observation is not a divergence;
* `exists_unfair_div`: a machine that may loop silently or exit has a `div`
  observation; it is not coarse-equivalent to one that returns at once,
  although a fair scheduler would identify them. Fair testing is not modelled;
* `exists_wait_not_div_stuck`, `exists_stuck`: quiescence (waiting for the
  environment) is neither divergence nor deadlock.

**Contexts.** For a class of tests over observations and a map `κ` (`id` for
tagged, `collapse` for coarse):

* soundness: if every context's success set is a union of `κ`-fibres
  (`Saturated`), equal `κ`-images give may-equivalence (`may_sound`) and,
  when completeness of an observation respects `κ`, must-equivalence
  (`must_sound`);
* completeness: if every `κ`-class is detected by a context (`Separates`),
  may-equivalence gives equal `κ`-images (`may_complete`);
* hence `mayEquiv_iff_tag` and `mayEquiv_iff_coarse`.

So the trap ≈ divergence equivalence is the contextual (may) equivalence of
exactly those context classes that cannot tell a trap from a divergence at the
same trace and can detect every coarse class. Contexts that observe
termination with a time-out (separating trap from divergence) are not
saturated for `collapse`. A context class that cannot see some other
distinction (a return value, a wait) is not separating. In either case
coarse equivalence and the contextual equivalence differ. Agreement with any
*existing* contextual equivalence therefore has to be checked against these
two hypotheses for its contexts; it does not follow from the collapse alone.
Must-testing is determined by the complete (non-`run`) observations, and
divergence is unfair: both are explicit choices, not defaults.
-/

public section

namespace Silmaril.Games.Abstract

universe u

namespace OMachine

variable {G : Game.{u}} {R : Type u} {M N : OMachine G R}

/-- The `run` observations are the traces. -/
theorem fin_run_mem_iff {s : List G.Move} : Obs.fin s .run ∈ M.obs ↔ s ∈ M.traces :=
  Silmaril.Proofs.Games.Abstract.Outcome.fin_run_mem_iff

/-- Every tagged finite observation's trace is a trace. -/
theorem mem_traces_of_fin {s : List G.Move} {t : Tag R} (h : Obs.fin s t ∈ M.obs) :
    s ∈ M.traces :=
  Silmaril.Proofs.Games.Abstract.Outcome.mem_traces_of_fin h

/-- The fibres of `collapse`. -/
theorem collapse_eq_iff {o o' : Obs G R} :
    o.collapse = o'.collapse ↔ o = o' ∨ ∃ s, o.IsAbortAt s ∧ o'.IsAbortAt s :=
  Silmaril.Proofs.Games.Abstract.Outcome.collapse_eq_iff

/-- Tagged inclusion implies coarse inclusion. -/
theorem cobs_mono (h : M.obs ⊆ N.obs) : M.cobs ⊆ N.cobs :=
  Silmaril.Proofs.Games.Abstract.Outcome.cobs_mono h

/-- Coarse inclusion implies trace inclusion. -/
theorem traces_subset_of_cobs (h : M.cobs ⊆ N.cobs) : M.traces ⊆ N.traces :=
  Silmaril.Proofs.Games.Abstract.Outcome.traces_subset_of_cobs h

/-- Tagged equivalence implies coarse equivalence. -/
theorem TagEquiv.coarse (h : M.TagEquiv N) : M.CoarseEquiv N := by
  unfold CoarseEquiv cobs; rw [h]

/-- Coarse equivalence implies trace equivalence. -/
theorem CoarseEquiv.trace (h : M.CoarseEquiv N) : M.TraceEquiv N :=
  Set.Subset.antisymm (traces_subset_of_cobs h.le) (traces_subset_of_cobs h.ge)

/-- Exactly what coarse equivalence identifies. -/
theorem coarseEquiv_iff :
    M.CoarseEquiv N ↔ (∀ o, (∀ s, ¬ o.IsAbortAt s) → (o ∈ M.obs ↔ o ∈ N.obs)) ∧
      ∀ s, (Obs.fin s .trap ∈ M.obs ∨ Obs.fin s .div ∈ M.obs ↔
        Obs.fin s .trap ∈ N.obs ∨ Obs.fin s .div ∈ N.obs) :=
  Silmaril.Proofs.Games.Abstract.Outcome.coarseEquiv_iff

end OMachine

namespace ObsTests

variable {α β : Type u}

/-- Saturated contexts cannot tell apart sets with equal `κ`-images (may). -/
theorem may_sound {X : ObsTests α} {κ : α → β} (hX : X.Saturated κ) {A B : Set α}
    (h : κ '' A = κ '' B) : X.MayEquiv A B :=
  Silmaril.Proofs.Games.Abstract.Outcome.may_sound hX h

/-- Saturated contexts cannot tell apart sets with equal `κ`-images (must). -/
theorem must_sound {X : ObsTests α} {κ : α → β} {complete : α → Prop} (hX : X.Saturated κ)
    (hc : ∀ o o', κ o = κ o' → (complete o ↔ complete o')) {A B : Set α}
    (h : κ '' A = κ '' B) : X.MustEquiv complete A B :=
  Silmaril.Proofs.Games.Abstract.Outcome.must_sound hX hc h

/-- Separating contexts distinguish sets with different `κ`-images (may). -/
theorem may_complete {X : ObsTests α} {κ : α → β} (hX : X.Separates κ) {A B : Set α}
    (h : X.MayEquiv A B) : κ '' A = κ '' B :=
  Silmaril.Proofs.Games.Abstract.Outcome.may_complete hX h

variable {G : Game.{u}} {R : Type u}

/-- Contexts that detect every tagged observation: may-equivalence is tagged
equivalence. -/
theorem mayEquiv_iff_tag {X : ObsTests (Obs G R)} (hX : X.Separates id) {M N : OMachine G R} :
    X.MayEquiv M.obs N.obs ↔ M.TagEquiv N := by
  refine ⟨fun h => by simpa [OMachine.TagEquiv] using may_complete hX h, fun h => ?_⟩
  exact may_sound (κ := id) (fun _ _ _ h => by simp only [id] at h; rw [h]) (by rw [h])

/-- Contexts that cannot tell a trap from a divergence at the same trace, and
detect every coarse class: may-equivalence is trap ≈ divergence equivalence. -/
theorem mayEquiv_iff_coarse {X : ObsTests (Obs G R)} (hs : X.Saturated Obs.collapse)
    (hX : X.Separates Obs.collapse) {M N : OMachine G R} :
    X.MayEquiv M.obs N.obs ↔ M.CoarseEquiv N :=
  ⟨may_complete hX, may_sound hs⟩

end ObsTests

namespace OMachine

open Silmaril.Proofs.Games.Abstract.Outcome.Examples in
/-- Trap after an event and a silent loop after it: coarse-equivalent, not
tagged-equivalent. -/
theorem exists_coarse_not_tag :
    ∃ (G : Game.{0}) (M N : OMachine G Unit), M.CoarseEquiv N ∧ ¬ M.TagEquiv N :=
  ⟨Gx, trapA, loopA, trapA_loopA_coarse, trapA_loopA_not_tag⟩

open Silmaril.Proofs.Games.Abstract.Outcome.Examples in
/-- Trap and divergence during startup: coarse-equivalent, not tagged-equivalent. -/
theorem exists_startup_coarse_not_tag :
    ∃ (G : Game.{0}) (M N : OMachine G Unit), M.CoarseEquiv N ∧ ¬ M.TagEquiv N :=
  ⟨Gx, trapS, loopS, trapS_loopS_coarse, trapS_loopS_not_tag⟩

open Silmaril.Proofs.Games.Abstract.Outcome.Examples in
/-- A trap during startup and a trap after `ready` are not coarse-equivalent. -/
theorem exists_startup_trap_distinct :
    ∃ (G : Game.{0}) (M N : OMachine G Unit), ¬ M.CoarseEquiv N :=
  ⟨Gx, trapS, readyTrap, trapS_not_coarse_readyTrap⟩

open Silmaril.Proofs.Games.Abstract.Outcome.Examples in
/-- A prefix observation is not a divergence. -/
theorem exists_prefix_not_div :
    ∃ (G : Game.{0}) (M : OMachine G Unit) (s : List G.Move),
      Obs.fin s .run ∈ M.obs ∧ Obs.fin s .div ∉ M.obs :=
  ⟨Gx, trapA, _, trapA_prefix_not_div⟩

open Silmaril.Proofs.Games.Abstract.Outcome.Examples in
/-- Divergence is unfair: a loop that may exit is observed. -/
theorem exists_unfair_div :
    ∃ (G : Game.{0}) (M N : OMachine G Unit),
      Obs.fin [] .div ∈ M.obs ∧ Obs.fin [] (.ret ()) ∈ M.obs ∧ ¬ M.CoarseEquiv N :=
  ⟨Gx, exitLoop, retM, exitLoop_obs.1, exitLoop_obs.2, exitLoop_not_coarse_retM⟩

open Silmaril.Proofs.Games.Abstract.Outcome.Examples in
/-- Waiting for the environment is neither divergence nor deadlock. -/
theorem exists_wait_not_div_stuck :
    ∃ (G : Game.{0}) (M : OMachine G Unit),
      Obs.fin [] .wait ∈ M.obs ∧ Obs.fin [] .div ∉ M.obs ∧ Obs.fin [] .stuck ∉ M.obs :=
  ⟨Gx, waitM, waitM_obs⟩

open Silmaril.Proofs.Games.Abstract.Outcome.Examples in
/-- A deadlocked machine. -/
theorem exists_stuck : ∃ (G : Game.{0}) (M : OMachine G Unit), Obs.fin [] .stuck ∈ M.obs :=
  ⟨Gx, stuckM, stuckM_obs⟩

end OMachine

end Silmaril.Games.Abstract
