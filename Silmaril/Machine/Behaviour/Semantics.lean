module

public import Silmaril.Machine.Behaviour.Outcome
public import Silmaril.Foundations.InfiniteTrace.Deterministic

/-!
# Small-step semantics and their behaviours

A `Semantics S R T F` is a transition relation on states `S` together with a
relation `final` saying which outcome a state shows when a run stops there.
`Beh s o` is the set of outcomes of runs from `s`:

* `diverges` exactly when there is an infinite path of actual transitions from
  `s` (`InfiniteTrace`);
* any other `o` when some reachable state is final with outcome `o`.

A stuck state (no transition, no final outcome) contributes no behaviour at all.
In particular it is never divergence (#426): finite prefixes alone cannot
distinguish termination from getting stuck. A semantics that wants a stuck
state to be observable declares it final with outcome `faulted` or
`undefined`. `final s .diverges` is never consulted.

Because a stuck run has no behaviour, a relation that quantifies over target
behaviours (`Refines`, `Implements`, `Refinement`) holds trivially at a target
state all of whose runs get stuck. Such statements are informative only
together with progress of the target: `Progress` for every state, or
`ProgressFrom s` for the states reachable from `s`. `Implements.Nonvacuous`
includes the latter.

`Beh` places no requirement on `final` states: a final state may still step, and
`final` may relate a state to several outcomes. Such a semantics is
nondeterministic. `Deterministic` collects the three conditions under which a
state has at most one behaviour (`Beh.unique`), and `Progress` (or, from one
state, `ProgressFrom`) the condition under which it has at least one
(`Beh.exists`, `Beh.exists_of_progressFrom`). Determinism is assumed only
where a statement says so: `Refines.of_forward`, `Implements.cross` and the
collapse `mutual_divergeToTrap_strict` use it; the definitions of refinement,
implementation and equivalence do not.
-/

@[expose] public section

namespace Silmaril.Machine.Behaviour

open Relation

universe uS uR uT uF

/-- A transition relation with designated final outcomes. -/
structure Semantics (S : Type uS) (R : Type uR) (T : Type uT) (F : Type uF) where
  step : S → S → Prop
  final : S → Outcome R T F → Prop

namespace Semantics

variable {S : Type uS} {R : Type uR} {T : Type uT} {F : Type uF}
variable (sem : Semantics S R T F)

/-- The behaviours of a state. Divergence is an actual infinite path; every
other outcome is shown by a reachable final state. -/
def Beh (s : S) : Outcome R T F → Prop
  | .diverges => InfiniteTrace sem.step s
  | o => ∃ t, ReflTransGen sem.step s t ∧ sem.final t o

/-- A state is safe when undefined behaviour is not among its behaviours. -/
def Safe (s : S) : Prop := ¬ sem.Beh s .undefined

/-- One successor per state, one outcome per final state, and final states do
not step. -/
structure Deterministic : Prop where
  step_unique : Relator.RightUnique sem.step
  final_unique : ∀ s o o', sem.final s o → sem.final s o' → o = o'
  final_stop : ∀ s o, sem.final s o → ∀ t, ¬ sem.step s t

/-- Every state steps or shows a finite outcome. -/
def Progress : Prop := ∀ s, (∃ t, sem.step s t) ∨ ∃ o, sem.final s o ∧ o ≠ .diverges

/-- No state reachable from `s` is stuck: each steps or shows a finite
outcome. Every run from `s` then either reaches a final state or continues
forever. -/
def ProgressFrom (s : S) : Prop :=
  ∀ u, ReflTransGen sem.step s u → (∃ v, sem.step u v) ∨ ∃ o, sem.final u o ∧ o ≠ .diverges

variable {sem}

theorem beh_diverges {s : S} : sem.Beh s .diverges ↔ InfiniteTrace sem.step s := Iff.rfl

theorem beh_of_ne {s : S} {o : Outcome R T F} (h : o ≠ .diverges) :
    sem.Beh s o ↔ ∃ t, ReflTransGen sem.step s t ∧ sem.final t o := by
  cases o <;> first | exact absurd rfl h | exact Iff.rfl

theorem Beh.of_final {s : S} {o : Outcome R T F} (h : sem.final s o) (ho : o ≠ .diverges) :
    sem.Beh s o :=
  (beh_of_ne ho).mpr ⟨s, .refl, h⟩

theorem Beh.of_reach {s t : S} {o : Outcome R T F} (hr : ReflTransGen sem.step s t)
    (h : sem.Beh t o) : sem.Beh s o := by
  by_cases ho : o = .diverges
  · subst ho
    exact InfiniteTrace.of_steps hr h
  · obtain ⟨u, hu, hf⟩ := (beh_of_ne ho).mp h
    exact (beh_of_ne ho).mpr ⟨u, hr.trans hu, hf⟩

theorem Beh.of_step {s t : S} {o : Outcome R T F} (hs : sem.step s t) (h : sem.Beh t o) :
    sem.Beh s o :=
  Beh.of_reach (.single hs) h

/-- The behaviours of a state that cannot step are the outcomes it shows. -/
theorem beh_of_stop {s : S} (hs : ∀ t, ¬ sem.step s t) {o : Outcome R T F} :
    sem.Beh s o ↔ sem.final s o ∧ o ≠ .diverges := by
  by_cases ho : o = .diverges
  · subst ho
    refine ⟨fun h => ?_, fun h => absurd rfl h.2⟩
    obtain ⟨t, ht, -⟩ := h.unfold
    exact absurd ht (hs t)
  · rw [beh_of_ne ho]
    refine ⟨fun ⟨t, ht, hf⟩ => ⟨?_, ho⟩, fun h => ⟨s, .refl, h.1⟩⟩
    rcases ht.cases_head with rfl | ⟨u, hu, -⟩
    · exact hf
    · exact absurd hu (hs u)

/-- A deterministic state has at most one behaviour. -/
theorem Beh.unique (hd : sem.Deterministic) {s : S} {o o' : Outcome R T F}
    (h : sem.Beh s o) (h' : sem.Beh s o') : o = o' := by
  by_cases ho : o = .diverges <;> by_cases ho' : o' = .diverges
  · rw [ho, ho']
  · subst ho
    obtain ⟨t, ht, hf⟩ := (beh_of_ne ho').mp h'
    exact absurd h (RightUnique.not_infinite_of_final hd.step_unique ht (hd.final_stop t o' hf))
  · subst ho'
    obtain ⟨t, ht, hf⟩ := (beh_of_ne ho).mp h
    exact absurd h' (RightUnique.not_infinite_of_final hd.step_unique ht (hd.final_stop t o hf))
  · obtain ⟨t, ht, hf⟩ := (beh_of_ne ho).mp h
    obtain ⟨t', ht', hf'⟩ := (beh_of_ne ho').mp h'
    have := RightUnique.reach_final_eq hd.step_unique ht ht' (hd.final_stop t o hf)
      (hd.final_stop t' o' hf')
    subst this
    exact hd.final_unique t o o' hf hf'

theorem Progress.progressFrom (hp : sem.Progress) (s : S) : sem.ProgressFrom s :=
  fun u _ => hp u

theorem ProgressFrom.of_reach {s t : S} (hp : sem.ProgressFrom s)
    (ht : ReflTransGen sem.step s t) : sem.ProgressFrom t :=
  fun u hu => hp u (ht.trans hu)

/-- A state from which no reachable state is stuck has a behaviour: a run
either stops at a final state or continues forever (classical). -/
theorem Beh.exists_of_progressFrom {s : S} (hp : sem.ProgressFrom s) : ∃ o, sem.Beh s o := by
  classical
  by_cases hstop : ∃ t, ReflTransGen sem.step s t ∧ ∀ u, ¬ sem.step t u
  · obtain ⟨t, ht, hs⟩ := hstop
    rcases hp t ht with ⟨u, hu⟩ | ⟨o, hf, ho⟩
    · exact absurd hu (hs u)
    · exact ⟨o, (beh_of_ne ho).mpr ⟨t, ht, hf⟩⟩
  · refine ⟨.diverges, InfiniteTrace.coinduct (fun t => ReflTransGen sem.step s t) ?_ .refl⟩
    intro t ht
    by_contra hno
    exact hstop ⟨t, ht, fun u hu => hno ⟨u, hu, ht.tail hu⟩⟩

/-- Under progress every state has a behaviour. -/
theorem Beh.exists (hp : sem.Progress) (s : S) : ∃ o, sem.Beh s o :=
  Beh.exists_of_progressFrom (hp.progressFrom s)

/-- In a deterministic semantics a step does not change the behaviours. -/
theorem Beh.step_iff (hd : sem.Deterministic) {s t : S} (hs : sem.step s t)
    {o : Outcome R T F} : sem.Beh s o ↔ sem.Beh t o := by
  refine ⟨fun h => ?_, Beh.of_step hs⟩
  by_cases ho : o = .diverges
  · subst ho
    obtain ⟨u, hu, hi⟩ := h.unfold
    rwa [hd.step_unique hs hu]
  · obtain ⟨u, hu, hf⟩ := (beh_of_ne ho).mp h
    rcases hu.cases_head with rfl | ⟨v, hv, hvu⟩
    · exact absurd hs (hd.final_stop _ o hf t)
    · rw [hd.step_unique hs hv]
      exact (beh_of_ne ho).mpr ⟨u, hvu, hf⟩

end Semantics

end Silmaril.Machine.Behaviour
