module

public import Silmaril.Raw.Semantics.Behaviour.Machine.Behaviour.Refinement
public import Silmaril.Raw.Semantics.Behaviour.Machine.Behaviour.Behaviours

/-!
# Small-step semantics as behaviour sets

`Semantics.observables sem s` is the behaviour set of a state: the
trace-free observables of the outcomes in `sem.Beh s`. The old and the new
notions agree:

* `mem_observables_ofOutcome`: `ofOutcome o ∈ observables sem s ↔ sem.Beh s o`;
* `safe_observables_iff`: the behaviour set is safe iff the state is
  (`Semantics.Safe`);
* `refines_strict_iff_observables`: `Refines ⟨.strict, x⟩ P Q I (Obs.id)`, the
  refinement of `Refinement.lean` at the strict failure mode and the identity
  observation, is `Observable.Refines x` of the behaviour sets of every
  initial pair. Its `Safe` premise becomes undefined behaviour as top, and its
  exhaustion axis is the exhaustion axis of the closure
  (`refines_strict_eq_iff_observables` for `I = Eq`);
* `implements_strict_iff_observables`: the same for the compilation relation
  `Implements`.

The other failure modes (`divergeToTrap`, `trapOrDiverge`) and non-identity
observations relate outcomes of different types; they stay relations on
outcomes (`Outcome.Rel`) and are not behaviour-set inclusions.
-/

@[expose] public section

open Silmaril.Machine.Behaviour

namespace Silmaril.Machine.Behaviour

open Observable

namespace Semantics

variable {S R T F E : Type*} (sem : Semantics S R T F)

/-- The behaviour set of a state of a small-step semantics. Events are of any
type `E`; the semantics emits none. -/
def observables (s : S) : Set (Observable E R Empty T F) :=
  {o | o.trace = [] ∧ sem.Beh s o.ending.toOutcome}

variable {sem}

@[simp] theorem mem_observables_ofOutcome {s : S} {o : Outcome R T F} :
    (Observable.ofOutcome o : Observable E R Empty T F) ∈ observables sem s ↔ sem.Beh s o := by
  simp [observables, Observable.ofOutcome, Observable.ofEnding]

theorem observables_eq_image (s : S) :
    (observables sem s : Set (Observable E R Empty T F)) =
      Observable.ofOutcome '' {o | sem.Beh s o} := by
  ext ⟨t, e⟩
  simp only [observables, Set.mem_ofPred_eq, Set.mem_image, Observable.ofOutcome,
    Observable.ofEnding, Observable.mk.injEq]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨e.toOutcome, h, rfl, Ending.ofOutcome_toOutcome e⟩
  · rintro ⟨o, h, rfl, rfl⟩
    simpa using h

theorem safe_observables_iff {s : S} :
    Observable.Safe (observables sem s : Set (Observable E R Empty T F)) ↔ sem.Safe s := by
  constructor
  · intro h hu
    exact h [] (mem_observables_ofOutcome.2 hu)
  · rintro h t ⟨-, hu⟩
    exact h hu

/-- The strict outcome relation at the identity observation is equality, up
to exhaustion when it is allowed. -/
theorem _root_.Silmaril.Machine.Behaviour.Outcome.rel_strict_id_iff {x : Exhaustion}
    {a b : Outcome R T F} :
    Outcome.Rel ⟨.strict, x⟩ Obs.id a b ↔ a = b ∨ (x = .allowed ∧ a = .exhausted) := by
  cases x <;> cases a <;> cases b <;> simp [Outcome.Rel, Obs.id]

/-- **The old refinement is behaviour-set refinement.** At the strict failure
mode and the identity observation, `Refines` of `Refinement.lean` is
`Observable.Refines` of the behaviour sets, for every initial pair. Its `Safe`
premise becomes undefined behaviour as top, and its exhaustion axis is the
exhaustion axis of the closure. -/
theorem refines_strict_iff_observables {S' : Type*} {P : Semantics S' R T F}
    {Q : Semantics S R T F} {I : S' → S → Prop} {x : Exhaustion} :
    Refines ⟨.strict, x⟩ P Q I (fun _ _ => Obs.id) ↔
      ∀ t s, I t s → Observable.Refines x (observables (E := E) P t) (observables Q s) := by
  constructor
  · intro h t s hI
    by_cases hs : Q.Safe s
    · rintro ⟨tr, e⟩ ⟨rfl, hb⟩
      obtain ⟨o', ho', hr⟩ := h t s hI hs _ hb
      rcases Outcome.rel_strict_id_iff.1 hr with he | ⟨hx, he⟩
      · refine .inl ?_
        have : (⟨[], e⟩ : Observable E R Empty T F) = Observable.ofOutcome o' := by
          simp [Observable.ofOutcome, Observable.ofEnding, ← he]
        rw [this]
        exact mem_observables_ofOutcome.2 ho'
      · refine .inr (.inr ⟨hx, ?_, _, mem_observables_ofOutcome.2 ho', List.nil_prefix⟩)
        exact (Ending.ofOutcome_toOutcome e).symm.trans (congrArg Ending.ofOutcome he)
    · refine refines_of_undefined_nil ?_ _
      exact mem_observables_ofOutcome.2 (not_not.1 hs)
  · rintro h t s hI hs o hb
    rcases h t s hI (mem_observables_ofOutcome.2 hb) with ho | ⟨t', -, hu⟩ | ⟨hx, he, o', ho', -⟩
    · exact ⟨o, mem_observables_ofOutcome.1 ho, Outcome.Rel.refl Obs.isRefl_id _ _⟩
    · exact absurd hu.2 hs
    · refine ⟨_, ho'.2, Outcome.rel_strict_id_iff.2 (.inr ⟨hx, ?_⟩)⟩
      simpa [Observable.ofOutcome, Observable.ofEnding] using he

/-- The identity-relation case: `P ⊑ Q` state by state. -/
theorem refines_strict_eq_iff_observables {P Q : Semantics S R T F} {x : Exhaustion} :
    Refines ⟨.strict, x⟩ P Q Eq (fun _ _ => Obs.id) ↔
      ∀ s, Observable.Refines x (observables (E := E) P s) (observables Q s) := by
  rw [refines_strict_iff_observables]
  exact ⟨fun h s => h s s rfl, fun h t s hts => hts ▸ h t⟩

/-- The compilation relation `Implements` at the strict failure mode and the
identity observation is behaviour-set refinement of every represented target
state by the entry state of its call. -/
theorem implements_strict_iff_observables {S' : Type*} {src : Semantics S R T F}
    {tgt : Semantics S' R T F} {Call : Type*} {entry : Call → S} {Rep : Call → S' → Prop}
    {x : Exhaustion} :
    Implements ⟨.strict, x⟩ src tgt entry Rep (fun _ _ => Obs.id) ↔
      ∀ c t, Rep c t → Observable.Refines x (observables (E := E) tgt t) (observables src (entry c)) := by
  have key : Implements ⟨.strict, x⟩ src tgt entry Rep (fun _ _ => Obs.id) ↔
      Refines ⟨.strict, x⟩ tgt src (fun t s => ∃ c, Rep c t ∧ entry c = s) (fun _ _ => Obs.id) := by
    constructor
    · rintro h t s ⟨c, hc, rfl⟩
      exact h c t hc
    · intro h c t hc
      exact h t (entry c) ⟨c, hc, rfl⟩
  rw [key, refines_strict_iff_observables]
  constructor
  · intro h c t hc
    exact h t _ ⟨c, hc, rfl⟩
  · rintro h t s ⟨c, hc, rfl⟩
    exact h c t hc

end Semantics

end Silmaril.Machine.Behaviour
