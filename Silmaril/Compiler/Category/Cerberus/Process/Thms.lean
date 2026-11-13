module

public import Silmaril.Compiler.Category.Cerberus.Process.Defs
public import Silmaril.Cerberus.Core.Run.Thms
public import Cslib.Foundations.Semantics.LTS.Relation

@[expose] public section
namespace Silmaril.Compiler.Category.Cerberus.Process

open Silmaril.Cerberus
open Silmaril.Cerberus.Core.Dynamics

/-- Erasing labels from genuine finite institution behaviors gives precisely
the source specification's reflexive-transitive reachability relation. -/
theorem finite_iff_reaches (source : Core.Model) (state : State) :
    (∃ actions, source.realises (.finite actions state)) ↔
      Relation.ReflTransGen (Spec.coreStep source.program source.labels)
        source.initialState state := by
  exact (Cslib.LTS.reflTransGen_unlabelledTr_iff
    (lts source.program source.labels)).symm

/-- Actual unlabeled infinite Core traces recover an actual label at every
step. Conversely, an infinite institution behavior erases to that trace. -/
theorem infinite_iff_trace (source : Core.Model) :
    (∃ states actions, source.realises (.infinite states actions)) ↔
      Silmaril.InfiniteTrace (Spec.coreStep source.program source.labels)
        source.initialState := by
  constructor
  · rintro ⟨states, actions, first, steps⟩
    exact ⟨states, first, fun n => ⟨actions n, steps n⟩⟩
  · rintro ⟨states, first, steps⟩
    classical
    choose actions transitions using steps
    exact ⟨states, actions, first, transitions⟩

/-- Recover a genuine labeled finite behavior from the compiler source
specification, and conversely. The source startup is fixed independently of
compiler acceptance and elaborator success. -/
theorem coreReach_iff_realises (document : Codec.Document) (arguments : List String)
    (initial : State) (labels : Labels)
    (start : Spec.coreStart document arguments = .ok (initial, labels)) (state : State) :
    Spec.CoreReach document arguments state ↔
      ∃ actions, (model document initial labels).realises (.finite actions state) := by
  constructor
  · rintro ⟨otherInitial, otherLabels, otherStart, reach⟩
    have same : (otherInitial, otherLabels) = (initial, labels) :=
      Except.ok.inj (otherStart.symm.trans start)
    cases same
    exact (finite_iff_reaches (model document initial labels) state).2 reach
  · intro behavior
    exact ⟨initial, labels, start,
      (finite_iff_reaches (model document initial labels) state).1 behavior⟩

/-- The imported complete process behaviors are exactly the fixed projection
of actual finite/infinite institution behaviors at the same Core startup.
This includes output and abort and does not depend on the Ail elaborator. -/
theorem coreBeh_iff_realises_observes (document : Codec.Document) (arguments : List String)
    (initial : State) (labels : Labels)
    (start : Spec.coreStart document arguments = .ok (initial, labels)) (observation : Spec.Obs) :
    Spec.CoreBeh document arguments observation ↔
      ∃ behavior, (model document initial labels).realises behavior ∧
        Observes behavior observation := by
  constructor
  · show Spec.CoreBeh document arguments observation →
      ∃ behavior, (model document initial labels).realises behavior ∧ Observes behavior observation
    intro behavior
    cases behavior with
    | @exit state value status reach halt allowed =>
      show ∃ behavior, (model document initial labels).realises behavior ∧
        Observes behavior (.exit status (Spec.coreBytes state.memory.stdout))
      obtain ⟨actions, trace⟩ :
          ∃ actions, (model document initial labels).realises (.finite actions state) :=
        (coreReach_iff_realises document arguments initial labels start state).1 reach
      exact ⟨.finite actions state, trace, value, halt, allowed, rfl⟩
    | @abort state reach halt =>
      show ∃ behavior, (model document initial labels).realises behavior ∧
        Observes behavior (.abort (Spec.coreBytes state.memory.stdout))
      obtain ⟨actions, trace⟩ :
          ∃ actions, (model document initial labels).realises (.finite actions state) :=
        (coreReach_iff_realises document arguments initial labels start state).1 reach
      exact ⟨.finite actions state, trace, halt, rfl⟩
    | @diverges otherInitial otherLabels otherStart trace =>
      show ∃ behavior, (model document initial labels).realises behavior ∧
        Observes behavior .diverges
      have same : (otherInitial, otherLabels) = (initial, labels) :=
        Except.ok.inj (otherStart.symm.trans start)
      have initial_eq : otherInitial = initial := congrArg Prod.fst same
      have labels_eq : otherLabels = labels := congrArg Prod.snd same
      have actualTrace : Silmaril.InfiniteTrace (Spec.coreStep document.file labels) initial := by
        simpa only [initial_eq, labels_eq] using trace
      obtain ⟨states, actions, realised⟩ :
          ∃ states actions, (model document initial labels).realises (.infinite states actions) :=
        (infinite_iff_trace (model document initial labels)).2 actualTrace
      exact ⟨.infinite states actions, realised, trivial⟩
  · show (∃ behavior, (model document initial labels).realises behavior ∧
      Observes behavior observation) → Spec.CoreBeh document arguments observation
    rintro ⟨behavior, realises, observed⟩
    cases behavior with
    | finite actions state =>
      show Spec.CoreBeh document arguments observation
      have reach : Spec.CoreReach document arguments state :=
        (coreReach_iff_realises document arguments initial labels start state).2 ⟨actions, realises⟩
      cases observation with
      | exit status stdout =>
        show Spec.CoreBeh document arguments (.exit status stdout)
        obtain ⟨value, halt, allowed, output⟩ :
            ∃ value, state.control = .halt (.defined value) ∧
              Spec.exitStatuses value status ∧ Spec.coreBytes state.memory.stdout = stdout := observed
        have result : Spec.CoreBeh document arguments
            (.exit status (Spec.coreBytes state.memory.stdout)) := .exit reach halt allowed
        simpa only [output] using result
      | abort stdout =>
        show Spec.CoreBeh document arguments (.abort stdout)
        have halt : state.control = .halt .aborted := observed.1
        have output : Spec.coreBytes state.memory.stdout = stdout := observed.2
        have result : Spec.CoreBeh document arguments
            (.abort (Spec.coreBytes state.memory.stdout)) := .abort reach halt
        simpa only [output] using result
      | trap | fault | diverges | exhausted => exact observed.elim
    | infinite states actions =>
      show Spec.CoreBeh document arguments observation
      cases observation with
      | diverges =>
        have trace : Silmaril.InfiniteTrace (Spec.coreStep document.file labels) initial :=
          (infinite_iff_trace (model document initial labels)).1 ⟨states, actions, realises⟩
        exact .diverges start trace
      | exit | abort | trap | fault | exhausted => exact observed.elim

/-- For a successful startup, source UB is precisely a genuine finite
institution behavior ending in UB. Failed startup UB is handled separately by
the imported source specification and cannot be represented by this model. -/
theorem coreUB_iff_realises_ub (document : Codec.Document) (arguments : List String)
    (initial : State) (labels : Labels)
    (start : Spec.coreStart document arguments = .ok (initial, labels)) :
    Spec.CoreUB document arguments ↔
      ∃ actions state location ub,
        (model document initial labels).realises (.finite actions state) ∧
          state.control = .halt (.ub location ub) := by
  constructor
  · rintro (⟨location, ub, failed⟩ | ⟨state, location, ub, reach, halt⟩)
    · rw [start] at failed
      cases failed
    · obtain ⟨actions, trace⟩ :=
        (coreReach_iff_realises document arguments initial labels start state).1 reach
      exact ⟨actions, state, location, ub, trace, halt⟩
  · rintro ⟨actions, state, location, ub, trace, halt⟩
    exact .inr ⟨state, location, ub,
      (coreReach_iff_realises document arguments initial labels start state).2
        ⟨actions, trace⟩, halt⟩

/-- The institution's universal UB safety predicate is exactly absence of
source-specification UB for the same successful Core startup. -/
theorem noUndefinedBehaviour_iff_not_coreUB
    (document : Codec.Document) (arguments : List String) (initial : State) (labels : Labels)
    (start : Spec.coreStart document arguments = .ok (initial, labels)) :
    Core.Satisfies (model document initial labels)
        Silmaril.Cerberus.Institution.noUndefinedBehaviour ↔
      ¬ Spec.CoreUB document arguments := by
  rw [coreUB_iff_realises_ub document arguments initial labels start]
  constructor
  · rintro safe ⟨actions, state, location, ub, trace, halt⟩
    exact safe _ trace location ub halt
  · intro noUB behavior trace
    cases behavior with
    | finite actions state =>
      intro location ub halt
      exact noUB ⟨actions, state, location, ub, trace, halt⟩
    | infinite => trivial

/-- A certified finite runner result witnesses an actual process behavior. This
is existential evidence for the selected schedule, not a universal safety or
compiler-refinement theorem. Output is read from the actual final Core memory. -/
theorem coreBeh_of_run_exit (document : Codec.Document) (arguments : List String)
    (initial : State) (labels : Labels)
    (start : Spec.coreStart document arguments = .ok (initial, labels))
    (fuel : Nat) (value : Val) (status : Nat)
    (ended : (run document.file labels fuel initial).ending = some (.defined value))
    (allowed : Spec.exitStatuses value status) :
    Spec.CoreBeh document arguments
      (.exit status (Spec.coreBytes (run document.file labels fuel initial).finalState.memory.stdout)) := by
  apply (coreBeh_iff_realises_observes document arguments initial labels start _).2
  exact ⟨.finite _ _, run_sound document.file labels fuel initial,
    value, run_ending document.file labels fuel initial (.defined value) ended, allowed, rfl⟩

/-- An actual abort ending is retained as abort, including all preceding output. -/
theorem coreBeh_of_run_abort (document : Codec.Document) (arguments : List String)
    (initial : State) (labels : Labels)
    (start : Spec.coreStart document arguments = .ok (initial, labels))
    (fuel : Nat) (ended : (run document.file labels fuel initial).ending = some .aborted) :
    Spec.CoreBeh document arguments
      (.abort (Spec.coreBytes (run document.file labels fuel initial).finalState.memory.stdout)) := by
  apply (coreBeh_iff_realises_observes document arguments initial labels start _).2
  exact ⟨.finite _ _, run_sound document.file labels fuel initial,
    run_ending document.file labels fuel initial .aborted ended, rfl⟩

/-- Replaying a UB ending witnesses UB in the source process specification.
It cannot be silently classified as a defined return or as fuel exhaustion. -/
theorem coreUB_of_run_undefined (document : Codec.Document) (arguments : List String)
    (initial : State) (labels : Labels)
    (start : Spec.coreStart document arguments = .ok (initial, labels))
    (fuel : Nat) (location : Loc) (undefined : UndefinedBehaviour)
    (ended : (run document.file labels fuel initial).ending = some (.ub location undefined)) :
    Spec.CoreUB document arguments := by
  have reachable : Spec.CoreReach document arguments (run document.file labels fuel initial).finalState :=
    (coreReach_iff_realises document arguments initial labels start _).2
      ⟨_, run_sound document.file labels fuel initial⟩
  exact Or.inr ⟨_, location, undefined, reachable,
    run_ending document.file labels fuel initial (.ub location undefined) ended⟩

end Silmaril.Compiler.Category.Cerberus.Process
