module

public import Silmaril.Machine.CBackend.Behaviour.OfSemantics.Defs
public import Silmaril.Machine.Trace

/-!
# Labelled semantics: runs that emit events

`LSemantics S E V X T F` is a transition relation whose steps emit finite lists
of events (the shape of `Silmaril.Machine.Trace`: one system call, one output
byte, nothing) together with the endings of final states. It is the hook for
process models: a system-call semantics is an `LSemantics` with
`E = Process.Syscall.Event` (`Adapters/Syscall.lean`).

* `observables s`: a finite run with trace `t` to a final state with ending
  `e ≠ diverges` shows `⟨t, e⟩`; a finite run with trace `t` followed by an
  infinite run of silent steps shows `⟨t, diverges⟩`.
* `prefixes s`: the traces of all finite runs, final or not. This is where a
  run that emits infinitely many events is seen (through its prefixes), and
  where safety statements such as `Process.CLI.Agrees` live.

Every `Semantics` is the silent instance (`Semantics.labelled`), with the same
behaviour set (`Semantics.labelled_observables`). The trace refinement of
`Machine.Trace` (a simulation that matches every implementation step by
specification runs with the same events) gives prefix inclusion
(`prefixes_subset_of_trace_refines`) and, when final endings are matched,
refinement of the terminating behaviours (`observables_subset_of_trace_refines`).
-/

@[expose] public section

namespace Silmaril.Machine.Behaviour

open Observable Silmaril.Machine.Trace Relation

/-- A transition relation emitting events, with the endings of final states. -/
structure LSemantics (S E V X T F : Type*) where
  step : S → List E → S → Prop
  final : S → Ending V X T F → Prop

namespace LSemantics

variable {S E V X T F : Type*} (L : LSemantics S E V X T F)

/-- A step that emits nothing. -/
def silent (a b : S) : Prop := L.step a [] b

/-- The behaviour set of a state. -/
def observables (s : S) : Set (Observable E V X T F) :=
  {o | (o.ending ≠ .diverges ∧ ∃ u, Runs L.step s o.trace u ∧ L.final u o.ending) ∨
    (o.ending = .diverges ∧ ∃ u, Runs L.step s o.trace u ∧ InfiniteTrace L.silent u)}

/-- The traces of all finite runs. -/
def prefixes (s : S) : Set (List E) := {t | ∃ u, Runs L.step s t u}

variable {L}

theorem trace_mem_prefixes {s : S} {o : Observable E V X T F} (h : o ∈ L.observables s) :
    o.trace ∈ L.prefixes s := by
  rcases h with ⟨-, u, hu, -⟩ | ⟨-, u, hu, -⟩ <;> exact ⟨u, hu⟩

/-- Prefix-closure of the run traces. -/
theorem prefixes_of_runs_append {s u : S} {t t' : List E} (h₁ : Runs L.step s t u)
    (h₂ : t' ∈ L.prefixes u) : t ++ t' ∈ L.prefixes s := by
  obtain ⟨v, hv⟩ := h₂
  exact ⟨v, h₁.append hv⟩

/-- A finite run is a path of actual transitions. -/
theorem runs_moves {s u : S} {t : List E} (h : Runs L.step s t u) :
    ReflTransGen (Trace.Moves L.step) s u := by
  induction h with
  | refl => exact .refl
  | cons hs _ ih => exact .head ⟨_, hs⟩ ih

/-- A diverging observable is an infinite run (`Machine.Trace.Diverges`). -/
theorem diverges_of_mem {s : S} {t : List E} (h : (⟨t, .diverges⟩ : Observable E V X T F) ∈ L.observables s) :
    Trace.Diverges L.step s := by
  rcases h with ⟨hne, -⟩ | ⟨-, u, hu, hi⟩
  · exact absurd rfl hne
  · exact InfiniteTrace.of_steps (runs_moves hu)
      (InfiniteTrace.map id (fun _ _ h => ⟨[], h⟩) hi)

/-! ## Trace refinement (`Machine.Trace.Refines`) -/

section TraceRefines

variable {S' : Type*} {M : LSemantics S' E V X T F} {Rel : S → S' → Prop}

/-- A trace simulation gives inclusion of the run traces. -/
theorem prefixes_subset_of_trace_refines (h : Trace.Refines L.step M.step Rel) {s : S} {s' : S'}
    (hR : Rel s s') : L.prefixes s ⊆ M.prefixes s' := by
  rintro t ⟨u, hu⟩
  obtain ⟨v, hv, -⟩ := h.runs hu hR
  exact ⟨v, hv⟩

/-- A trace simulation that matches final endings gives refinement of the
terminating behaviours. -/
theorem observables_subset_of_trace_refines (h : Trace.Refines L.step M.step Rel)
    (hfin : ∀ a b e, Rel a b → L.final a e → M.final b e) {s : S} {s' : S'} (hR : Rel s s') :
    {o ∈ L.observables s | o.ending ≠ .diverges} ⊆ M.observables s' := by
  rintro o ⟨(⟨hne, u, hu, hf⟩ | ⟨hd, -⟩), hne'⟩
  · obtain ⟨v, hv, hr⟩ := h.runs hu hR
    exact .inl ⟨hne, v, hv, hfin u v _ hr hf⟩
  · exact absurd hd hne'

end TraceRefines

end LSemantics

/-! ## Every small-step semantics is the silent instance -/

namespace Semantics

variable {S R T F : Type*}

/-- A small-step semantics as a labelled one whose steps emit nothing. -/
def labelled (E : Type*) (sem : Semantics S R T F) : LSemantics S E R Empty T F where
  step a l b := l = [] ∧ sem.step a b
  final s e := sem.final s e.toOutcome

variable {E : Type*} {sem : Semantics S R T F}

theorem labelled_runs_iff {s u : S} {t : List E} :
    Runs (sem.labelled E).step s t u ↔ t = [] ∧ ReflTransGen sem.step s u := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨rfl, .refl⟩
    | cons hs _ ih =>
      obtain ⟨rfl, hs⟩ := hs
      obtain ⟨rfl, ih⟩ := ih
      exact ⟨rfl, .head hs ih⟩
  · rintro ⟨rfl, h⟩
    induction h using ReflTransGen.head_induction_on with
    | refl => exact .refl _
    | head hs _ ih => simpa using Runs.cons (step := (sem.labelled E).step) ⟨rfl, hs⟩ ih

theorem labelled_silent : (sem.labelled E).silent = sem.step := by
  funext a b
  simp [LSemantics.silent, labelled]

/-- The labelled view of a semantics has the same behaviour set. -/
theorem labelled_observables (s : S) :
    (sem.labelled E).observables s = sem.observables s := by
  ext ⟨t, e⟩
  simp only [LSemantics.observables, observables, Set.mem_ofPred_eq, labelled_runs_iff,
    labelled_silent]
  constructor
  · rintro (⟨hne, u, ⟨rfl, hu⟩, hf⟩ | ⟨rfl, u, ⟨rfl, hu⟩, hi⟩)
    · refine ⟨rfl, (beh_of_ne ?_).2 ⟨u, hu, hf⟩⟩
      simpa using hne
    · exact ⟨rfl, InfiniteTrace.of_steps hu hi⟩
  · rintro ⟨rfl, hb⟩
    by_cases hd : e = .diverges
    · subst hd
      exact .inr ⟨rfl, s, ⟨rfl, .refl⟩, hb⟩
    · have hne : e.toOutcome ≠ .diverges := by simpa using hd
      obtain ⟨u, hu, hf⟩ := (beh_of_ne hne).1 hb
      exact .inl ⟨hd, u, ⟨rfl, hu⟩, hf⟩

end Semantics

end Silmaril.Machine.Behaviour
