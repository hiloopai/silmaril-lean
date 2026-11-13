module

public import Silmaril.Compiler.C.Sem.Basic.Defs
public import Silmaril.Machine.CBackend.Behaviour.Behaviours.Defs
/-!
# Adapter: process observations of the C semantics (`Compile.C.Sem.Obs`)

The C rungs (`C0` … `C7`) observe a process by its standard output and how it
ended (`Exit`: a status, a signal, divergence). This is the process-level
instance of the core, `ProcessObservable`: the events are the bytes written
to standard output, a process exits with a status, aborts with a signal
number, and the C semantics has no function return and no fault payload.

* `Obs.toObservable_injective`, `Obs.ofObservable?_toObservable`: the
  embedding loses nothing, and `Obs.range_toObservable` says exactly which
  observables are C observations (no undefined behaviour, exhaustion or
  fault: the C semantics close undefined behaviour to all observations
  instead);
* `subset_iff_refines`, `refinesOn_iff`: inclusion of C behaviour sets, and
  hence the ladder order `S ⊑[F] T` of `Compile/Category/Lattice.lean`, is
  `Observable.Refines .forbidden` of the embedded sets.

The same type receives core-comp's `Spec.Obs` (`Compile/Core/BehaviourAdapter.lean`),
where an `abort` is signal 6, a trap signal 4 and a fault signal 11, as the
runtime reports them (`Compile.Target.Interp.observe`).
-/

@[expose] public section

namespace Silmaril.Compile.C.Sem

open Silmaril.Machine.Behaviour Silmaril.Compile.Category

/-- Process-level observables: standard-output bytes, then an exit status, a
signal, or one of the generic endings. -/
abbrev ProcessObservable : Type := Observable UInt8 Empty Nat Nat Empty

/-- How a C process ends, as an ending. -/
def Exit.toEnding : Exit → Ending Empty Nat Nat Empty
  | .status n => .exited n
  | .signal n => .aborted n
  | .diverges => .diverges

theorem Exit.toEnding_injective : Function.Injective Exit.toEnding := by
  intro a b h
  cases a <;> cases b <;> simp_all [Exit.toEnding]

/-- A C observation as a process observable. -/
def Obs.toObservable (o : Obs) : ProcessObservable := ⟨o.stdout, o.exit.toEnding⟩

theorem Obs.toObservable_injective : Function.Injective Obs.toObservable := by
  rintro ⟨s, e⟩ ⟨s', e'⟩ h
  simp only [Obs.toObservable, Observable.mk.injEq] at h
  rw [h.1, Exit.toEnding_injective h.2]

/-- Read a process observable back as a C observation. -/
def Obs.ofObservable? (o : ProcessObservable) : Option Obs :=
  match o.ending with
  | .exited n => some ⟨o.trace, .status n⟩
  | .aborted n => some ⟨o.trace, .signal n⟩
  | .diverges => some ⟨o.trace, .diverges⟩
  | _ => none

theorem Obs.ofObservable?_toObservable (o : Obs) : Obs.ofObservable? o.toObservable = some o := by
  obtain ⟨s, e⟩ := o
  cases e <;> rfl

/-- The C observations are the observables ending in an exit, a signal or
divergence. -/
theorem Obs.range_toObservable :
    Set.range Obs.toObservable =
      {o | (∃ n, o.ending = .exited n) ∨ (∃ n, o.ending = .aborted n) ∨ o.ending = .diverges} := by
  ext ⟨t, e⟩
  constructor
  · rintro ⟨⟨s, x⟩, h⟩
    simp only [Obs.toObservable, Observable.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases x <;> simp [Exit.toEnding]
  · rintro (⟨n, he⟩ | ⟨n, he⟩ | he) <;> simp only at he <;> subst he
    · exact ⟨⟨t, .status n⟩, rfl⟩
    · exact ⟨⟨t, .signal n⟩, rfl⟩
    · exact ⟨⟨t, .diverges⟩, rfl⟩

/-- An embedded C behaviour set has no undefined behaviour. -/
theorem safe_image (A : Set Obs) : Observable.Safe (Obs.toObservable '' A) := by
  rintro t ⟨⟨s, x⟩, -, h⟩
  cases x <;> simp [Obs.toObservable, Exit.toEnding] at h

/-- Inclusion of C behaviour sets is core refinement of their embeddings. -/
theorem subset_iff_refines (A B : Set Obs) :
    A ⊆ B ↔ Observable.Refines .forbidden (Obs.toObservable '' A) (Obs.toObservable '' B) := by
  rw [Observable.refines_iff_subset_of_safe (safe_image B)]
  exact (Set.image_subset_image_iff Obs.toObservable_injective).symm

/-- The ladder order of the C semantics is core refinement. -/
theorem refinesOn_iff (F : Set cSyntax.Prog) (S T : Semantics) :
    Syntax.RefinesOn F S T ↔ ∀ p ∈ F,
      Observable.Refines .forbidden (Obs.toObservable '' S p) (Obs.toObservable '' T p) :=
  forall₂_congr fun p _ => subset_iff_refines (S p) (T p)

end Silmaril.Compile.C.Sem
