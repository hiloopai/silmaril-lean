module

public import Silmaril.Wasm.Behaviour.Optimization
public import Silmaril.Wasm.Binaryen.PassAPI.Instances
public import Silmaril.Wasm.Binaryen.PassAPI.Shared

@[expose] public section

/-! # Explicit optimizer modes over actual Core export sessions

These additional contracts retain validity and distinguish exact equivalence,
feasible refinement, and trap insertion. All profiles and hosts are parameters.
The old subset-only refinement and source-trap-as-UB contracts remain available.

Feasible refinement has the old `ExportRefines Eq` safety obligation plus
preservation of observation existence. That extra obligation prevents an empty
behavior set from erasing a guaranteed trap. No totality of arbitrary numerical
profiles or hosts is assumed. Trap insertion matches a prefix of returned values
and then licenses the trace after a target trap, including calls by an embedder
that catches that trap. A source trap supplies no such license.
-/

namespace Silmaril.Wasm.Binaryen.Modes

open Execution.Core Numerics Validation Optimization

variable {H : Type}

def Admission : Mode → Prop → Prop → Prop
  | .equivalence, source, target => source ↔ target
  | .refinement, source, target => source → target
  | .trapInsertion, source, target => source → target

theorem admission_refl (mode : Mode) (source : Prop) : Admission mode source source := by
  cases mode
  · exact Iff.rfl
  · exact id
  · exact id

theorem admission_trans (mode : Mode) {a b c : Prop}
    (hab : Admission mode a b) (hbc : Admission mode b c) : Admission mode a c := by
  cases mode
  · exact hab.trans hbc
  · exact fun h => hbc (hab h)
  · exact fun h => hbc (hab h)

def Instantiates (P : Profile) (host : HostSemantics H) (s : Store H)
    (imports : List ExternAddr) (m : Module) : Prop :=
  ∃ c, Instantiate P host s m imports c

/-- Source-first correctness at actual Core instantiation and export-session
observations; every premise is retained at this boundary. -/
structure ExportCorrect (mode : Mode) (P : Profile) (host : HostSemantics H)
    (source target : Module) : Prop where
  admission : ∀ s imports, StoreOk s → Admission mode
    (Instantiates P host s imports source) (Instantiates P host s imports target)
  observations : ∀ s imports script, StoreOk s →
    Correct (sessionOrder Val) mode
      (moduleObs P host s imports source script) (moduleObs P host s imports target script)

namespace ExportCorrect

theorem refl (mode : Mode) (P : Profile) (host : HostSemantics H) (source : Module) :
    ExportCorrect mode P host source source :=
  ⟨fun _ _ _ => admission_refl mode _, fun _ _ _ _ => correct_refl _ mode _⟩

theorem trans {mode : Mode} {P : Profile} {host : HostSemantics H} {a b c : Module}
    (hab : ExportCorrect mode P host a b) (hbc : ExportCorrect mode P host b c) :
    ExportCorrect mode P host a c :=
  ⟨fun s imports hs => admission_trans mode (hab.admission s imports hs) (hbc.admission s imports hs),
    fun s imports script hs => correct_trans _ mode
      (hab.observations s imports script hs) (hbc.observations s imports script hs)⟩

theorem equivalence_refinement {P : Profile} {host : HostSemantics H} {source target : Module}
    (h : ExportCorrect .equivalence P host source target) :
    ExportCorrect .refinement P host source target :=
  ⟨fun s imports hs => (h.admission s imports hs).mp,
    fun s imports script hs => equivalence_refines (h.observations s imports script hs)⟩

theorem refinement_trapInsertion {P : Profile} {host : HostSemantics H} {source target : Module}
    (h : ExportCorrect .refinement P host source target) :
    ExportCorrect .trapInsertion P host source target :=
  ⟨h.admission, fun s imports script hs =>
    refinement_insertsTraps _ (h.observations s imports script hs)⟩

end ExportCorrect

/-- Under equality, the existing session relation is exact list equality. Its
source-UB constructor cannot be triggered by equality of distinct behaviors. -/
theorem sessionRel_eq_iff {target source : List (Behaviour Val)} :
    SessionRel (· = ·) target source ↔ target = source := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons h _ ih => exact congrArg₂ List.cons h ih
    | ub h =>
      have bad : (Behaviour.traps : Behaviour Val) = .diverges := (h .traps).trans (h .diverges).symm
      cases bad
  · intro h
    subst h
    exact SessionRel.refl (fun _ => rfl) _

theorem equivalence_iff {P : Profile} {host : HostSemantics H} {source target : Module} :
    ExportCorrect .equivalence P host source target ↔ ExportEquiv (· = ·) P host target source := by
  constructor
  · intro h
    constructor
    · refine ⟨fun s imports c hs hi => (h.admission s imports hs).mp ⟨c, hi⟩, ?_⟩
      intro s imports script hs trace ht
      refine ⟨trace, ?_, SessionRel.refl (fun _ => rfl) _⟩
      rw [h.observations s imports script hs]
      exact ht
    · refine ⟨fun s imports c hs hi => (h.admission s imports hs).mpr ⟨c, hi⟩, ?_⟩
      intro s imports script hs trace ht
      refine ⟨trace, ?_, SessionRel.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩
      rw [← h.observations s imports script hs]
      exact ht
  · intro h
    constructor
    · intro s imports hs
      exact ⟨fun ⟨c, hi⟩ => h.1.instantiates s imports c hs hi,
        fun ⟨c, hi⟩ => h.2.instantiates s imports c hs hi⟩
    · intro s imports script hs
      apply Set.Subset.antisymm
      · intro trace ht
        obtain ⟨trace', ht', eq⟩ := h.2.obs s imports script hs trace ht
        exact sessionRel_eq_iff.mp (eq.mono fun _ _ h => h.symm) ▸ ht'
      · intro trace ht
        obtain ⟨trace', ht', eq⟩ := h.1.obs s imports script hs trace ht
        exact sessionRel_eq_iff.mp eq ▸ ht'

/-- An existing exact-equivalence theorem is usable at every mode. -/
theorem ExportCorrect.of_equiv (mode : Mode) {P : Profile} {host : HostSemantics H}
    {source target : Module} (h : ExportEquiv (· = ·) P host target source) :
    ExportCorrect mode P host source target := by
  cases mode
  · exact equivalence_iff.mpr h
  · exact (equivalence_iff.mpr h).equivalence_refinement
  · exact (equivalence_iff.mpr h).equivalence_refinement.refinement_trapInsertion

/-- The safety half of feasible refinement is exactly the old export refinement. -/
theorem refinement_exportRefines {P : Profile} {host : HostSemantics H} {source target : Module}
    (h : ExportCorrect .refinement P host source target) :
    ExportRefines (· = ·) P host target source :=
  ⟨fun s imports c hs hi => h.admission s imports hs ⟨c, hi⟩,
    fun s imports script hs trace ht =>
      ⟨trace, (h.observations s imports script hs).1 ht, SessionRel.refl (fun _ => rfl) _⟩⟩

/-- Upgrade an existing refinement with precisely the additional feasibility
obligation, without changing its transformation or hiding a totality axiom. -/
theorem refinement_of_exportRefines {P : Profile} {host : HostSemantics H} {source target : Module}
    (h : ExportRefines (· = ·) P host target source)
    (feasible : ∀ s imports script, StoreOk s → Feasible
      (moduleObs P host s imports source script) (moduleObs P host s imports target script)) :
    ExportCorrect .refinement P host source target := by
  refine ⟨fun s imports hs ⟨c, hi⟩ => h.instantiates s imports c hs hi, ?_⟩
  intro s imports script hs
  refine ⟨?_, feasible s imports script hs⟩
  intro trace ht
  obtain ⟨trace', ht', eq⟩ := h.obs s imports script hs trace ht
  exact sessionRel_eq_iff.mp eq ▸ ht'

/-- All modes use the same valid-module invariant and the shared pass API. -/
def contract (mode : Mode) (P : Profile) (host : HostSemantics H) :
    Silmaril.Compile.PassAPI.Contract BModule where
  Rel source target := ExportCorrect mode P host source.lower target.lower
  refl source := ExportCorrect.refl mode P host source.lower
  trans := ExportCorrect.trans
  Inv := BModule.Ok

theorem equivalence_le_refinement (P : Profile) (host : HostSemantics H) :
    contract .equivalence P host ≤ contract .refinement P host :=
  ⟨fun _ => Iff.rfl, fun _ _ _ h => h.equivalence_refinement⟩

theorem refinement_le_trapInsertion (P : Profile) (host : HostSemantics H) :
    contract .refinement P host ≤ contract .trapInsertion P host :=
  ⟨fun _ => Iff.rfl, fun _ _ _ h => h.refinement_trapInsertion⟩

theorem old_equivalence_le (P : Profile) (host : HostSemantics H) :
    (PassAPI.equivContract P host).toShared ≤ contract .equivalence P host :=
  ⟨fun _ => Iff.rfl, fun _ _ _ h => equivalence_iff.mpr h⟩

theorem equivalence_le_old (P : Profile) (host : HostSemantics H) :
    contract .equivalence P host ≤ (PassAPI.equivContract P host).toShared :=
  ⟨fun _ => Iff.rfl, fun _ _ _ h => equivalence_iff.mp h⟩

end Silmaril.Wasm.Binaryen.Modes
