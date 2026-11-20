module

public import Silmaril.Wasm.Institution.DirectLiftTerminal.Defs
public import Mathlib.CategoryTheory.ComposableArrows.Basic
import Silmaril.Proofs.Wasm.Institution.DirectLiftTerminal

@[expose] public section

namespace Silmaril.Wasm.Institution.DirectLiftTerminal

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component (CallOutcome)
open Silmaril.Wasm.Component.Reference (SimpleExport)
open Silmaril.Wasm.Numerics (Profile)

noncomputable section

/-- Both independent relations give the same terminal observations, including the store. -/
theorem ComponentModel.reaches_iff {P : Profile} {x : SimpleExport} (model : ComponentModel P x)
    (out : CallOutcome) (store : Store Nat) :
    model.reaches out store ↔ coreReaches P x model.reduct out store :=
  Proofs.Wasm.Institution.DirectLiftTerminal.reaches_iff model out store

/-- Sentences keep the same ABI and store predicate; component models reduce
contravariantly to Core invocations. Satisfaction uses `reaches_iff` in both directions. -/
def corridor (P : Profile) (x : SimpleExport) : coreRoom P x ⟶ componentRoom P x where
  sen := id
  mod := Discrete.functor fun model => Discrete.mk model.reduct
  sat model test := by
    change Discrete (ComponentModel P x) at model
    change (∃ out store, model.as.reaches out store ∧ test out store) ↔
      (∃ out store, coreReaches P x model.as.reduct out store ∧ test out store)
    simp only [ComponentModel.reaches_iff]

/-- The two signatures are the Core and component *views* of a fixed ABI.
The only nonidentity arrow is the direct-lift corridor. This is not a category
of arbitrary ABI changes, linking operations, or Wasm dialects. -/
def roomDiagram (P : Profile) (x : SimpleExport) : Fin 2 ⥤ Room.{0, 0, 0} :=
  ComposableArrows.mk₁ (corridor P x)

/-- Use the repository's institution construction, with its sentence and
contravariant model functor laws. There are no fuel parameters. -/
def institution (P : Profile) (x : SimpleExport) : ClassicInstitution (Fin 2) :=
  ClassicInstitution.ofRoomFunctor (roomDiagram P x)

end

end Silmaril.Wasm.Institution.DirectLiftTerminal
