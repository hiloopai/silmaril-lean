module

public import Silmaril.Wasm.Institution.DirectLiftTerminal.Defs
import Silmaril.Wasm.Component.Reference.DirectLift.Init.Thms

public section

namespace Silmaril.Proofs.Wasm.Institution.DirectLiftTerminal

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.DirectLift
open Silmaril.Wasm.Institution.DirectLiftTerminal
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core

theorem reaches_iff {P : Profile} {x : SimpleExport} (model : ComponentModel P x)
    (out : CallOutcome) (store : Store Nat) :
    model.reaches out store ↔ coreReaches P x model.reduct out store := by
  have init := (DirectWire.instantiates_iff (prof := model.profile) model.prepared).2
    ⟨rfl, rfl, rfl⟩
  have named : model.wire.exportMap.lookup x.name = some (⟨0⟩ : FuncId) := by
    simp [model.named, DirectWire.exportMap]
  exact DirectWire.terminalObservationIff model.prepared model.boundary model.signature init named

end Silmaril.Proofs.Wasm.Institution.DirectLiftTerminal
