module

public import Silmaril.Logic.Institution.Basic
public import Silmaril.Wasm.Component.Reference.DirectLift.Init.Defs
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

namespace Silmaril.Wasm.Institution.DirectLiftTerminal

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.DirectLift
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

noncomputable section

/-- A test for a reachable terminal ABI outcome and the mapped final Core store. -/
abbrev Sentence := CallOutcome → Store Nat → Prop

/-- A certified direct wire at the fixed scalar export interface `x`, together with
the selected invocation. Preparations are start-free, and `Boundary` checks the
argument and signature agreement and the host-free scalar entry. -/
structure ComponentModel (P : Profile) (x : SimpleExport) where
  wire : DirectWire
  shared : Store (CanonHost (core3P P))
  entry : ScalarInstance
  question : entry.F.Op
  args : List Component.Val
  profile : ProfileKind
  call : Nat
  prepared : wire.Prepared P shared (entry.addr question.1)
  boundary : Boundary entry shared x args question
  signature : wire.liftType = liftedFt x
  named : x.name = wire.exportName

/-- Forget the component frame and lower to the actual Core invocation configuration. -/
def ComponentModel.reduct {P : Profile} {x : SimpleExport} (model : ComponentModel P x) : Config Nat :=
  invoke (Store.mapH (fun _ => 0) model.shared) (model.entry.addr model.question.1) model.question.2.val

/-- Stock component calls on the ready frame. The wire allocates its unique lift at slot zero. -/
def ComponentModel.reaches {P : Profile} {x : SimpleExport} (model : ComponentModel P x)
    (out : CallOutcome) (store : Store Nat) : Prop :=
  ∃ final, Calls model.profile (refHost P).hr (D P)
    (model.wire.ready model.shared (model.entry.addr model.question.1)) ⟨model.call⟩ ⟨0⟩
    (model.args.map toRefVal) final out ∧ store = Store.mapH (fun _ => 0) final.store.core

/-- Unfuelled Core termination observed using the fixed export's ABI, not by
defining Core satisfaction as a pullback of component satisfaction. -/
def coreReaches (P : Profile) (x : SimpleExport) (model : Config Nat)
    (out : CallOutcome) (store : Store Nat) : Prop :=
  ∃ final result, Entry.Finishes P Det.noHost model final result ∧ Reports x out result ∧ store = final.store

/-- The Core room uses ordinary Core configurations, with observations through the fixed ABI. -/
def coreRoom (P : Profile) (x : SimpleExport) : Room.{0, 0, 0} :=
  ⟨Sentence, Cat.of (Discrete (Config Nat)), fun model test =>
    ∃ out store, coreReaches P x model.as out store ∧ test out store⟩

/-- The component room uses certified ready direct wires. The discrete model
category deliberately makes no claim about maps between runtime states. -/
def componentRoom (P : Profile) (x : SimpleExport) : Room.{0, 0, 0} :=
  ⟨Sentence, Cat.of (Discrete (ComponentModel P x)), fun model test =>
    ∃ out store, model.as.reaches out store ∧ test out store⟩

end

end Silmaril.Wasm.Institution.DirectLiftTerminal
