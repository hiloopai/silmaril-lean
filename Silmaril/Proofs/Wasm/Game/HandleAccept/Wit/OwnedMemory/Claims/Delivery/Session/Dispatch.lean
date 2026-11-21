module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.Dispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall ComponentCall.Delivery.FiniteSession ComponentCall.Delivery.FiniteSession.Dispatch

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)} {callees : List (Callee sig)}
  {start finish : Config (core3 grow) (HostState sig)}

theorem closedDispatch {call : Call (core3 grow)} (closed : ¬ UsesComponent call) :
    coreOnly ready bindings call = linked ready bindings callees call := by
  cases call with
  | funcInst | hostFunc => exact False.elim (closed trivial)
  | hostCallout callout => cases callout <;> rfl
  | threadBody body => cases body <;> rfl
  | onCancel cancel => cases cancel <;> rfl
  | _ => rfl

theorem closedAgrees (closed : ClosedAt start) : AgreesAt ready bindings callees start :=
  fun focus => closedDispatch (closed focus)

theorem overlayStep {label} (agrees : AgreesAt ready bindings callees start)
    (step : Step profile ready (coreOnly ready bindings) start label finish) :
    Step profile ready (linked ready bindings callees) start label finish := by
  cases step with
  | call focus =>
    rw [agrees focus]
    exact .call focus
  | coreCallout focus status =>
    rw [closedDispatch (ready := ready) (bindings := bindings) (callees := callees) (call := .hostCallout _ _) (fun impossible => impossible)]
    exact .coreCallout focus status
  | newThread focus alloc =>
    unfold StepDefs.threadAct
    rw [closedDispatch (ready := ready) (bindings := bindings) (callees := callees) (call := .threadBody _) (fun impossible => impossible)]
    exact .newThread focus alloc
  | popProg focus => exact .popProg focus
  | popCore focus => exact .popCore focus
  | threadExit focus => exact .threadExit focus
  | hostDone focus => exact .hostDone focus
  | callCore focus => exact .callCore focus
  | coreInternal focus status advance => exact .coreInternal focus status advance
  | coreReturned focus status => exact .coreReturned focus status
  | coreTrap focus status => exact .coreTrap focus status
  | get focus => exact .get focus
  | modify focus => exact .modify focus
  | trap focus => exact .trap focus
  | choose answer focus allowed => exact .choose answer focus allowed
  | currentThread focus => exact .currentThread focus
  | block focus => exact .block focus
  | blockSwitch focus saved => exact .blockSwitch focus saved
  | resumeThread focus saved => exact .resumeThread focus saved
  | hostGet focus => exact .hostGet focus
  | hostSet focus => exact .hostSet focus
  | emit focus => exact .emit focus
  | fault reason => exact .fault reason
  | hostInvoke hostReady fresh => exact .hostInvoke hostReady fresh
  | hostTick hostReady => exact .hostTick hostReady
  | hostCancel hostReady cancel unresolved => exact .hostCancel hostReady cancel unresolved
  | hostRun hostReady => exact .hostRun hostReady

theorem compatibleSteps {labels} (run : Compatible profile ready bindings callees start labels finish) :
    Steps profile ready (linked ready bindings callees) start labels finish := by
  induction run with
  | done => exact .refl _
  | next agrees step _ ih => exact .cons (overlayStep agrees step) ih

theorem closedPrefix {labels} (run : Steps profile ready (coreOnly ready bindings) start labels finish)
    (closed : ClosedThrough profile ready bindings start labels finish) : Compatible profile ready bindings callees start labels finish := by
  induction run with
  | refl => exact .done _
  | cons step tail ih =>
    refine .next (closedAgrees (closed (leading := []) rfl (.refl _) (.cons step tail))) step (ih ?_)
    intro leading cut label trailing eq before after
    exact closed (leading := _ :: leading) (congrArg (_ :: ·) eq) (.cons step before) after

theorem corePrefix {count : Nat}
    (run : Steps profile ready (coreOnly ready bindings) start (List.replicate count .core) finish) :
    Compatible profile ready bindings callees start (List.replicate count .core) finish := by
  induction count generalizing start with
  | zero => cases run; exact .done _
  | succ count ih =>
    cases run with
    | cons step tail =>
      cases step with
      | coreInternal focused status advance =>
        refine .next (closedAgrees ?_) (.coreInternal focused status advance) (ih tail)
        intro thread call next frames rest focus
        rw [focused] at focus
        cases focus

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.Dispatch
