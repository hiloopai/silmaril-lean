module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Plain.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain

open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Component
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (LocalIssue)

/-- An exact finite path whose executed steps never focus a direct dispatch.
The terminal focus need not be closed. -/
inductive NoDirectCalls {E : CoreEngine} {Host : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) :
    Machine.Config E Host → List (Machine.Label E Host) → Machine.Config E Host → Prop where
  | done (state : Machine.Config E Host) : NoDirectCalls profile ready dispatch state [] state
  | next {start middle finish label labels}
      (closed : ∀ {thread call next frames rest}, start.ctl ≠ ⟨thread, .prog (.op (.call call) next), frames⟩ :: rest)
      (step : Machine.Step profile ready dispatch start label middle)
      (tail : NoDirectCalls profile ready dispatch middle labels finish) :
      NoDirectCalls profile ready dispatch start (label :: labels) finish

/-- Evaluate the non-suspending part of a checked import. A known activation
supplies its thread (which may be absent on a host frame). With no activation
given, even a thread query is rejected; neither case handles suspension or calls.
An unsupported request retains all preceding effects. -/
def runBody {E : CoreEngine} {Host Result : Type} (body : P E Host Result)
    (reference : CStore E) (host : Host) (activation : Option (Option ThreadId) := none) :
    CStore E × Host × Except LocalIssue Result :=
  match body with
  | .pure result => (reference, host, .ok result)
  | .op op next =>
    match op with
    | .get => runBody (next reference) reference host activation
    | .modify update => runBody (next ()) (update reference) host activation
    | .hostGet => runBody (next host) reference host activation
    | .hostSet updated => runBody (next ()) reference updated activation
    | .trap reason => (reference, host, .error (.trapped reason))
    | .choose _ => (reference, host, .error .choice)
    | .callCore _ _ => (reference, host, .error .coreCall)
    | .call _ => (reference, host, .error .canonicalCall)
    | .currentThread =>
      match activation with
      | some thread => runBody (next thread) reference host activation
      | none => (reference, host, .error .scheduling)
    | .newThread _ | .block _ | .resumeThread _ =>
      (reference, host, .error .scheduling)
    | .emit _ => (reference, host, .error .hostEffect)
termination_by structural body

/-- Resolve the active thread's instance through the live arenas. A host frame
has no instance; a dangling thread or task is a reference-machine error, not
a recoverable wrong-caller refusal. -/
def callerInstance {E : CoreEngine} (reference : CStore E) : Option ThreadId →
    Except LocalIssue (Option InstId)
  | none => .ok none
  | some thread => do
    let some active := ArenaField.threads.get? reference thread
      | throw (.trapped (.internal "dangling arena id"))
    let some task := ArenaField.tasks.get? reference active.task
      | throw (.trapped (.internal "dangling arena id"))
    return some task.inst

/-- The endpoint-only diagnostic matched by a scheduled receipt-aware refusal.
`none` does not turn a new diagnostic into old success. -/
def oldIssue : Issue → Option Endpoints.Core.Scheduled.Issue
  | .accept issue => Core.Plain.oldIssue issue |>.map .accept
  | .wrongContext => some .wrongContext
  | .wrongType => some .wrongType
  | .ambiguousBinding => some .ambiguousBinding
  | .badSelection => some .badSelection
  | _ => none

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain
