module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Traversal.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

/-- A finite decomposition of a checked run into scheduler segments and
compared gives. The canonical body of a give is itself a plan, so callouts
under a parked allocator can be compared before following the outer suffix.
Local body evidence names the actual replies or stop; it does not supply a
run at the replacement host or the older paired frames. -/
inductive NestedPlan (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) :
    Config (core3 grow) (HostState sig) → Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | segment {start labels finish}
      (run : Steps profile ready (specDispatch ready base) start labels finish) :
      NestedPlan bindings profile ready base start labels finish
  | localSegment {start labels finish}
      (run : PayloadPrefix.LocalSteps profile ready (specDispatch ready base) start labels finish) :
      NestedPlan bindings profile ready base start labels finish
  | commit {start target index} (resolve : ComponentCall.Delivery.LinkedResolution start target index) :
      NestedPlan bindings profile ready base start (List.replicate 17 .tau) resolve.committed
  | poll {start target index result suffix} (poll : ComponentCall.Delivery.ParkedPoll start target profile)
      (pending : ComponentCall.Delivery.PendingAt start.store target index)
      (branch : BufferBranch start.store poll.memory (flatNat poll.out) result suffix) :
      NestedPlan bindings profile ready base start (pollLabels poll ++ suffix)
        (result.finish (pollReply poll index) { start with store := StepDefs.lockdownSt poll.delivered, ctl := [] })
  | waitBlock {start} (wait : ComponentCall.Delivery.ParkedWait start) (empty : start.store.wsetHasEvent wait.ws = false) :
      NestedPlan bindings profile ready base start (List.replicate 13 .tau) wait.blocked
  | waitReady {start} (wait : ComponentCall.Delivery.ParkedWait start) (available : start.store.wsetHasEvent wait.ws = true)
      (early : Bool) (allowed : Allowed profile (.earlyReturn .waitableSetWait) early) :
      NestedPlan bindings profile ready base start (ComponentCall.Delivery.ParkedWait.readyLabels early)
        (if early then wait.early else wait.blocked)
  | waitResume {initial start} {wait : ComponentCall.Delivery.ParkedWait initial}
      (resume : ComponentCall.Delivery.WaitResume wait start) (saved : start.cont? wait.thread = some wait.saved) :
      NestedPlan bindings profile ready base start (List.replicate 4 .tau) resume.reached
  | waitTake {initial start target index result suffix} {wait : ComponentCall.Delivery.ParkedWait initial}
      (delivery : ComponentCall.Delivery.WaitDelivery wait start profile target)
      (focused : start.ctl = ⟨some wait.thread, .prog wait.takeEvent, .core wait.core wait.next :: wait.segments⟩ :: start.ctl.drop 1)
      (pending : ComponentCall.Delivery.PendingAt start.store target index)
      (branch : BufferBranch delivery.delivered wait.memory (flatNat wait.out) result suffix) :
      NestedPlan bindings profile ready base start (delivery.labels ++ suffix)
        (result.finish (delivery.resumed index) { start with store := StepDefs.lockdownSt delivery.delivered, ctl := [] })
  | cancelReturned {start target index} (cancel : ComponentCall.Delivery.ParkedCancel start target)
      (pending : ComponentCall.Delivery.PendingAt start.store target index)
      (available : ComponentCall.Delivery.CancelAvailable start.store target) :
      NestedPlan bindings profile ready base start (List.replicate 15 .tau) cancel.resumed
  | cancelRequest {start target} (cancel : ComponentCall.Delivery.ParkedCancel start target) (record : Subtask)
      (live : start.store.subtask? target = some record) (unresolved : record.state.resolved = false)
      (notDelivered : record.lenders.isSome = true) (notRequested : record.cancellationRequested = false)
      (notJoined : record.common.wset = none) :
      NestedPlan bindings profile ready base start (List.replicate 14 .tau) (cancel.callbackEntry record ready base)
  | cancelReentry {start target callee} {cancel : ComponentCall.Delivery.ParkedCancel start target}
      (request : ComponentCall.Delivery.TaskCancelAdmission cancel) (mode : ComponentCall.Delivery.TaskCancelReentry request ready)
      (saved : start.cont? request.implicitThread = some callee) :
      NestedPlan bindings profile ready base start (List.replicate request.reentrySteps .tau) (request.reentered callee)
  | cancelCallbackDone {start target} {cancel : ComponentCall.Delivery.ParkedCancel start target}
      (request : ComponentCall.Delivery.StartedCancel cancel) :
      NestedPlan bindings profile ready base start (List.replicate 20 .tau) request.callbackReturned
  | cancelPark {initial start target} {cancel : ComponentCall.Delivery.ParkedCancel initial target}
      (wait : ComponentCall.Delivery.SyncCancelWait cancel start) :
      NestedPlan bindings profile ready base start (List.replicate 5 .tau) wait.blocked
  | cancelResume {initial start target} {cancel : ComponentCall.Delivery.ParkedCancel initial target}
      (resume : ComponentCall.Delivery.SyncCancelResume cancel start) (saved : start.cont? cancel.thread = some cancel.saved) :
      NestedPlan bindings profile ready base start (List.replicate 3 .tau) resume.reached
  | cancelFinish {initial start target rest} (cancel : ComponentCall.Delivery.ParkedCancel initial target) (record : Subtask)
      (focused : start.ctl = ⟨some cancel.thread, .prog (ComponentCall.Delivery.ParkedCancel.finish target),
        .core cancel.core cancel.next :: cancel.segments⟩ :: rest)
      (live : start.store.subtask? target = some record) (resolved : record.state.resolved = true)
      (pending : record.common.pending = some (.subtask target)) :
      NestedPlan bindings profile ready base start (List.replicate 6 .tau) (cancel.finishReply start record.state rest)
  | sequence {start middle finish leading trailing}
      (front : NestedPlan bindings profile ready base start leading middle)
      (back : NestedPlan bindings profile ready base middle trailing finish) :
      NestedPlan bindings profile ready base start (leading ++ trailing) finish
  | give {route} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      {entryLabels checkLabels referenceLabels reached reference checked baseline}
      (entry : Transition profile ready base site.start (.give route .entered) entryLabels site.checked)
      (checkedBody : Steps profile ready (specDispatch ready base) site.checked checkLabels reached)
      (body : NestedPlan bindings profile ready base (site.reference site.referenceReply) (referenceLabels ++ [.tau]) baseline)
      (value : route.output.Result)
      (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible referenceLabels) :
      NestedPlan bindings profile ready base site.start (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked
  | stop {route} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      {entryLabels checkLabels referenceLabels reached reference phase check}
      (entry : Transition profile ready base site.start (.give route .entered) entryLabels site.checked)
      (checkedBody : Steps profile ready (specDispatch ready base) site.checked checkLabels reached)
      (body : NestedPlan bindings profile ready base (site.reference site.referenceReply) referenceLabels reference)
      (stop : GiveStop site check phase referenceLabels reached reference)
      (store : reached.store = reference.store)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible referenceLabels) :
      NestedPlan bindings profile ready base site.start (entryLabels ++ checkLabels) reached

/-- Reasons to stop at an actual live configuration. A local checked stop
has a matched store and observed trace, but does not rejoin (including when
the plan has a later checked-only suffix). Unselected roots are not assumed
to retain their previous tree across earlier compared episodes. -/
inductive NestedCut (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) :
    Config (core3 grow) (HostState sig) → Prop where
  | request {before incoming label after}
      (paired : HostFrame.Related.Paired older before incoming)
      (install : GiveInstall bindings (specDispatch ready base) before label after) :
      NestedCut bindings profile ready base older incoming
  | boundary {before incoming label after reached}
      (paired : HostFrame.Related.Paired older before incoming)
      (cut : HostFrame.Related.Boundary older before incoming label after reached)
      (checkedStep : Step profile ready (specDispatch ready base) before label after)
      (referenceStep : Step profile ready (specDispatch ready (host bindings base)) incoming label reached) :
      NestedCut bindings profile ready base older reached
  | unselected {route incoming} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      (paired : HostFrame.Related.Paired older site.start incoming)
      (selection : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle ≠ some site.tree) :
      NestedCut bindings profile ready base older incoming
  | publication {start target index incoming} (resolve : ComponentCall.Delivery.LinkedResolution start target index)
      (paired : HostFrame.Related.Paired older start incoming)
      (different : ¬ ∃ writer, incoming.host.writer.register resolve.tree = .ok writer ∧
        writer.accepted.length = resolve.writer.accepted.length) :
      NestedCut bindings profile ready base older incoming
  | cancelReadiness {start target incoming} {cancel : ComponentCall.Delivery.ParkedCancel start target}
      (request : ComponentCall.Delivery.TaskCancelAdmission cancel) (mode : ComponentCall.Delivery.TaskCancelReentry request ready)
      (paired : HostFrame.Related.Paired older start incoming)
      (different : ¬ (request.callee.state = .started →
        request.markedStore.threadReady (ready incoming.host) request.implicitThread = true)) :
      NestedCut bindings profile ready base older incoming
  | stopped {route phase checkLabels referenceLabels liveLabels liveStart checked reference reached check}
      (site : PayloadRoot.Site grow sig route) (stop : GiveStop site check phase referenceLabels checked reference)
      (checkedBody : Steps profile ready (specDispatch ready base) site.checked checkLabels checked)
      (referenceBody : Steps profile ready (specDispatch ready (host bindings base)) liveStart liveLabels reached)
      (paired : HostFrame.Related.Paired older reference reached)
      (store : checked.store = reached.store)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible liveLabels) :
      NestedCut bindings profile ready base older reached

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch
