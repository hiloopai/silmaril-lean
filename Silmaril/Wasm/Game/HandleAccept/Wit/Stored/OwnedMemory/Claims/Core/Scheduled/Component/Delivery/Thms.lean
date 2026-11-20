module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {initial committed parked : Config (core3 grow) (HostState sig)} {subtask : SubtaskId} {index : Nat}

theorem Retaining.reaches {labels}
    (path : Retaining profile ready (specDispatch ready impl) subtask index committed labels parked)
    (pending : PendingAt committed.store subtask index) :
    Steps profile ready (specDispatch ready impl) committed labels parked ∧ PendingAt parked.store subtask index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.retainingPath path pending

theorem Retaining.of_subtasks {E : CoreEngine} {Host : Type} {hr : HostReady Host} {dispatch : Call E → P E Host (Ret E)}
    {state reached : Config E Host} {label} (run : Step profile hr dispatch state label reached)
    (same : reached.store.subtasks = state.store.subtasks) : Retaining profile hr dispatch subtask index state [label] reached :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.stepOfSubtasks run same

theorem Retaining.join {E : CoreEngine} {Host : Type} {hr : HostReady Host} {dispatch : Call E → P E Host (Ret E)}
    {state : Config E Host} {thread segments rest}
    (waitable : Waitable) (set : Option WsetId) (next : P E Host (Ret E))
    (focused : state.ctl = ⟨thread, .prog (Waitable.join waitable set >>= fun () => next), segments⟩ :: rest) :
    Retaining profile hr dispatch subtask index state [.tau]
      { state with store := state.store.joinSt waitable set, ctl := ⟨thread, .prog next, segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.joinStep waitable set next focused

theorem LinkedResolution.indexed_steps (resolve : LinkedResolution initial subtask index) :
    Steps profile ready (specDispatch ready impl) initial (List.replicate 17 .tau) resolve.committed ∧
      PendingAt resolve.committed.store subtask index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resolutionIndexed resolve

/-- Between result commit and a selected parked poll, the reached prefix
must retain the pending event. Poll buffer traps still occur after removal
and lend release, not before commit or as a rollback. -/
theorem LinkedResolution.then_poll (resolve : LinkedResolution initial subtask index) {between}
    (path : Retaining profile ready (specDispatch ready impl) subtask index resolve.committed between parked)
    (poll : ParkedPoll parked subtask profile) :
    poll.steps index ready impl initial (List.replicate 17 .tau ++ between) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resolutionPoll resolve path poll

theorem ParkedPoll.delivered_clears (poll : ParkedPoll parked subtask profile) (pending : PendingAt parked.store subtask index) :
    ∃ record, poll.delivered.subtask? subtask = some record ∧ record.common.pending = none ∧
      record.lenders = none ∧ record.state = .returned ∧ record.index = some index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.deliveredClears poll pending

/-- An empty poll or another waitable's delivery preserves the tracked return event
and saved slot at each cut, including through the actual canonical shuffle and take.
The endpoint is just before result-buffer validation and writes. -/
theorem PollAdmission.retains_until_unpack (poll : PollAdmission parked) (saved : ThreadId)
    (selection : PollRetention profile parked.store poll.ws subtask) :
    ParkedRetaining profile ready (specDispatch ready impl) saved subtask index parked
      (List.replicate 8 .tau ++ selection.labels) (poll.beforeUnpack selection.reached) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.poll_retains_until_unpack
    impl poll saved subtask index selection

theorem ParkedRetaining.reaches {saved labels}
    (path : ParkedRetaining profile ready (specDispatch ready impl) saved subtask index committed labels parked)
    (pending : PendingAt committed.store subtask index) :
    ParkedPrefix profile ready (specDispatch ready impl) saved committed labels parked ∧
      PendingAt parked.store subtask index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.retainingParked path pending

/-- Extend the same retained path through the actual buffer writes and Core reply,
or through a late buffer trap. A trap does not undo another waitable's delivery. -/
theorem PollAdmission.retains_through_reply (poll : PollAdmission parked) (saved : ThreadId)
    (selection : PollRetention profile parked.store poll.ws subtask) :
    poll.retentionOutcomes selection ready impl saved index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.poll_retention_outcomes
    impl poll saved subtask index selection

/-- With no event available, the wait registers the actual ready condition and parks the
Core continuation. It neither returns to Core nor consumes an event. -/
theorem ParkedWait.blocks (wait : ParkedWait initial) (empty : initial.store.wsetHasEvent wait.ws = false) :
    Steps profile ready (specDispatch ready impl) initial (List.replicate 13 .tau) wait.blocked :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.parkedWaitBlocks wait empty

/-- A ready Core wait still obeys the profile's actual choice: the early
branch reaches event selection; the other branch installs the saved wait. -/
theorem ParkedWait.ready_choice (wait : ParkedWait initial) (available : initial.store.wsetHasEvent wait.ws = true)
    (early : Bool) (allowed : Allowed profile (.earlyReturn .waitableSetWait) early) :
    Steps profile ready (specDispatch ready impl) initial (ParkedWait.readyLabels early)
      (if early then wait.early else wait.blocked) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.parkedWaitReady wait available early allowed

/-- The early branch consumes the selected return from the reached store and
then writes the buffer or traps, without a block or host tick. -/
theorem ParkedWait.delivers_early (wait : ParkedWait initial) (available : initial.store.wsetHasEvent wait.ws = true)
    (allowed : Allowed profile (.earlyReturn .waitableSetWait) true)
    (delivery : WaitDelivery wait wait.early profile subtask) (pending : PendingAt initial.store subtask index) :
    delivery.outcomes index ready impl initial (ParkedWait.readyLabels true) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.earlyWaitDelivery wait available allowed delivery pending

/-- On the selected tick, resume the saved wait and reach selection in the current store.
This does not assume that the scheduler will ever select that waiter. -/
theorem WaitTick.resumes {atHost : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
    (tick : WaitTick wait atHost ready profile) (saved : atHost.cont? wait.thread = some wait.saved) :
    Steps profile ready (specDispatch ready impl) atHost tick.labels tick.reached :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resumeWaitTick tick saved

/-- A reached resume of the same blocked occurrence restores its actual saved
activation, without requiring a tick or a ready event. Selection is subsequent. -/
theorem WaitResume.resumes_tracked {atResume : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
    (resume : WaitResume wait atResume) {leading}
    (prefixRun : ParkedPrefix profile ready (specDispatch ready impl) wait.thread wait.blocked leading atResume) :
    Steps profile ready (specDispatch ready impl) wait.blocked (leading ++ List.replicate 4 .tau) resume.reached :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resumeTrackedWait resume prefixRun

/-- A reached forced resume without an event does not behave like an empty poll.
The actual wait decrements its count and shuffles before trapping. -/
theorem WaitResume.traps_empty {atResume : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
    (resume : WaitResume wait atResume) {leading}
    (prefixRun : ParkedPrefix profile ready (specDispatch ready impl) wait.thread wait.blocked leading atResume)
    (record : WaitableSet) (perm : List Nat) (live : resume.reached.store.wset? wait.ws = some record)
    (empty : resume.reached.store.wsetHasEvent wait.ws = false) (allowed : Allowed profile (.shuffle record.elems.length) perm) :
    Steps profile ready (specDispatch ready impl) wait.blocked
      ((leading ++ List.replicate 4 .tau) ++ [.tau, .choice (.shuffle record.elems.length) perm, .tau, .tau,
        .trap (.internal "WaitableSet.get_pending_event: no pending event")])
      (StepDefs.trapCfg { resume.reached with
        store := resume.reached.store.wsetSetElemsSt wait.ws (applyPerm perm record.elems) }) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resumeWaitEmpty resume prefixRun
    record perm live empty allowed

/-- If the same pending return survives to a reached resume, the selected
delivery uses the reached store and the caller from the original saved wait. -/
theorem WaitResume.delivers_returned {atResume : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
    (resume : WaitResume wait atResume) {leading}
    (prefixRun : ParkedRetaining profile ready (specDispatch ready impl) wait.thread subtask index
      wait.blocked leading atResume)
    (pending : PendingAt wait.blocked.store subtask index)
    (delivery : WaitDelivery wait resume.reached profile subtask) :
    delivery.outcomes index ready impl wait.blocked (leading ++ List.replicate 4 .tau) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resumedWaitDelivery resume prefixRun pending delivery

/-- A resolution can feed a previously blocked Core wait on the selected tick.
The actual buffer check follows consumption; a trap retains the earlier effects. -/
theorem LinkedResolution.then_wait {atHost : Config (core3 grow) (HostState sig)} {wait : ParkedWait parked}
    {tick : WaitTick wait atHost ready profile} (delivery : WaitDelivery wait tick.reached profile subtask)
    (resolve : LinkedResolution initial subtask index) {between}
    (path : Retaining profile ready (specDispatch ready impl) subtask index resolve.committed between atHost)
    (saved : atHost.cont? wait.thread = some wait.saved) :
    delivery.outcomes index ready impl initial ((List.replicate 17 .tau ++ between) ++ tick.labels) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resolutionWait delivery resolve path saved

/-- Compose the actual block, reached resolution and selected wakeup. The
same saved activation is derived from the actual edits, not a final lookup. -/
theorem ParkedWait.then_resolution {atHost resolving : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
    {tick : WaitTick wait atHost ready profile} (delivery : WaitDelivery wait tick.reached profile subtask)
    (empty : initial.store.wsetHasEvent wait.ws = false) {whileBlocked between}
    (runs : ParkedPrefix profile ready (specDispatch ready impl) wait.thread wait.blocked whileBlocked resolving)
    (resolve : LinkedResolution resolving subtask index)
    (path : ParkedRetaining profile ready (specDispatch ready impl) wait.thread subtask index resolve.committed between atHost) :
    delivery.outcomes index ready impl initial
      ((((List.replicate 13 .tau ++ whileBlocked) ++ List.replicate 17 .tau) ++ between) ++ tick.labels) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.blockedResolutionWait delivery empty runs resolve path

/-- On an already resolved subtask, cancel consumes the returned event and
reports its existing state. It does not run the cancellation callback. -/
theorem ParkedCancel.delivers_returned (cancel : ParkedCancel parked subtask) (pending : PendingAt parked.store subtask index)
    (available : CancelAvailable parked.store subtask) :
    Steps profile ready (specDispatch ready impl) parked (List.replicate 15 .tau) cancel.resumed :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.cancelReturned cancel pending available

/-- An unresolved cancel first records the request and its sync waiter, then
enters the actual late-bound cancellation callback. No return is assumed. -/
theorem ParkedCancel.requests (cancel : ParkedCancel parked subtask) (record : Subtask)
    (live : parked.store.subtask? subtask = some record) (unresolved : record.state.resolved = false)
    (notDelivered : record.lenders.isSome = true) (notRequested : record.cancellationRequested = false)
    (notJoined : record.common.wset = none) :
    Steps profile ready (specDispatch ready impl) parked (List.replicate 14 .tau)
      (cancel.callbackEntry record ready impl) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.cancelRequests cancel record live
    unresolved notDelivered notRequested notJoined

/-- Initial cancellation forces the resume; a started guest reenters only
when its reached implicit thread is cancellable and ready after marking. -/
theorem TaskCancelAdmission.reenters {cancel : ParkedCancel parked subtask} (request : TaskCancelAdmission cancel)
    (mode : TaskCancelReentry request ready) {callee : Activation (core3 grow) (HostState sig)}
    (saved : parked.cont? request.implicitThread = some callee) :
    Steps profile ready (specDispatch ready impl) parked (List.replicate request.reentrySteps .tau)
      (request.reentered callee) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.taskCancelReenters cancel request mode saved

/-- On this closed guest callback path, cancel marks the started task pending
cancel, clears the temporary waiter and returns BLOCKED to the same Core caller. -/
theorem StartedCancel.resumes_blocked {cancel : ParkedCancel parked subtask} (request : StartedCancel cancel)
    (asynchronous : cancel.async_ = true) :
    Steps profile ready (specDispatch ready impl) parked (List.replicate 24 .tau) request.resumed :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.cancelStartedBlocked cancel request asynchronous

theorem StartedCancel.returns_from_callback {cancel : ParkedCancel parked subtask} (request : StartedCancel cancel) :
    Steps profile ready (specDispatch ready impl) parked (List.replicate 20 .tau) request.callbackReturned :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.cancelStartedReturns cancel request

def StartedCancel.syncWait {cancel : ParkedCancel parked subtask} (request : StartedCancel cancel)
    (synchronous : cancel.async_ = false) : SyncCancelWait cancel request.callbackReturned :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.startedCancelWait cancel request synchronous

/-- With an unresolved subtask, K8 blocks without an early-return choice and
saves the original Core continuation. -/
theorem SyncCancelWait.blocks {cancel : ParkedCancel parked subtask} {atReturn : Config (core3 grow) (HostState sig)}
    (wait : SyncCancelWait cancel atReturn) :
    Steps profile ready (specDispatch ready impl) atReturn (List.replicate 5 .tau) wait.blocked :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.syncCancelBlocks cancel wait

theorem StartedCancel.blocks {cancel : ParkedCancel parked subtask} (request : StartedCancel cancel)
    (synchronous : cancel.async_ = false) :
    Steps profile ready (specDispatch ready impl) parked (List.replicate 25 .tau) (request.syncWait synchronous).blocked :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.startedCancelBlocks cancel request synchronous

theorem SyncCancelResume.resumes_tracked {cancel : ParkedCancel parked subtask}
    {atReturn atResume : Config (core3 grow) (HostState sig)} {leading}
    (resume : SyncCancelResume cancel atResume) (wait : SyncCancelWait cancel atReturn)
    (prefixRun : ParkedPrefix profile ready (specDispatch ready impl) cancel.thread wait.blocked leading atResume) :
    Steps profile ready (specDispatch ready impl) wait.blocked (leading ++ List.replicate 3 .tau) resume.reached :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.syncCancelResumes cancel wait resume prefixRun

/-- After resumption, a reached pending return is consumed before the same
Core caller receives its reply. This uses the reached event, not the request-time state. -/
theorem SyncCancelResume.delivers_returned {cancel : ParkedCancel parked subtask}
    {atResume : Config (core3 grow) (HostState sig)} (resume : SyncCancelResume cancel atResume)
    (pending : PendingAt atResume.store subtask index) :
    Steps profile ready (specDispatch ready impl) resume.reached (List.replicate 6 .tau) resume.delivered :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.syncCancelDelivers cancel resume pending

theorem SelectedTick.waiting {thread : ThreadId} {atHost : Config (core3 grow) (HostState sig)}
    (tick : SelectedTick thread atHost ready profile) : tick.atResume.store.threadIs Thread.waiting thread = true :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.selectedTickWaiting tick

/-- Commit the linked result while K8 is parked, then deliver it to the original
caller when the scheduler actually selects that saved thread on a tick. -/
theorem SyncCancelWait.linked_tick_delivers {cancel : ParkedCancel parked subtask}
    {atReturn resolving atHost : Config (core3 grow) (HostState sig)} {whileBlocked between}
    (wait : SyncCancelWait cancel atReturn)
    (runs : ParkedPrefix profile ready (specDispatch ready impl) cancel.thread wait.blocked whileBlocked resolving)
    (resolve : LinkedResolution resolving subtask index)
    (path : ParkedRetaining profile ready (specDispatch ready impl) cancel.thread subtask index resolve.committed between atHost)
    (tick : SelectedTick cancel.thread atHost ready profile) :
    Steps profile ready (specDispatch ready impl) atReturn
      (List.replicate 5 .tau ++ whileBlocked ++ List.replicate 17 .tau ++ between ++
        tick.selectionLabels ++ List.replicate 9 .tau)
      (SyncCancelResume.afterTick tick tick.waiting).delivered :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.syncCancelLinkedTick cancel wait runs resolve path tick

/-- The closed started-task route reaches K8 from the original Core callout;
no callback-return or saved-activation equality is a premise. -/
theorem StartedCancel.linked_tick_delivers {cancel : ParkedCancel parked subtask}
    {resolving atHost : Config (core3 grow) (HostState sig)} {whileBlocked between}
    (request : StartedCancel cancel) (synchronous : cancel.async_ = false)
    (runs : ParkedPrefix profile ready (specDispatch ready impl) cancel.thread
      (request.syncWait synchronous).blocked whileBlocked resolving)
    (resolve : LinkedResolution resolving subtask index)
    (path : ParkedRetaining profile ready (specDispatch ready impl) cancel.thread subtask index resolve.committed between atHost)
    (tick : SelectedTick cancel.thread atHost ready profile) :
    Steps profile ready (specDispatch ready impl) parked
      (List.replicate 25 .tau ++ whileBlocked ++ List.replicate 17 .tau ++ between ++
        tick.selectionLabels ++ List.replicate 9 .tau)
      (SyncCancelResume.afterTick tick tick.waiting).delivered :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.startedCancelLinkedTick cancel request
    synchronous runs resolve path tick

theorem ParkedCancel.delivered_clears (cancel : ParkedCancel parked subtask) (pending : PendingAt parked.store subtask index) :
    ∃ record, cancel.resumed.store.subtask? subtask = some record ∧ record.common.pending = none ∧
      record.lenders = none ∧ record.state = .returned ∧ record.index = some index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.cancelClears cancel pending

/-- After committing a result, a cancel callout on the same live subtask can
deliver the result without a poll or event buffer. The publication is retained. -/
theorem LinkedResolution.then_cancel (resolve : LinkedResolution initial subtask index) {between}
    (path : Retaining profile ready (specDispatch ready impl) subtask index resolve.committed between parked)
    (cancel : ParkedCancel parked subtask) (available : CancelAvailable parked.store subtask) :
    Steps profile ready (specDispatch ready impl) initial ((List.replicate 17 .tau ++ between) ++ List.replicate 15 .tau)
      cancel.resumed :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resolutionCancel resolve path cancel available

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery
