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

theorem take_event_other (store : CStore (core3 grow)) (selected : Waitable) (target : SubtaskId)
    (other : selected ≠ .subtask target) :
    (store.takeWaitableEventSt selected).subtask? target = store.subtask? target :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.takeEvent_other store selected target other

/-- A selected resolved subtask clears its event and releases the recorded
lends, without changing the subtask's resolution code or numeric index. -/
theorem take_pending_resolution (store : CStore (core3 grow)) (record : Subtask)
    (live : store.subtask? subtask = some record) (resolved : record.state.resolved = true)
    (pending : record.common.pending = some (.subtask subtask)) :
    store.takeWaitableEvent (.subtask subtask) =
      (cancelDelivered store subtask, some ⟨.subtask, record.index.getD 0, record.state.toNat⟩) ∧
    (cancelDelivered store subtask).subtask? subtask = some { record with
      common := { record.common with pending := none }, lenders := none } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.takePendingResolution store record live resolved pending

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

/-- A poll uses the event in the reached store; its producer need not be
part of the same proof or leave the event pending throughout an earlier path. -/
theorem ParkedPoll.delivers_returned (poll : ParkedPoll parked subtask profile)
    (pending : PendingAt parked.store subtask index) : poll.steps index ready impl parked [] :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.pollReturned poll pending

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

/-- The reached scheduler choice enters `Thread.resume` for the selected thread. -/
theorem SelectedTick.selects_thread {atHost : Config (core3 grow) (HostState sig)} {thread : ThreadId}
    (tick : SelectedTick thread atHost ready profile) :
    Steps profile ready (specDispatch ready impl) atHost tick.selectionLabels tick.atResume :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.selectTick tick

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

/-- Selection and occurrence tracking are separate: this rule starts at the
reached resume and checks the original saved activation in that state. -/
theorem WaitResume.resumes {atResume : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
    (resume : WaitResume wait atResume) (saved : atResume.cont? wait.thread = some wait.saved) :
    Steps profile ready (specDispatch ready impl) atResume (List.replicate 4 .tau) resume.reached :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resumeWait resume saved

/-- Once a wait reaches its selection program, consume from that state, not
from the store when the wait was started or parked. -/
theorem WaitDelivery.at_selection {wait : ParkedWait parked} (delivery : WaitDelivery wait initial profile subtask)
    (focused : initial.ctl = ⟨some wait.thread, .prog wait.takeEvent,
      .core wait.core wait.next :: wait.segments⟩ :: initial.ctl.drop 1)
    (pending : PendingAt initial.store subtask index) : delivery.outcomes index ready impl initial [] :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.waitDeliveryAtSelection delivery focused pending

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

/-- An unready K1 wait installs the canonical backpressure continuation
without an early-return choice. -/
theorem K1Wait.blocks {atWait : Config (core3 grow) (HostState sig)} {thread : ThreadId} {taskId : TaskId}
    (wait : K1Wait atWait thread taskId) (unready : wait.condition.eval (fun _ => false) wait.incremented = false) :
    Steps profile ready (specDispatch ready impl) atWait (List.replicate 5 .tau) wait.blocked :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.k1Blocks wait unready

/-- Reach the K1 wait from the canonical lifted thread body, not an assumed
wait continuation. Cancelling the gate skips registration and the callee body. -/
theorem lift_k1_gate {atGate : Config (core3 grow) (HostState sig)} {thread : ThreadId} {taskId : TaskId}
    (callee : (core3 grow).FuncAddr) (task : Task (core3 grow)) (instance_ : InstState)
    (rest : List (Activation (core3 grow) (HostState sig)))
    (focused : atGate.ctl = ⟨some thread, .prog (liftThreadBody .spec .none taskId callee), []⟩ :: rest)
    (liveTask : atGate.store.task? taskId = some task) (asynchronous : task.ft.async_ = true)
    (liveInst : atGate.store.inst? task.inst = some instance_)
    (gated : (instance_.hasBackpressure task.needsExclusive || decide (instance_.numWaitingToEnter > 0)) = true) :
    ∃ entry : K1GateEntry atGate thread taskId,
      Steps profile ready (specDispatch ready impl) atGate (List.replicate 4 .tau) entry.waitingEntry ∧
      entry.wait.next false = .pure .unit ∧ entry.wait.segments = [] ∧ entry.next = liftAdmissionTail taskId callee :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.liftK1Gate
    callee task instance_ rest focused liveTask asynchronous liveInst gated

/-- Initial cancellation forces the same installed K1 continuation, decrements
the reached instance count and delivers cancellation to the task. Outstanding
borrows trap after those effects, rather than resolving or rolling them back. -/
theorem TaskCancelAdmission.initial_k1 {cancel : ParkedCancel parked subtask}
    {atWait : Config (core3 grow) (HostState sig)} (request : TaskCancelAdmission cancel)
    (wait : K1Wait atWait request.implicitThread request.taskId) {between}
    (path : ParkedPrefix profile ready (specDispatch ready impl) request.implicitThread wait.blocked between parked)
    (initialTask : request.callee.state = .initial) :
    (request.callee.numBorrows = 0 → Steps profile ready (specDispatch ready impl) parked
      (List.replicate request.reentrySteps .tau ++ List.replicate 5 .tau)
      (wait.resolveEntry (request.reentered wait.saved) request.callee.caller ready impl cancel.callbackTail)) ∧
    (request.callee.numBorrows > 0 → Steps profile ready (specDispatch ready impl) parked
      (List.replicate request.reentrySteps .tau ++ (List.replicate 4 .tau ++ [.trap .borrowsRemain]))
      (wait.borrowTrap (request.reentered wait.saved))) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.initialK1Cancel request wait path initialTask

/-- The reached lower callback resolves without lowering a result value. It
releases no lends under the specification dispatcher; a queued event has not yet been consumed. -/
theorem LowerCancelResolution.steps {atWait : Config (core3 grow) (HostState sig)} {thread : ThreadId} {taskId : TaskId}
    {caller : CallerId} (wait : K1Wait atWait thread taskId) (atResume : Config (core3 grow) (HostState sig))
    (resolution : LowerCancelResolution (wait.deliveredStore atResume.store) caller subtask)
    (rest : List (Activation (core3 grow) (HostState sig))) :
    Steps profile ready (specDispatch ready impl) (wait.resolveEntry atResume caller ready impl rest)
      (List.replicate resolution.callbackSteps .tau) (resolution.continued wait atResume rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.k1LowerCancel wait atResume resolution rest

theorem LowerCancelResolution.live_resolved {store : CStore (core3 grow)} {caller : CallerId}
    (resolution : LowerCancelResolution store caller subtask) :
    resolution.resolvedStore.subtask? subtask = some resolution.resolvedRecord :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.lowerCancelRecord resolution

/-- The false lift-entry continuation exits the resolved callee and restores
its resumer. It does not deliver or consume the subtask event. -/
theorem LowerCancelResolution.exits {atWait : Config (core3 grow) (HostState sig)} {thread : ThreadId} {taskId : TaskId}
    {caller : CallerId} (wait : K1Wait atWait thread taskId) (atResume : Config (core3 grow) (HostState sig))
    (resolution : LowerCancelResolution (wait.deliveredStore atResume.store) caller subtask)
    (rest : List (Activation (core3 grow) (HostState sig))) (cancelled : wait.next false = .pure .unit)
    (emptySegments : wait.segments = []) :
    Step profile ready (specDispatch ready impl) (resolution.continued wait atResume rest) .tau
      { atResume with
        store := StepDefs.threadStatusSt thread .exited (resolution.resolvedStore.setTaskState taskId .resolved)
        ctl := rest } :=
  Step.threadExit (r := .unit) (by simp [LowerCancelResolution.continued, cancelled, emptySegments])

theorem LowerCancelResolution.not_pending_return {store : CStore (core3 grow)} {caller : CallerId}
    (resolution : LowerCancelResolution store caller subtask) (index : Nat) :
    ¬ PendingAt resolution.resolvedStore subtask index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.lowerCancelNotReturned resolution index

/-- For a linked starting subtask, derive the reached callback admission from
the tracked K1 frame and the caller record. The cancelled subtask is resolved;
the surrounding cancellation call has not yet delivered its reply. -/
theorem TaskCancelAdmission.initial_k1_resolves {cancel : ParkedCancel parked subtask}
    {atWait : Config (core3 grow) (HostState sig)} (request : TaskCancelAdmission cancel)
    (wait : K1Wait atWait request.implicitThread request.taskId) {between}
    (path : ParkedPrefix profile ready (specDispatch ready impl) request.implicitThread wait.blocked between parked)
    (initialTask : request.callee.state = .initial) (empty : request.callee.numBorrows = 0)
    (starting : request.record.state = .starting)
    {context : LiftLowerContext (core3 grow)} {args position ft maxParams maxResults}
    (linked : ArenaField.callers.get? parked.store request.callee.caller =
      some (.lower subtask context args position ft maxParams maxResults)) :
    ∃ resolution : LowerCancelResolution (wait.deliveredStore (request.reentered wait.saved).store) request.callee.caller subtask,
      Steps profile ready (specDispatch ready impl) parked
        (List.replicate request.reentrySteps .tau ++ List.replicate 5 .tau ++ List.replicate resolution.callbackSteps .tau)
        (resolution.continued wait (request.reentered wait.saved) cancel.callbackTail) ∧
      resolution.resolvedRecord.state = .cancelledBeforeStarted ∧ resolution.record.index = request.record.index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.initialK1Lower request wait path initialTask empty starting linked

/-- After the callback has resolved the subtask, clear the synchronous waiter,
consume the reached cancelled event and return its status to the same Core caller. -/
theorem ParkedCancel.finish_cancelled_callback (cancel : ParkedCancel parked subtask)
    (atExit : Config (core3 grow) (HostState sig)) (record : Subtask) (focused : atExit.ctl = cancel.callbackTail)
    (live : atExit.store.subtask? subtask = some record)
    (cancelled : record.state = .cancelledBeforeStarted ∨ record.state = .cancelledBeforeReturned)
    (pending : record.common.pending = some (.subtask subtask)) :
    Steps profile ready (specDispatch ready impl) atExit (List.replicate 8 .tau) (cancel.cancelledReply atExit record.state) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.cancelCallbackDelivers cancel atExit record
    focused live cancelled pending

/-- Initial K1 cancellation of a linked indexed subtask reaches the actual
callee exit, then consumes the cancelled event and replies to the original Core
caller. The exit cut keeps canonical resolution distinct from delivery. -/
theorem TaskCancelAdmission.initial_k1_delivers {cancel : ParkedCancel parked subtask}
    {atWait : Config (core3 grow) (HostState sig)} (request : TaskCancelAdmission cancel)
    (wait : K1Wait atWait request.implicitThread request.taskId) {between}
    (path : ParkedPrefix profile ready (specDispatch ready impl) request.implicitThread wait.blocked between parked)
    (initialTask : request.callee.state = .initial) (empty : request.callee.numBorrows = 0)
    (starting : request.record.state = .starting) (indexed : request.record.index = some index)
    (cancelledTail : wait.next false = .pure .unit) (emptySegments : wait.segments = [])
    {context : LiftLowerContext (core3 grow)} {args position ft maxParams maxResults}
    (linked : ArenaField.callers.get? parked.store request.callee.caller =
      some (.lower subtask context args position ft maxParams maxResults)) :
    ∃ exited,
      Steps profile ready (specDispatch ready impl) parked
        (List.replicate request.reentrySteps .tau ++ List.replicate 13 .tau ++ [.tau]) exited ∧
      Steps profile ready (specDispatch ready impl) exited (List.replicate 8 .tau)
        (cancel.cancelledReply exited .cancelledBeforeStarted) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.initialK1Delivers request wait path initialTask empty
    starting indexed cancelledTail emptySegments linked

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

theorem SyncCancelResume.resumes {cancel : ParkedCancel parked subtask}
    {atResume : Config (core3 grow) (HostState sig)} (resume : SyncCancelResume cancel atResume)
    (saved : atResume.cont? cancel.thread = some cancel.saved) :
    Steps profile ready (specDispatch ready impl) atResume (List.replicate 3 .tau) resume.reached :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resumeSyncCancel cancel resume saved

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
