module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Callback.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Callback
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackDelivery

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.AsyncRef
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start reached parked : Config (core3 grow) (HostState sig)}
  {thread : ThreadId} {taskId : TaskId} {task : Task (core3 grow)}
  {segments : List (Seg (core3 grow) (HostState sig))} {rest : List (Activation (core3 grow) (HostState sig))}

/-- With no cancellation on entry, the actual YIELD branch releases the
exclusive callback lock before testing K2. -/
theorem callback_yield_entry {index : Nat}
    (focused : start.ctl = ⟨some thread, .prog (callbackLoopBody .spec taskId thread CallbackCode.yield.toNat index), segments⟩ :: rest)
    (live : start.store.task? taskId = some task) (noCancel : task.state ≠ .pendingCancel) :
    Steps profile ready (specDispatch ready impl) start (List.replicate 3 .tau)
      ((⟨thread, taskId, task, .yield, segments⟩ : CallbackWait grow sig).entry start rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.callbackYieldEntry focused live noCancel

/-- The actual WAIT branch selects the arena waitable set after releasing the
lock, then increments its wait count before testing K3. -/
theorem callback_wait_entry {index : Nat} {set : WsetId} {inst : InstState}
    (focused : start.ctl = ⟨some thread, .prog (callbackLoopBody .spec taskId thread CallbackCode.wait.toNat index), segments⟩ :: rest)
    (live : start.store.task? taskId = some task) (noCancel : task.state ≠ .pendingCancel)
    (instanceLive : (LiftSt.releaseCallbackSt task.inst thread start.store).inst? task.inst = some inst)
    (selected : inst.handles.get? index = some (.wset set)) :
    Steps profile ready (specDispatch ready impl) start (List.replicate 6 .tau)
      ((⟨thread, taskId, task, .wait set, segments⟩ : CallbackWait grow sig).entry start rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.callbackWaitEntry focused live noCancel instanceLive selected

/-- Both branches install their actual continuation. A ready condition takes
the profile-permitted non-early choice; an unready one makes no choice. -/
theorem CallbackWait.parks (wait : CallbackWait grow sig) {available : Bool}
    (availability : wait.condition.eval (fun _ => false) (wait.released start.store) = available) :
    Steps profile ready (specDispatch ready impl) (wait.entry start rest) (wait.parkLabels available)
      (wait.blocked start rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.callbackBlocks wait availability

/-- On the reached saved suffix, cancellation wins over waitable selection.
K3 decrements the waiter count first; both routes deliver the pending cancel,
retake the callback lock and invoke the real Core function with TASK_CANCELLED. -/
theorem CallbackWait.cancel_calls_core (wait : CallbackWait grow sig) {liveTask : Task (core3 grow)}
    {callback : (core3 grow).FuncAddr} (focused : reached.ctl = wait.saved :: rest)
    (live : reached.store.task? wait.taskId = some liveTask) (pending : liveTask.state = .pendingCancel)
    (chosen : wait.task.opts.callback = some callback) :
    Steps profile ready (specDispatch ready impl) reached (List.replicate wait.cancelSteps .tau)
      (wait.called reached callback rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.callbackCancelCore wait focused live pending chosen

/-- Ready started reentry uses the tracked occurrence and the live task from
the marked store. The original cancellation caller remains below the Core
callback; neither Core return nor event delivery is asserted. -/
theorem TaskCancelAdmission.started_calls_core {subtask : SubtaskId} {cancel : ParkedCancel parked subtask}
    (request : TaskCancelAdmission cancel) (wait : CallbackWait grow sig)
    (sameThread : wait.thread = request.implicitThread) (sameTask : wait.taskId = request.taskId) {between}
    (path : ParkedPrefix profile ready (specDispatch ready impl) wait.thread (wait.blocked start rest) between parked)
    (started : request.callee.state = .started) (cancellable : request.implicitState.cancellable = true)
    (available : request.markedStore.threadReady (ready parked.host) request.implicitThread = true)
    {callback : (core3 grow).FuncAddr} (chosen : wait.task.opts.callback = some callback) :
    Steps profile ready (specDispatch ready impl) parked
      (List.replicate request.reentrySteps .tau ++ List.replicate wait.cancelSteps .tau)
      (wait.called (request.reentered wait.saved) callback cancel.callbackTail) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.startedCancelCore request wait sameThread sameTask
    path started cancellable available chosen

/-- Classify the values at a reached Core return, not an assumed callback
outcome. A valid result re-enters the actual callback loop with the reached
store and outer frames. Bad arity or an unsupported code traps in place. -/
theorem CallbackWait.core_returned (wait : CallbackWait grow sig) {core : (core3 grow).Thread (CanonHost (core3 grow))}
    {values : List FlatValue}
    (focused : reached.ctl = ⟨some wait.thread, .core core wait.afterCore, wait.segments⟩ :: rest)
    (result : (core3 grow).status reached.store.core core = .returned (.values values)) :
    match callbackReturn values with
    | .ok next => Steps profile ready (specDispatch ready impl) reached [.tau, .tau] (wait.nextIteration reached next rest)
    | .error reason => Steps profile ready (specDispatch ready impl) reached [.tau, .trap reason] (StepDefs.trapCfg reached) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.callbackReturned wait focused result

/-- A trap of the actual Core callback is not an ABI decode or an unresolved
cancellation reply. Lockdown retains the reached store's earlier effects. -/
theorem CallbackWait.core_trapped (wait : CallbackWait grow sig) {core : (core3 grow).Thread (CanonHost (core3 grow))}
    (focused : reached.ctl = ⟨some wait.thread, .core core wait.afterCore, wait.segments⟩ :: rest)
    (result : (core3 grow).status reached.store.core core = .returned .trap) :
    Step profile ready (specDispatch ready impl) reached (.trap .coreTrap) (StepDefs.trapCfg reached) :=
  .coreTrap focused result

/-- An EXIT code cannot discard the last thread of an unresolved task. This
checks the reached task after Core ran, without presuming it resolved. -/
theorem CallbackWait.exit_unresolved (wait : CallbackWait grow sig) {index : Nat} {liveTask : Task (core3 grow)}
    (focused : reached.ctl = ⟨some wait.thread,
      .prog (callbackLoopBody .spec wait.taskId wait.thread CallbackCode.exit.toNat index), wait.segments⟩ :: rest)
    (live : reached.store.task? wait.taskId = some liveTask) (implicitThread : liveTask.implicitThread = some wait.thread)
    (lastThread : (liveTask.threads.erase wait.thread).isEmpty = true) (unresolved : liveTask.state ≠ .resolved) :
    Steps profile ready (specDispatch ready impl) reached [.tau, .tau, .trap .taskNotResolved]
      (StepDefs.trapCfg reached) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.callbackExitUnresolved wait focused live
    implicitThread lastThread unresolved

/-- A valid YIELD or WAIT return can park again. The next iteration reads the
reached task and resolves the reached handle; it does not inherit a waitable
set identity from the preceding iteration. The original resumer stays below
the new saved activation, with no assumption of another return. -/
theorem CallbackWait.core_reparks (wait : CallbackWait grow sig) {core : (core3 grow).Thread (CanonHost (core3 grow))}
    {values : List FlatValue} (focused : reached.ctl = ⟨some wait.thread, .core core wait.afterCore, wait.segments⟩ :: rest)
    (result : (core3 grow).status reached.store.core core = .returned (.values values))
    {kind : CallbackWaitKind} {index : Nat} (decoded : callbackReturn values = .ok (kind.code, index))
    {liveTask : Task (core3 grow)} (live : reached.store.task? wait.taskId = some liveTask)
    (noCancel : liveTask.state ≠ .pendingCancel) (selected : (wait.followingWait liveTask kind).selected reached index) :
    let entry := wait.nextIteration reached (kind.code, index) rest
    let following := wait.followingWait liveTask kind
    Steps profile ready (specDispatch ready impl) reached
      ([.tau, .tau] ++ (List.replicate kind.entrySteps .tau ++ following.parkLabels (following.readyAt entry)))
      (following.blocked entry rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.callbackReparks wait focused result decoded live
    noCancel selected

/-- The resolved EXIT route unregisters the reached implicit thread and
releases its exclusive lock when required. It does not consume a subtask event. -/
theorem CallbackWait.exit_resolved (wait : CallbackWait grow sig) {index : Nat} {liveTask : Task (core3 grow)}
    (focused : reached.ctl = ⟨some wait.thread,
      .prog (callbackLoopBody .spec wait.taskId wait.thread CallbackCode.exit.toNat index), wait.segments⟩ :: rest)
    (live : reached.store.task? wait.taskId = some liveTask) (implicitThread : liveTask.implicitThread = some wait.thread)
    (resolved : liveTask.state = .resolved) {threadState : Thread} {slot : Nat}
    (threadLive : ArenaField.threads.get? reached.store wait.thread = some threadState)
    (threadIndex : threadState.index = some slot) {inst removed : InstState}
    (instanceLive : reached.store.inst? liveTask.inst = some inst)
    (remove : inst.removeThread? slot = some (wait.thread, removed)) :
    Steps profile ready (specDispatch ready impl) reached
      (List.replicate (5 + (liveTask.ft.async_ && liveTask.needsExclusive).toNat) .tau)
      (wait.exitComplete reached liveTask slot rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.callbackExitResolved wait focused live
    implicitThread resolved threadLive threadIndex instanceLive remove

/-- Pop every identity continuation left by the reached loop iterations, and
then return control to the resumer without fabricating a cancellation reply. -/
theorem unwind_callback (depth : Nat)
    (focused : reached.ctl = ⟨some thread, .prog (.pure .unit),
      List.replicate depth (.prog (fun returned => .pure returned))⟩ :: rest) :
    Steps profile ready (specDispatch ready impl) reached (List.replicate (depth + 1) .tau)
      { reached with store := StepDefs.threadStatusSt thread .exited reached.store, ctl := rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.unwindCallback depth focused

/-- The actual task.cancel import reads the reached callback task. A live
borrow traps before resolution; otherwise the machine enters onResolve(none)
above the original Core callback invocation. -/
theorem CallbackCancelImport.enters_resolution {wait : CallbackWait grow sig} (entry : CallbackCancelImport wait reached) :
    (entry.liveTask.numBorrows = 0 → Steps profile ready (specDispatch ready impl) reached
      (List.replicate 9 .tau) entry.resolveEntry) ∧
    (entry.liveTask.numBorrows > 0 → Steps profile ready (specDispatch ready impl) reached
      (List.replicate 8 .tau ++ [.trap .borrowsRemain]) (StepDefs.trapCfg reached)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.callbackCancelImport entry

/-- Resolve the reached indexed started subtask, then return the empty
task.cancel results to the callback. The cancelled event remains pending and
the subtask's lenders are still attached; neither is delivered by this callout. -/
theorem CallbackCancelImport.resolves_started {wait : CallbackWait grow sig} (entry : CallbackCancelImport wait reached)
    (empty : entry.liveTask.numBorrows = 0)
    {subtask : SubtaskId} (resolution : LowerCancelResolution reached.store entry.liveTask.caller subtask)
    (started : resolution.record.state = .started) {index : Nat} (indexed : resolution.record.index = some index) :
    Steps profile ready (specDispatch ready impl) reached
      (List.replicate 9 .tau ++ List.replicate (resolution.callbackSteps + 1) .tau) (entry.resumed resolution) ∧
    (entry.resumed resolution).store.subtask? subtask = some resolution.resolvedRecord ∧
    resolution.resolvedRecord.state = .cancelledBeforeReturned ∧ resolution.resolvedRecord.index = some index ∧
    resolution.resolvedRecord.common.pending = some (.subtask subtask) ∧
    resolution.resolvedRecord.lenders = resolution.record.lenders :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.callbackCancelStarted entry empty resolution started indexed

/-- Every finite host-free prefix of the focused Core callback keeps its
component continuation, resumer and component arenas. The Core store can change. -/
theorem CallbackWait.core_only_cut (wait : CallbackWait grow sig)
    {core : (core3 grow).Thread (CanonHost (core3 grow))} {count : Nat}
    (focused : start.ctl = ⟨some wait.thread, .core core wait.afterCore, wait.segments⟩ :: rest)
    (run : Steps profile ready (specDispatch ready impl) start (List.replicate count .core) reached) :
    ∃ next, reached = wait.coreAt start reached.store.core next rest :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.callbackCoreOnlyCut wait focused run

/-- After the reached task.cancel import, a finite host-free Core suffix
returning EXIT unregisters the callback and retains its pending event until
the original cancellation caller takes it and releases the lends. This does
not assert callback return, or cover intervening imports or wait iterations. -/
theorem CallbackCancelImport.delivers_started {wait : CallbackWait grow sig}
    (entry : CallbackCancelImport wait reached) {subtask : SubtaskId}
    (cancel : ParkedCancel parked subtask)
    (empty : entry.liveTask.numBorrows = 0)
    (resolution : LowerCancelResolution reached.store entry.liveTask.caller subtask)
    (started : resolution.record.state = .started) {index slot depth : Nat} {removed : InstState}
    (indexed : resolution.record.index = some index)
    (resumer : entry.rest = cancel.callbackTail)
    (implicitThread : entry.liveTask.implicitThread = some wait.thread)
    (threadIndex : entry.liveThread.index = some slot)
    (remove : entry.liveInst.removeThread? slot = some (wait.thread, removed))
    (identityFrames : wait.segments = List.replicate depth (.prog (fun returned => .pure returned)))
    {cut : Config (core3 grow) (HostState sig)} {count : Nat}
    (run : Steps profile ready (specDispatch ready impl) (entry.resumed resolution) (List.replicate count .core) cut)
    {core : (core3 grow).Thread (CanonHost (core3 grow))} {values : List FlatValue} {exitIndex : Nat}
    (focused : cut.ctl = ⟨some wait.thread, .core core wait.afterCore, wait.segments⟩ :: entry.rest)
    (returned : (core3 grow).status cut.store.core core = .returned (.values values))
    (decoded : callbackReturn values = .ok (.exit, exitIndex)) :
    ∃ exited,
      Steps profile ready (specDispatch ready impl) reached
        (List.replicate 9 .tau ++ List.replicate (resolution.callbackSteps + 1) .tau ++ List.replicate count .core ++
          List.replicate (depth + 9 + (entry.liveTask.ft.async_ && entry.liveTask.needsExclusive).toNat) .tau) exited ∧
      exited.store.subtask? subtask = some resolution.resolvedRecord ∧
      Steps profile ready (specDispatch ready impl) exited (List.replicate 8 .tau)
        (cancel.cancelledReply exited .cancelledBeforeReturned) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.callbackCancelDeliversStarted entry cancel
    empty resolution started indexed resumer implicitThread threadIndex remove identityFrames run focused returned decoded

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery
