module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.AsyncRef

/-- The two released callback-loop routes, with the arena identity selected by
the reached handle lookup for WAIT. -/
inductive CallbackWaitKind where
  | yield
  | wait (set : WsetId)

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

structure CallbackWait (grow : SingleThreaded.GrowOracle) (sig : Signature) where
  thread : ThreadId
  taskId : TaskId
  task : Task (core3 grow)
  kind : CallbackWaitKind
  segments : List (Seg (core3 grow) (HostState sig))

def CallbackWait.site (wait : CallbackWait grow sig) : WaitSite :=
  match wait.kind with
  | .yield => .callbackYield
  | .wait _ => .callbackWait

def CallbackWait.condition (wait : CallbackWait grow sig) : ReadyCond :=
  match wait.kind with
  | .yield => .exclusiveFree wait.task.inst
  | .wait set => .callbackWait wait.task.inst wait.taskId set

def CallbackWait.released (wait : CallbackWait grow sig) (store : CStore (core3 grow)) : CStore (core3 grow) :=
  let store := LiftSt.releaseCallbackSt wait.task.inst wait.thread store
  match wait.kind with
  | .yield => store
  | .wait set => store.wsetIncWaitingSt set

def CallbackWait.decrement (wait : CallbackWait grow sig) (store : CStore (core3 grow)) : CStore (core3 grow) :=
  match wait.kind with
  | .yield => store
  | .wait set => store.wsetDecWaitingSt set

def CallbackWait.afterCore (wait : CallbackWait grow sig) (values : List FlatValue) :
    Session grow sig (Ret (core3 grow)) :=
  match values with
  | [packed] => do
    let (code, index) ← Canon.unpackCallbackResult (flatNat packed)
    callRet (.loop (.callbackLoop wait.taskId wait.thread code.toNat index))
  | _ => internal "canon_lift: callback must return one value"

def CallbackWait.invoke (wait : CallbackWait grow sig) (event : EventTuple) : Session grow sig (Ret (core3 grow)) := do
  let callback ← orTrap (.internal "canon_lift: callback option missing") wait.task.opts.callback
  callCore callback (event.callbackArgs.map i32Flat) >>= wait.afterCore

def CallbackWait.suffix (wait : CallbackWait grow sig) : Session grow sig (Ret (core3 grow)) := do
    let event ← (match wait.kind with
      | .yield => do
        if ← Task.deliverPendingCancel wait.taskId then pure EventTuple.taskCancelled else pure EventTuple.none
      | .wait set => do
        modifyStore (fun store => store.wsetDecWaitingSt set)
        if ← Task.deliverPendingCancel wait.taskId then pure EventTuple.taskCancelled else wsetGetPendingEvent set :
      Session grow sig EventTuple)
    modifyStore (LiftSt.retakeCallbackSt wait.task.inst wait.thread)
    wait.invoke event

def CallbackWait.saved (wait : CallbackWait grow sig) : Activation (core3 grow) (HostState sig) :=
  ⟨some wait.thread, .prog wait.suffix, wait.segments⟩

def CallbackWait.entry (wait : CallbackWait grow sig) (start : Config (core3 grow) (HostState sig))
    (rest : List (Activation (core3 grow) (HostState sig))) : Config (core3 grow) (HostState sig) :=
  { start with
    store := wait.released start.store
    ctl := ⟨some wait.thread, .prog (Thread.waitUntilGuest wait.site wait.condition >>= fun () => wait.suffix),
      wait.segments⟩ :: rest }

def CallbackWait.blocked (wait : CallbackWait grow sig) (start : Config (core3 grow) (HostState sig))
    (rest : List (Activation (core3 grow) (HostState sig))) : Config (core3 grow) (HostState sig) :=
  { (start.setCont wait.thread (some wait.saved)) with
    store := StepDefs.threadStatusSt wait.thread .blocked ((wait.released start.store).startWaitingSt wait.thread wait.condition),
    ctl := rest }

def CallbackWait.parkLabels (wait : CallbackWait grow sig) (available : Bool) :
    List (Label (core3 grow) (HostState sig)) :=
  [.tau, .tau] ++ (if available then [.choice (.earlyReturn wait.site) false] else []) ++ [.tau, .tau]

def CallbackWait.cancelledStore (wait : CallbackWait grow sig) (store : CStore (core3 grow)) : CStore (core3 grow) :=
  LiftSt.retakeCallbackSt wait.task.inst wait.thread ((wait.decrement store).setTaskState wait.taskId .cancelDelivered)

def CallbackWait.cancelSteps (wait : CallbackWait grow sig) : Nat :=
  match wait.kind with
  | .yield => 4
  | .wait _ => 5

def CallbackWait.called (wait : CallbackWait grow sig) (reached : Config (core3 grow) (HostState sig))
    (callback : (core3 grow).FuncAddr) (rest : List (Activation (core3 grow) (HostState sig))) :
    Config (core3 grow) (HostState sig) :=
  { reached with
    store := wait.cancelledStore reached.store
    ctl := ⟨some wait.thread, .core ((core3 grow).invoke callback (EventTuple.taskCancelled.callbackArgs.map i32Flat))
      wait.afterCore, wait.segments⟩ :: rest }

/-- Classify a reached normal Core return using the canonical callback ABI.
A Core execution trap is separate from an invalid successful Core return. -/
def callbackReturn (values : List FlatValue) : Except TrapReason (CallbackCode × Nat) :=
  match values with
  | [packed] =>
    match AsyncRef.unpackCallbackResult (flatNat packed) with
    | some next => .ok next
    | none => .error .unsupportedCallbackCode
  | _ => .error (.internal "canon_lift: callback must return one value")

def CallbackWait.nextIteration (wait : CallbackWait grow sig) (reached : Config (core3 grow) (HostState sig))
    (next : CallbackCode × Nat) (rest : List (Activation (core3 grow) (HostState sig))) :
    Config (core3 grow) (HostState sig) :=
  { reached with ctl := ⟨some wait.thread, .prog (callbackLoopBody .spec wait.taskId wait.thread next.1.toNat next.2),
    .prog (fun returned => .pure returned) :: wait.segments⟩ :: rest }

def CallbackWaitKind.code : CallbackWaitKind → CallbackCode
  | .yield => .yield
  | .wait _ => .wait

def CallbackWaitKind.entrySteps : CallbackWaitKind → Nat
  | .yield => 3
  | .wait _ => 6

def CallbackWait.readyAt (wait : CallbackWait grow sig) (start : Config (core3 grow) (HostState sig)) : Bool :=
  wait.condition.eval (fun _ => false) (wait.released start.store)

def CallbackWait.selected (wait : CallbackWait grow sig) (start : Config (core3 grow) (HostState sig))
    (index : Nat) : Prop :=
  match wait.kind with
  | .yield => True
  | .wait set => ∃ inst, (LiftSt.releaseCallbackSt wait.task.inst wait.thread start.store).inst? wait.task.inst = some inst ∧
      inst.handles.get? index = some (.wset set)

def CallbackWait.followingWait (wait : CallbackWait grow sig) (task : Task (core3 grow))
    (kind : CallbackWaitKind) : CallbackWait grow sig :=
  { wait with task, kind, segments := .prog (fun returned => .pure returned) :: wait.segments }

def CallbackWait.exitComplete (wait : CallbackWait grow sig) (reached : Config (core3 grow) (HostState sig))
    (live : Task (core3 grow)) (slot : Nat) (rest : List (Activation (core3 grow) (HostState sig))) :
    Config (core3 grow) (HostState sig) :=
  let unregistered := reached.store.unregisterThreadSt wait.taskId wait.thread slot
  { reached with
    store := if live.ft.async_ && live.needsExclusive then
      ArenaField.insts.modify unregistered live.inst (InstState.withExclusive none)
    else unregistered
    ctl := ⟨some wait.thread, .prog (.pure .unit), wait.segments⟩ :: rest }

/-- A callback's actual callout to its own instance's canonical task.cancel. -/
structure CallbackCancelImport (wait : CallbackWait grow sig) (reached : Config (core3 grow) (HostState sig)) where
  core : (core3 grow).Thread (CanonHost (core3 grow))
  rest : List (Activation (core3 grow) (HostState sig))
  liveTask : Task (core3 grow)
  liveThread : Thread
  liveInst : InstState
  focused : reached.ctl = ⟨some wait.thread, .core core wait.afterCore, wait.segments⟩ :: rest
  callout : (core3 grow).status reached.store.core core = .callout (.builtin .taskCancel liveTask.inst) []
  threadRecord : ArenaField.threads.get? reached.store wait.thread = some liveThread
  taskIdentity : liveThread.task = wait.taskId
  taskRecord : reached.store.task? wait.taskId = some liveTask
  instRecord : reached.store.inst? liveTask.inst = some liveInst
  mayLeave : liveInst.mayLeave = true
  asyncOpts : liveTask.opts.async_ = true
  delivered : liveTask.state = .cancelDelivered

variable {wait : CallbackWait grow sig} {reached : Config (core3 grow) (HostState sig)}

def CallbackCancelImport.afterResolve (_ : CallbackCancelImport wait reached)
    (result : Ret (core3 grow)) : Session grow sig (Ret (core3 grow)) :=
  match result with
  | .unit => modifyStore (CStore.setTaskState wait.taskId .resolved) >>= fun () => pure (.flat [])
  | _ => internal "late-bound call: expected Ret.unit"

def CallbackCancelImport.resolveEntry (entry : CallbackCancelImport wait reached) : Config (core3 grow) (HostState sig) :=
  { reached with ctl := ⟨some wait.thread, .prog (callerOnResolve .spec .none entry.liveTask.caller none),
    .prog entry.afterResolve :: .core entry.core wait.afterCore :: wait.segments⟩ :: entry.rest }

def CallbackCancelImport.resumed (entry : CallbackCancelImport wait reached) {subtask : SubtaskId}
    (resolution : LowerCancelResolution reached.store entry.liveTask.caller subtask) : Config (core3 grow) (HostState sig) :=
  let store := resolution.resolvedStore.setTaskState wait.taskId .resolved
  { reached with
    store := store
    ctl := ⟨some wait.thread, .core ((core3 grow).resume store.core entry.core (.values []))
      wait.afterCore, wait.segments⟩ :: entry.rest }

/-- A cut of the same running callback with the reached Core store and
thread, but the original component continuation and resumer. -/
def CallbackWait.coreAt (wait : CallbackWait grow sig) (base : Config (core3 grow) (HostState sig))
    (coreStore : (core3 grow).Store (CanonHost (core3 grow)))
    (core : (core3 grow).Thread (CanonHost (core3 grow)))
    (rest : List (Activation (core3 grow) (HostState sig))) : Config (core3 grow) (HostState sig) :=
  { base with
    store := { base.store with core := coreStore }
    ctl := ⟨some wait.thread, .core core wait.afterCore, wait.segments⟩ :: rest }

/-- The ready branch enters the same suffix as resumption, without
installing a saved continuation or changing the thread's wait status. -/
def CallbackWait.early (wait : CallbackWait grow sig) (start : Config (core3 grow) (HostState sig))
    (rest : List (Activation (core3 grow) (HostState sig))) : Config (core3 grow) (HostState sig) :=
  { start with
    store := wait.released start.store
    ctl := wait.saved :: rest }

def CallbackWait.eventCall (wait : CallbackWait grow sig) (base : Config (core3 grow) (HostState sig))
    (store : CStore (core3 grow)) (callback : (core3 grow).FuncAddr) (event : EventTuple)
    (rest : List (Activation (core3 grow) (HostState sig))) : Config (core3 grow) (HostState sig) :=
  { base with
    store := LiftSt.retakeCallbackSt wait.task.inst wait.thread store
    ctl := ⟨some wait.thread, .core ((core3 grow).invoke callback (event.callbackArgs.map i32Flat))
      wait.afterCore, wait.segments⟩ :: rest }

def CallbackWait.shuffled (wait : CallbackWait grow sig) (store : CStore (core3 grow)) (set : WsetId)
    (record : WaitableSet) (permutation : List Nat) : CStore (core3 grow) :=
  (wait.decrement store).wsetSetElemsSt set (applyPerm permutation record.elems)

/-- A reached forced resume of the callback, separate from its scheduler
selection and the subsequent cancellation or event read. -/
structure CallbackResume (wait : CallbackWait grow sig) (atResume : Config (core3 grow) (HostState sig)) where
  thread : Option ThreadId
  next : Session grow sig (Ret (core3 grow))
  segments : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  focused : atResume.ctl = ⟨thread, .prog (Thread.resume wait.thread >>= fun () => next), segments⟩ :: rest

variable {atResume : Config (core3 grow) (HostState sig)}

def CallbackResume.tail (resume : CallbackResume wait atResume) : List (Activation (core3 grow) (HostState sig)) :=
  ⟨resume.thread, .prog resume.next, resume.segments⟩ :: resume.rest

def CallbackResume.labels (_ : CallbackResume wait atResume) : List (Label (core3 grow) (HostState sig)) :=
  List.replicate (if atResume.store.threadIs Thread.waiting wait.thread then 3 else 2) .tau

def CallbackResume.resumed (resume : CallbackResume wait atResume) : Config (core3 grow) (HostState sig) :=
  let store := if atResume.store.threadIs Thread.waiting wait.thread then atResume.store.stopWaitingSt wait.thread
    else atResume.store
  { (atResume.setCont wait.thread none) with
    store := StepDefs.threadStatusSt wait.thread .running store
    ctl := wait.saved :: resume.tail }

def CallbackWait.tickResume (wait : CallbackWait grow sig) {atHost : Config (core3 grow) (HostState sig)}
    {ready : HostReady (HostState sig)} {profile : ProfileKind} (tick : SelectedTick wait.thread atHost ready profile) :
    CallbackResume wait tick.atResume :=
  ⟨none, modifyStore StepDefs.leaveHostSt >>= fun () => pure .unit, [], [], rfl⟩

/-- Finite callback fragments made from actual Core steps and reached canonical
loop entries, parks and resumes. K3 may deliver another waitable, not the tracked subtask.
One may stop while Core is still running; no eventual return is required. -/
inductive ClosedCallbackPrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (impl : HostImpl (core3 grow) (HostState sig)) (target : SubtaskId) :
    Config (core3 grow) (HostState sig) → List (Label (core3 grow) (HostState sig)) →
      Config (core3 grow) (HostState sig) → Prop where
  | done (state : Config (core3 grow) (HostState sig)) : ClosedCallbackPrefix profile ready impl target state [] state
  | core {start cut last labels} (wait : CallbackWait grow sig) {rest count core}
      (focused : start.ctl = ⟨some wait.thread, .core core wait.afterCore, wait.segments⟩ :: rest)
      (run : Steps profile ready (specDispatch ready impl) start (List.replicate count .core) cut)
      (tail : ClosedCallbackPrefix profile ready impl target cut labels last) :
      ClosedCallbackPrefix profile ready impl target start (List.replicate count .core ++ labels) last
  | nextWait {start last labels} (wait : CallbackWait grow sig) {rest core values}
      (focused : start.ctl = ⟨some wait.thread, .core core wait.afterCore, wait.segments⟩ :: rest)
      (returned : (core3 grow).status start.store.core core = .returned (.values values))
      {kind : CallbackWaitKind} {index : Nat} (decoded : callbackReturn values = .ok (kind.code, index))
      {task : Task (core3 grow)} (live : start.store.task? wait.taskId = some task)
      (noCancel : task.state ≠ .pendingCancel) (selected : (wait.followingWait task kind).selected start index)
      (tail : ClosedCallbackPrefix profile ready impl target
        ((wait.followingWait task kind).entry (wait.nextIteration start (kind.code, index) rest) rest) labels last) :
      ClosedCallbackPrefix profile ready impl target start
        (([.tau, .tau] ++ List.replicate kind.entrySteps .tau) ++ labels) last
  | early {start last labels} (wait : CallbackWait grow sig) {rest}
      (available : wait.readyAt start = true) (early : Allowed profile (.earlyReturn wait.site) true)
      (tail : ClosedCallbackPrefix profile ready impl target (wait.early start rest) labels last) :
      ClosedCallbackPrefix profile ready impl target (wait.entry start rest)
        ([.tau, .tau, .choice (.earlyReturn wait.site) true] ++ labels) last
  | park {start last labels} (wait : CallbackWait grow sig) {rest available}
      (availability : wait.readyAt start = available)
      (tail : ClosedCallbackPrefix profile ready impl target (wait.blocked start rest) labels last) :
      ClosedCallbackPrefix profile ready impl target (wait.entry start rest) (wait.parkLabels available ++ labels) last
  | resume {wait : CallbackWait grow sig} {atResume last labels} (resume : CallbackResume wait atResume)
      (saved : atResume.cont? wait.thread = some wait.saved)
      (tail : ClosedCallbackPrefix profile ready impl target resume.resumed labels last) :
      ClosedCallbackPrefix profile ready impl target atResume (resume.labels ++ labels) last
  | tick {atHost last labels} (wait : CallbackWait grow sig) (tick : SelectedTick wait.thread atHost ready profile)
      (saved : atHost.cont? wait.thread = some wait.saved)
      (tail : ClosedCallbackPrefix profile ready impl target (wait.tickResume tick).resumed labels last) :
      ClosedCallbackPrefix profile ready impl target atHost
        ((tick.selectionLabels ++ (wait.tickResume tick).labels) ++ labels) last
  | yieldNone {reached last labels} (wait : CallbackWait grow sig) {rest} (kind : wait.kind = .yield)
      (focused : reached.ctl = wait.saved :: rest)
      {task : Task (core3 grow)} (live : reached.store.task? wait.taskId = some task)
      (noCancel : task.state ≠ .pendingCancel)
      {callback : (core3 grow).FuncAddr} (chosen : wait.task.opts.callback = some callback)
      (tail : ClosedCallbackPrefix profile ready impl target
        (wait.eventCall reached reached.store callback .none rest) labels last) :
      ClosedCallbackPrefix profile ready impl target reached (List.replicate 3 .tau ++ labels) last
  | waitOther {reached last labels} (wait : CallbackWait grow sig) {rest set} (kind : wait.kind = .wait set)
      (focused : reached.ctl = wait.saved :: rest)
      {task : Task (core3 grow)} (live : reached.store.task? wait.taskId = some task)
      (noCancel : task.state ≠ .pendingCancel)
      {record : WaitableSet} (setLive : (wait.decrement reached.store).wset? set = some record)
      {permutation : List Nat} (allowed : Allowed profile (.shuffle record.elems.length) permutation)
      {selected : Waitable} (selects : (applyPerm permutation record.elems).find?
        (wait.shuffled reached.store set record permutation).waitableHasEvent = some selected)
      {taken : CStore (core3 grow)} {event : EventTuple}
      (take : (wait.shuffled reached.store set record permutation).takeWaitableEvent selected = (taken, some event))
      {callback : (core3 grow).FuncAddr} (chosen : wait.task.opts.callback = some callback)
      (other : selected ≠ .subtask target)
      (tail : ClosedCallbackPrefix profile ready impl target
        (wait.eventCall reached taken callback event rest) labels last) :
      ClosedCallbackPrefix profile ready impl target reached
        ((List.replicate 3 .tau ++ [.choice (.shuffle record.elems.length) permutation] ++ List.replicate 6 .tau) ++ labels) last

/-- The reached registration and ABI return needed for a resolved callback
to exit, with every loop continuation accounted for. -/
structure CallbackExit (wait : CallbackWait grow sig) (cut : Config (core3 grow) (HostState sig)) where
  core : (core3 grow).Thread (CanonHost (core3 grow))
  rest : List (Activation (core3 grow) (HostState sig))
  values : List FlatValue
  index : Nat
  depth : Nat
  task : Task (core3 grow)
  thread : Thread
  slot : Nat
  instance_ : InstState
  removed : InstState
  focused : cut.ctl = ⟨some wait.thread, .core core wait.afterCore, wait.segments⟩ :: rest
  returned : (core3 grow).status cut.store.core core = .returned (.values values)
  decoded : callbackReturn values = .ok (.exit, index)
  taskLive : cut.store.task? wait.taskId = some task
  implicitThread : task.implicitThread = some wait.thread
  resolved : task.state = .resolved
  threadLive : ArenaField.threads.get? cut.store wait.thread = some thread
  threadIndex : thread.index = some slot
  instanceLive : cut.store.inst? task.inst = some instance_
  remove : instance_.removeThread? slot = some (wait.thread, removed)
  frames : wait.segments = List.replicate depth (.prog (fun returned => .pure returned))

def CallbackWait.exitFrame (wait : CallbackWait grow sig) : CallbackWait grow sig :=
  { wait with segments := .prog (fun returned => .pure returned) :: wait.segments }

def CallbackExit.unregistered {cut : Config (core3 grow) (HostState sig)} (exit : CallbackExit wait cut) :
    Config (core3 grow) (HostState sig) :=
  wait.exitFrame.exitComplete (wait.nextIteration cut (.exit, exit.index) exit.rest)
    exit.task exit.slot exit.rest

def CallbackExit.unwound {cut : Config (core3 grow) (HostState sig)} (exit : CallbackExit wait cut) :
    Config (core3 grow) (HostState sig) :=
  { exit.unregistered with store := StepDefs.threadStatusSt wait.thread .exited exit.unregistered.store, ctl := exit.rest }

def CallbackExit.labels {cut : Config (core3 grow) (HostState sig)} (exit : CallbackExit wait cut) :
    List (Label (core3 grow) (HostState sig)) :=
  [.tau, .tau] ++ List.replicate (5 + (exit.task.ft.async_ && exit.task.needsExclusive).toNat) .tau ++
    List.replicate (exit.depth + 2) .tau

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery
