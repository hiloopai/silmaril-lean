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

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery
