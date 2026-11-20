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

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery
