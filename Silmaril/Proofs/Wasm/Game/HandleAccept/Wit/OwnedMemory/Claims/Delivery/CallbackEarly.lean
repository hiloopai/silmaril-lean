module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Callback.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.AsyncRef
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall ComponentCall.Delivery

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start reached : Config (core3 grow) (HostState sig)} {liveTask : Task (core3 grow)}
  {rest : List (Activation (core3 grow) (HostState sig))}

theorem callbackEarly (wait : CallbackWait grow sig) (available : wait.readyAt start = true)
    (allowed : Allowed profile (.earlyReturn wait.site) true) :
    Steps profile ready (specDispatch ready impl) (wait.entry start rest)
      [.tau, .tau, .choice (.earlyReturn wait.site) true] (wait.early start rest) := by
  cases kind : wait.kind with
  | yield =>
    have siteEq : wait.site = .callbackYield := by simp [CallbackWait.site, kind]
    rw [congrArg (fun site => .choice (.earlyReturn site) true : WaitSite → Label (core3 grow) (HostState sig)) siteEq]
    simp only [CallbackWait.readyAt, CallbackWait.condition, kind] at available
    simp only [CallbackWait.entry, CallbackWait.condition, CallbackWait.site, kind] at allowed ⊢
    refine .cons (.currentThread rfl) (.cons (.get rfl) ?_)
    simp [Prog.bind, pure, available, Prog.bind_assoc]
    exact .cons (.choose (ck := .earlyReturn .callbackYield) true rfl allowed) (.refl _)
  | wait set =>
    have siteEq : wait.site = .callbackWait := by simp [CallbackWait.site, kind]
    rw [congrArg (fun site => .choice (.earlyReturn site) true : WaitSite → Label (core3 grow) (HostState sig)) siteEq]
    simp only [CallbackWait.readyAt, CallbackWait.condition, kind] at available
    simp only [CallbackWait.entry, CallbackWait.condition, CallbackWait.site, kind] at allowed ⊢
    refine .cons (.currentThread rfl) (.cons (.get rfl) ?_)
    simp [Prog.bind, pure, available, Prog.bind_assoc]
    exact .cons (.choose (ck := .earlyReturn .callbackWait) true rfl allowed) (.refl _)

theorem callbackYieldNone (wait : CallbackWait grow sig) (kind : wait.kind = .yield)
    (focused : reached.ctl = wait.saved :: rest)
    (live : reached.store.task? wait.taskId = some liveTask) (noCancel : liveTask.state ≠ .pendingCancel)
    {callback : (core3 grow).FuncAddr} (chosen : wait.task.opts.callback = some callback) :
    Steps profile ready (specDispatch ready impl) reached (List.replicate 3 .tau)
      (wait.eventCall reached reached.store callback .none rest) := by
  have lookup : ArenaField.tasks.get? reached.store wait.taskId = some liveTask := live
  simp only [CallbackWait.saved, CallbackWait.suffix, kind] at focused
  refine .cons (.get focused) ?_
  simp [Prog.bind, lookup, noCancel, pure, CallbackWait.invoke, chosen]
  exact .cons (.modify rfl) (.cons (.callCore rfl) (.refl _))

theorem callbackWaitEvent (wait : CallbackWait grow sig) {set : WsetId} (kind : wait.kind = .wait set)
    (focused : reached.ctl = wait.saved :: rest)
    (live : reached.store.task? wait.taskId = some liveTask) (noCancel : liveTask.state ≠ .pendingCancel)
    {record : WaitableSet} (setLive : (wait.decrement reached.store).wset? set = some record)
    {permutation : List Nat} (allowed : Allowed profile (.shuffle record.elems.length) permutation)
    {selected : Waitable} (selects : (applyPerm permutation record.elems).find?
      (wait.shuffled reached.store set record permutation).waitableHasEvent = some selected)
    {taken : CStore (core3 grow)} {event : EventTuple}
    (take : (wait.shuffled reached.store set record permutation).takeWaitableEvent selected = (taken, some event))
    {callback : (core3 grow).FuncAddr} (chosen : wait.task.opts.callback = some callback) :
    Steps profile ready (specDispatch ready impl) reached
      (List.replicate 3 .tau ++ [.choice (.shuffle record.elems.length) permutation] ++ List.replicate 6 .tau)
      (wait.eventCall reached taken callback event rest) := by
  have lookup : ArenaField.tasks.get? (reached.store.wsetDecWaitingSt set) wait.taskId = some liveTask := live
  have setLookup : ArenaField.wsets.get? (reached.store.wsetDecWaitingSt set) set = some record := by
    simpa only [CallbackWait.decrement, kind, CStore.wset?] using setLive
  have selection := selects
  have consumed := take
  simp only [CallbackWait.shuffled, CallbackWait.decrement, kind] at selection consumed
  simp only [CallbackWait.saved, CallbackWait.suffix, kind] at focused
  refine .cons (.modify focused) (.cons (.get rfl) ?_)
  simp [Prog.bind, lookup, noCancel, pure, wsetGetPendingEvent, getObj]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, setLookup, pure, Canon.shuffle]
  refine .cons (.choose (ck := .shuffle record.elems.length) permutation rfl allowed) ?_
  refine .cons (.modify rfl) ?_
  refine .cons (.get rfl) ?_
  simp [Prog.bind, selection, Waitable.getPendingEvent, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, consumed, CallbackWait.invoke, chosen]
  refine .cons (.modify rfl) (.cons (.modify rfl) (.cons (.callCore rfl) ?_))
  simp only [CallbackWait.eventCall, CStore.takeWaitableEventSt, consumed]
  exact .refl _

theorem callbackWaitEmpty (wait : CallbackWait grow sig) {set : WsetId} (kind : wait.kind = .wait set)
    (focused : reached.ctl = wait.saved :: rest)
    (live : reached.store.task? wait.taskId = some liveTask) (noCancel : liveTask.state ≠ .pendingCancel)
    {record : WaitableSet} (setLive : (wait.decrement reached.store).wset? set = some record)
    (empty : (wait.decrement reached.store).wsetHasEvent set = false)
    {permutation : List Nat} (allowed : Allowed profile (.shuffle record.elems.length) permutation) :
    Steps profile ready (specDispatch ready impl) reached
      [.tau, .tau, .tau, .choice (.shuffle record.elems.length) permutation, .tau, .tau,
        .trap (.internal "WaitableSet.get_pending_event: no pending event")]
      (StepDefs.trapCfg { reached with store := wait.shuffled reached.store set record permutation }) := by
  have lookup : ArenaField.tasks.get? (reached.store.wsetDecWaitingSt set) wait.taskId = some liveTask := live
  simp only [CallbackWait.saved, CallbackWait.suffix, kind] at focused
  refine .cons (.modify focused) (.cons (.get rfl) ?_)
  simp [Prog.bind, lookup, noCancel, pure]
  simp only [CallbackWait.decrement, kind] at setLive empty
  let next : EventTuple → Session grow sig (Ret (core3 grow)) := fun event =>
    Prog.bind (modifyStore (LiftSt.retakeCallbackSt wait.task.inst wait.thread)) (fun () => wait.invoke event)
  let cut := { reached with
    store := reached.store.wsetDecWaitingSt set
    ctl := ⟨some wait.thread, .prog (Prog.bind (wsetGetPendingEvent set) next), wait.segments⟩ :: rest }
  simpa only [CallbackWait.shuffled, CallbackWait.decrement, kind, cut, next, StepDefs.trapCfg] using
    get_shuffles_empty (config := cut) (dispatch := specDispatch ready impl) set record permutation
      setLive empty allowed next rfl

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery
