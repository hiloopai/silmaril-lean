module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Callback.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.AsyncRef
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall ComponentCall.Delivery

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start reached : Config (core3 grow) (HostState sig)}
  {thread : ThreadId} {taskId : TaskId} {task : Task (core3 grow)}
  {segments : List (Seg (core3 grow) (HostState sig))} {rest : List (Activation (core3 grow) (HostState sig))}

theorem callbackYieldEntry {index : Nat}
    (focused : start.ctl = ⟨some thread, .prog (callbackLoopBody .spec taskId thread CallbackCode.yield.toNat index), segments⟩ :: rest)
    (live : start.store.task? taskId = some task) (noCancel : task.state ≠ .pendingCancel) :
    Steps profile ready (specDispatch ready impl) start (List.replicate 3 .tau)
      ((⟨thread, taskId, task, .yield, segments⟩ : CallbackWait grow sig).entry start rest) := by
  have lookup : ArenaField.tasks.get? start.store taskId = some task := live
  refine .cons (.get focused) ?_
  simp [Prog.bind, lookup, pure, Task.deliverPendingCancel]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, lookup, pure, noCancel]
  refine .cons (.modify rfl) ?_
  simp [CallbackWait.entry, CallbackWait.released, CallbackWait.site, CallbackWait.condition,
    CallbackWait.suffix, CallbackWait.invoke, CallbackCode.ofNat?, CallbackCode.toNat,
    Task.deliverPendingCancel, Prog.bind_assoc, Prog.bind, pure]
  exact .refl _

theorem callbackWaitEntry {index : Nat} {set : WsetId} {inst : InstState}
    (focused : start.ctl = ⟨some thread, .prog (callbackLoopBody .spec taskId thread CallbackCode.wait.toNat index), segments⟩ :: rest)
    (live : start.store.task? taskId = some task) (noCancel : task.state ≠ .pendingCancel)
    (instanceLive : (LiftSt.releaseCallbackSt task.inst thread start.store).inst? task.inst = some inst)
    (selected : inst.handles.get? index = some (.wset set)) :
    Steps profile ready (specDispatch ready impl) start (List.replicate 6 .tau)
      ((⟨thread, taskId, task, .wait set, segments⟩ : CallbackWait grow sig).entry start rest) := by
  have lookup : ArenaField.tasks.get? start.store taskId = some task := live
  have instLookup : ArenaField.insts.get? (LiftSt.releaseCallbackSt task.inst thread start.store) task.inst = some inst :=
    instanceLive
  have taskLookup : ArenaField.tasks.get? (LiftSt.releaseCallbackSt task.inst thread start.store) taskId = some task := live
  refine .cons (.get focused) ?_
  simp [Prog.bind, lookup, pure, Task.deliverPendingCancel]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, lookup, pure, noCancel]
  refine .cons (.modify rfl) (.cons (.get rfl) ?_)
  simp [Prog.bind, instLookup, selected, pure, wsetWaitFromCallback]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, taskLookup, pure]
  refine .cons (.modify rfl) ?_
  simp [CallbackWait.entry, CallbackWait.released, CallbackWait.site, CallbackWait.condition,
    CallbackWait.suffix, CallbackWait.invoke, CallbackCode.toNat,
    Prog.bind_assoc, Prog.bind, pure]
  exact .refl _

theorem callbackBlocks (wait : CallbackWait grow sig) {available : Bool}
    (availability : wait.condition.eval (fun _ => false) (wait.released start.store) = available) :
    Steps profile ready (specDispatch ready impl) (wait.entry start rest) (wait.parkLabels available)
      (wait.blocked start rest) := by
  cases kind : wait.kind with
  | yield =>
    have eval : (ReadyCond.exclusiveFree wait.task.inst).eval (fun _ => false) (wait.released start.store) = available := by
      simpa only [CallbackWait.condition, kind] using availability
    simp only [CallbackWait.entry, CallbackWait.parkLabels, CallbackWait.site, CallbackWait.condition, kind, List.cons_append,
      List.nil_append]
    refine .cons (.currentThread rfl) (.cons (.get rfl) ?_)
    rw [CallbackWait.blocked, CallbackWait.condition, kind]
    cases available with
    | false =>
      simp [Prog.bind, eval, pure, Thread.startWaiting, Prog.bind_assoc]
      exact .cons (.modify rfl) (.cons (.block rfl) (.refl _))
    | true =>
      simp [Prog.bind, eval, pure, Thread.startWaiting, Prog.bind_assoc]
      exact .cons (.choose (ck := .earlyReturn .callbackYield) false rfl (fun _ => rfl))
        (.cons (.modify rfl) (.cons (.block rfl) (.refl _)))
  | wait set =>
    have eval : (ReadyCond.callbackWait wait.task.inst wait.taskId set).eval (fun _ => false) (wait.released start.store) = available := by
      simpa only [CallbackWait.condition, kind] using availability
    simp only [CallbackWait.entry, CallbackWait.parkLabels, CallbackWait.site, CallbackWait.condition, kind, List.cons_append,
      List.nil_append]
    refine .cons (.currentThread rfl) (.cons (.get rfl) ?_)
    rw [CallbackWait.blocked, CallbackWait.condition, kind]
    cases available with
    | false =>
      simp [Prog.bind, eval, pure, Thread.startWaiting, Prog.bind_assoc]
      exact .cons (.modify rfl) (.cons (.block rfl) (.refl _))
    | true =>
      simp [Prog.bind, eval, pure, Thread.startWaiting, Prog.bind_assoc]
      exact .cons (.choose (ck := .earlyReturn .callbackWait) false rfl (fun _ => rfl))
        (.cons (.modify rfl) (.cons (.block rfl) (.refl _)))

theorem callbackCancelCore (wait : CallbackWait grow sig) {liveTask : Task (core3 grow)}
    {callback : (core3 grow).FuncAddr} (focused : reached.ctl = wait.saved :: rest)
    (live : reached.store.task? wait.taskId = some liveTask) (pending : liveTask.state = .pendingCancel)
    (chosen : wait.task.opts.callback = some callback) :
    Steps profile ready (specDispatch ready impl) reached
      (List.replicate wait.cancelSteps .tau) (wait.called reached callback rest) := by
  cases kind : wait.kind with
  | yield =>
    simp only [CallbackWait.cancelSteps, kind]
    have lookup : ArenaField.tasks.get? reached.store wait.taskId = some liveTask := live
    simp only [CallbackWait.saved, CallbackWait.suffix, kind] at focused
    refine .cons (.get focused) ?_
    simp [Prog.bind, lookup, pending, pure, CallbackWait.invoke, chosen]
    refine .cons (.modify rfl) (.cons (.modify rfl) (.cons (.callCore rfl) ?_))
    simp only [CallbackWait.called, CallbackWait.cancelledStore, CallbackWait.decrement, kind]
    exact .refl _
  | wait set =>
    simp only [CallbackWait.cancelSteps, kind]
    have lookup : ArenaField.tasks.get? (reached.store.wsetDecWaitingSt set) wait.taskId = some liveTask := live
    simp only [CallbackWait.saved, CallbackWait.suffix, kind] at focused
    refine .cons (.modify focused) (.cons (.get rfl) ?_)
    simp [Prog.bind, lookup, pending, pure, CallbackWait.invoke, chosen]
    refine .cons (.modify rfl) (.cons (.modify rfl) (.cons (.callCore rfl) ?_))
    simp only [CallbackWait.called, CallbackWait.cancelledStore, CallbackWait.decrement, kind]
    exact .refl _

private theorem appendRun {first mid last : Config (core3 grow) (HostState sig)} {leading trailing}
    (run : Steps profile ready (specDispatch ready impl) first leading mid)
    (tail : Steps profile ready (specDispatch ready impl) mid trailing last) :
    Steps profile ready (specDispatch ready impl) first (leading ++ trailing) last := by
  induction run with
  | refl => exact tail
  | cons step _ ih => exact .cons step (ih tail)

theorem startedCancelCore {parked : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    {cancel : ParkedCancel parked subtask} (request : TaskCancelAdmission cancel)
    (wait : CallbackWait grow sig) (sameThread : wait.thread = request.implicitThread)
    (sameTask : wait.taskId = request.taskId) {between}
    (path : ParkedPrefix profile ready (specDispatch ready impl) wait.thread (wait.blocked start rest) between parked)
    (started : request.callee.state = .started) (cancellable : request.implicitState.cancellable = true)
    (available : request.markedStore.threadReady (ready parked.host) request.implicitThread = true)
    {callback : (core3 grow).FuncAddr} (chosen : wait.task.opts.callback = some callback) :
    Steps profile ready (specDispatch ready impl) parked
      (List.replicate request.reentrySteps .tau ++ List.replicate wait.cancelSteps .tau)
      (wait.called (request.reentered wait.saved) callback cancel.callbackTail) := by
  have saved : parked.cont? request.implicitThread = some wait.saved := by
    rw [← sameThread]
    exact path.reaches.2.trans (Config.cont?_setCont_self _ _ _)
  have entered := request.reenters (profile := profile) (impl := impl) (.started started cancellable available) saved
  have marked : request.markedStore.task? request.taskId = some (request.callee.withState .pendingCancel) := by
    change ArenaField.tasks.get? (ArenaField.tasks.modify (Builtins.WaitableSt.requestCancel subtask cancel.thread
      parked.store) request.taskId _) request.taskId = _
    rw [ArenaField.get?_modify_self]
    have live : ArenaField.tasks.get? (Builtins.WaitableSt.requestCancel subtask cancel.thread parked.store)
      request.taskId = some request.callee := request.taskLive
    rw [live]
    rfl
  have live : (request.reentered wait.saved).store.task? wait.taskId = some (request.callee.withState .pendingCancel) := by
    rw [sameTask]
    unfold TaskCancelAdmission.reentered
    split <;> exact marked
  exact appendRun entered (callbackCancelCore wait rfl live rfl chosen)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery
