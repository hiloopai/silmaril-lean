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

private theorem callbackReturnBody (wait : CallbackWait grow sig) (values : List FlatValue) :
    wait.afterCore values =
      match callbackReturn values with
      | .ok (code, index) => callRet (.loop (.callbackLoop wait.taskId wait.thread code.toNat index))
      | .error reason => trap reason := by
  cases values with
  | nil => rfl
  | cons packed more =>
    cases more with
    | cons => rfl
    | nil =>
      cases decoded : AsyncRef.unpackCallbackResult (flatNat packed) with
      | some next =>
        cases next
        simp [CallbackWait.afterCore, callbackReturn, Canon.unpackCallbackResult, decoded, orTrap, Prog.bind, pure]
      | none =>
        simp only [CallbackWait.afterCore, callbackReturn, Canon.unpackCallbackResult, decoded, orTrap, trap]
        apply congrArg (fun tail => Prog.op (S := Eff (core3 grow) (HostState sig)) (.trap .unsupportedCallbackCode) tail)
        funext failure
        cases failure

theorem callbackReturned (wait : CallbackWait grow sig) {core : (core3 grow).Thread (CanonHost (core3 grow))}
    {values : List FlatValue}
    (focused : reached.ctl = ⟨some wait.thread, .core core wait.afterCore, wait.segments⟩ :: rest)
    (result : (core3 grow).status reached.store.core core = .returned (.values values)) :
    match callbackReturn values with
    | .ok next => Steps profile ready (specDispatch ready impl) reached [.tau, .tau] (wait.nextIteration reached next rest)
    | .error reason => Steps profile ready (specDispatch ready impl) reached [.tau, .trap reason] (StepDefs.trapCfg reached) := by
  have returned := Step.coreReturned (prof := profile) (hr := ready) (dispatch := specDispatch ready impl) focused result
  rw [callbackReturnBody] at returned
  cases classified : callbackReturn values with
  | ok next =>
    cases next
    simp only [classified] at returned ⊢
    exact .cons returned (.cons (.call rfl) (.refl _))
  | error reason =>
    simp only [classified] at returned ⊢
    exact .cons returned (.cons (.trap rfl) (.refl _))

theorem callbackExitUnresolved (wait : CallbackWait grow sig) {index : Nat} {liveTask : Task (core3 grow)}
    (focused : reached.ctl = ⟨some wait.thread,
      .prog (callbackLoopBody .spec wait.taskId wait.thread CallbackCode.exit.toNat index), wait.segments⟩ :: rest)
    (live : reached.store.task? wait.taskId = some liveTask) (implicitThread : liveTask.implicitThread = some wait.thread)
    (lastThread : (liveTask.threads.erase wait.thread).isEmpty = true) (unresolved : liveTask.state ≠ .resolved) :
    Steps profile ready (specDispatch ready impl) reached [.tau, .tau, .trap .taskNotResolved]
      (StepDefs.trapCfg reached) := by
  have lookup : ArenaField.tasks.get? reached.store wait.taskId = some liveTask := live
  refine .cons (.get focused) ?_
  simp [Prog.bind, lookup, implicitThread, orTrap, pure, Task.unregisterThread]
  refine .cons (.get rfl) ?_
  have guard : ((liveTask.threads.erase wait.thread).isEmpty && !decide (liveTask.state = .resolved)) = true := by
    simp only [lastThread, decide_eq_false unresolved, Bool.not_false, Bool.and_true]
  simp only [Prog.bind, lookup, pure, guard, trapIf, ite_true]
  exact .cons (.trap rfl) (.refl _)

theorem callbackNextWait (wait : CallbackWait grow sig) {core : (core3 grow).Thread (CanonHost (core3 grow))}
    {values : List FlatValue} (focused : reached.ctl = ⟨some wait.thread, .core core wait.afterCore, wait.segments⟩ :: rest)
    (result : (core3 grow).status reached.store.core core = .returned (.values values))
    {kind : CallbackWaitKind} {index : Nat} (decoded : callbackReturn values = .ok (kind.code, index))
    {liveTask : Task (core3 grow)} (live : reached.store.task? wait.taskId = some liveTask)
    (noCancel : liveTask.state ≠ .pendingCancel) (selected : (wait.followingWait liveTask kind).selected reached index) :
    let entry := wait.nextIteration reached (kind.code, index) rest
    let following := wait.followingWait liveTask kind
    Steps profile ready (specDispatch ready impl) reached
      ([.tau, .tau] ++ List.replicate kind.entrySteps .tau) (following.entry entry rest) := by
  have returned := callbackReturned (profile := profile) (ready := ready) (impl := impl) wait focused result
  rw [decoded] at returned
  dsimp only
  refine appendRun returned ?_
  cases kind with
  | yield => exact callbackYieldEntry rfl live noCancel
  | wait set =>
    obtain ⟨inst, instLive, handle⟩ := selected
    exact callbackWaitEntry rfl live noCancel instLive handle

theorem callbackReparks (wait : CallbackWait grow sig) {core : (core3 grow).Thread (CanonHost (core3 grow))}
    {values : List FlatValue} (focused : reached.ctl = ⟨some wait.thread, .core core wait.afterCore, wait.segments⟩ :: rest)
    (result : (core3 grow).status reached.store.core core = .returned (.values values))
    {kind : CallbackWaitKind} {index : Nat} (decoded : callbackReturn values = .ok (kind.code, index))
    {liveTask : Task (core3 grow)} (live : reached.store.task? wait.taskId = some liveTask)
    (noCancel : liveTask.state ≠ .pendingCancel) (selected : (wait.followingWait liveTask kind).selected reached index) :
    let entry := wait.nextIteration reached (kind.code, index) rest
    let following := wait.followingWait liveTask kind
    Steps profile ready (specDispatch ready impl) reached
      ([.tau, .tau] ++ (List.replicate kind.entrySteps .tau ++ following.parkLabels (following.readyAt entry)))
      (following.blocked entry rest) := by
  dsimp only
  rw [← List.append_assoc]
  exact appendRun (callbackNextWait wait focused result decoded live noCancel selected) (callbackBlocks _ rfl)

theorem callbackExitResolved (wait : CallbackWait grow sig) {index : Nat} {liveTask : Task (core3 grow)}
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
      (wait.exitComplete reached liveTask slot rest) := by
  have lookup : ArenaField.tasks.get? reached.store wait.taskId = some liveTask := live
  have instLookup : ArenaField.insts.get? reached.store liveTask.inst = some inst := instanceLive
  have count := List.replicate_add (α := Label (core3 grow) (HostState sig)) 5
    (liveTask.ft.async_ && liveTask.needsExclusive).toNat .tau
  rw [count]
  refine .cons (.get focused) ?_
  simp [Prog.bind, lookup, implicitThread, orTrap, pure, Task.unregisterThread]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, lookup, resolved, pure, trapIf]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, threadLive, threadIndex, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, instLookup, remove, pure]
  refine .cons (.modify rfl) ?_
  cases release : (liveTask.ft.async_ && liveTask.needsExclusive) with
  | false =>
    simp only [CallbackWait.exitComplete, ← Bool.and_eq_true, release, Bool.false_eq_true, ite_false]
    exact .refl _
  | true =>
    simp only [CallbackWait.exitComplete, ← Bool.and_eq_true, release, ite_true]
    exact .cons (.modify rfl) (.refl _)

theorem unwindCallback (depth : Nat)
    (focused : reached.ctl = ⟨some thread, .prog (.pure .unit),
      List.replicate depth (.prog (fun returned => .pure returned))⟩ :: rest) :
    Steps profile ready (specDispatch ready impl) reached (List.replicate (depth + 1) .tau)
      { reached with store := StepDefs.threadStatusSt thread .exited reached.store, ctl := rest } := by
  induction depth generalizing reached with
  | zero => exact .cons (.threadExit focused) (.refl _)
  | succ depth ih => exact .cons (.popProg focused) (ih rfl)

private def importGuard {wait : CallbackWait grow sig} (entry : CallbackCancelImport wait reached) :
    Config (core3 grow) (HostState sig) :=
  { reached with ctl := ⟨some wait.thread, .prog (do
    trapIf (decide (entry.liveTask.numBorrows > 0)) .borrowsRemain
    callUnit (.onResolve entry.liveTask.caller none)
    modifyStore (CStore.setTaskState wait.taskId .resolved)
    pure (.flat [])), .core entry.core wait.afterCore :: wait.segments⟩ :: entry.rest }

private theorem callbackCancelGuard {wait : CallbackWait grow sig} (entry : CallbackCancelImport wait reached) :
    Steps profile ready (specDispatch ready impl) reached (List.replicate 8 .tau) (importGuard entry) := by
  have taskLive : ArenaField.tasks.get? reached.store wait.taskId = some entry.liveTask := entry.taskRecord
  have instLive : ArenaField.insts.get? reached.store entry.liveTask.inst = some entry.liveInst := entry.instRecord
  have admitted : calloutEntry reached.store (some wait.thread) (.builtin .taskCancel entry.liveTask.inst) = none := by
    simp [calloutEntry, instOfThread?, entry.threadRecord, entry.taskIdentity, taskLive]
  refine .cons (.coreCallout (dispatch := specDispatch ready impl) entry.focused entry.callout)
    (.cons (.currentThread rfl) (.cons (.get rfl) ?_))
  simp [Prog.bind, admitted, calloutBody, builtinProg, withArgs0, Builtins.taskCancel]
  refine .cons (.currentThread rfl) (.cons (.get rfl) ?_)
  simp [Prog.bind, entry.threadRecord, entry.taskIdentity, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, taskLive, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, instLive, entry.mayLeave, entry.asyncOpts, trapIf, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, taskLive, entry.delivered, trapIf, pure, importGuard, Prog.bind_assoc]
  exact .refl _

theorem callbackCancelImport {wait : CallbackWait grow sig} (entry : CallbackCancelImport wait reached) :
    (entry.liveTask.numBorrows = 0 → Steps profile ready (specDispatch ready impl) reached
      (List.replicate 9 .tau) entry.resolveEntry) ∧
    (entry.liveTask.numBorrows > 0 → Steps profile ready (specDispatch ready impl) reached
      (List.replicate 8 .tau ++ [.trap .borrowsRemain]) (StepDefs.trapCfg reached)) := by
  have leading := callbackCancelGuard (profile := profile) (ready := ready) (impl := impl) entry
  constructor
  · intro empty
    have focused : (importGuard entry).ctl = ⟨some wait.thread, .prog (.op (.call (.onResolve entry.liveTask.caller none))
      entry.afterResolve), .core entry.core wait.afterCore :: wait.segments⟩ :: entry.rest := by
      simp [importGuard, trapIf, empty, callUnit, callRet, perform, Eff, Prog.lift, pure]
      apply congrArg (fun tail => Focus.prog (Prog.op (S := Eff (core3 grow) (HostState sig))
        (.call (.onResolve entry.liveTask.caller none)) tail))
      funext result
      cases result <;> first | rfl |
        (simp [CallbackCancelImport.afterResolve, internal, trap, Eff, Prog.bind]; funext failure; cases failure)
    exact appendRun leading (.cons (.call focused) (.refl _))
  · intro borrows
    have focused : (importGuard entry).ctl = ⟨some wait.thread, .prog (trap .borrowsRemain),
      .core entry.core wait.afterCore :: wait.segments⟩ :: entry.rest := by
      simp only [importGuard, trapIf, decide_eq_true borrows, ite_true, Prog.bind_eq, trap]
      simp [Eff, Prog.bind]
      apply congrArg (fun tail => Focus.prog (Prog.op (S := Eff (core3 grow) (HostState sig)) (.trap .borrowsRemain) tail))
      funext failure
      cases failure
    exact appendRun leading (.cons (.trap focused) (.refl _))

theorem callbackCancelResolve {wait : CallbackWait grow sig} (entry : CallbackCancelImport wait reached)
    {subtask : SubtaskId} (resolution : LowerCancelResolution reached.store entry.liveTask.caller subtask) :
    Steps profile ready (specDispatch ready impl) entry.resolveEntry
      (List.replicate (resolution.callbackSteps + 1) .tau) (entry.resumed resolution) := by
  have live : ArenaField.subtasks.get? reached.store subtask = some resolution.record := resolution.live
  let progressRecord := { resolution.record with common := { resolution.record.common with pending := some (.subtask subtask) } }
  have queued : ArenaField.subtasks.get? (reached.store.setPendingSt (.subtask subtask) (.subtask subtask)) subtask =
      some progressRecord := by
    simp only [CStore.setPendingSt, CStore.modifyWaitableCommon, ArenaField.get?_modify_self, live, Option.map_some, progressRecord]
  have selectState : (if resolution.record.state = .starting then
      Subtask.resolve (E := core3 grow) (σ := HostState sig) subtask .cancelledBeforeStarted []
      else Subtask.resolve subtask .cancelledBeforeReturned []) = Subtask.resolve subtask resolution.cancelledState [] := by
    unfold LowerCancelResolution.cancelledState
    split <;> rfl
  have read := Step.get (prof := profile) (hr := ready) (dispatch := specDispatch ready impl)
    (show entry.resolveEntry.ctl = ⟨some wait.thread,
      .prog (callerOnResolve .spec .none entry.liveTask.caller none),
      .prog entry.afterResolve :: .core entry.core wait.afterCore :: wait.segments⟩ :: entry.rest from rfl)
  simp [Prog.bind, CallbackCancelImport.resolveEntry, resolution.callerLive, pure] at read
  cases found : resolution.record.index <;>
    simp only [LowerCancelResolution.callbackSteps, found, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
      ite_false, ite_true] <;>
    refine .cons read (.cons (.get rfl) ?_) <;>
    simp [Prog.bind, resolution.callerLive, pure, Quirks.none, Prog.bind_assoc]
  · refine .cons (.get rfl) ?_
    simp [Prog.bind, live, found, pure]
    refine .cons (.get rfl) ?_
    simp [Prog.bind, live, pure, selectState]
    refine .cons (.modify rfl) (.cons (.popProg rfl) (.cons (.modify rfl) (.cons (.popCore rfl) ?_)))
    simp [CallbackCancelImport.resumed, LowerCancelResolution.resolvedStore, LowerCancelResolution.progressStore, found]
    exact .refl _
  · refine .cons (.get rfl) ?_
    simp [Prog.bind, live, found, pure]
    refine .cons (.modify rfl) (.cons (.get rfl) ?_)
    simp [Prog.bind, queued, progressRecord, pure, selectState]
    refine .cons (.modify rfl) (.cons (.popProg rfl) (.cons (.modify rfl) (.cons (.popCore rfl) ?_)))
    simp [CallbackCancelImport.resumed, LowerCancelResolution.resolvedStore, LowerCancelResolution.progressStore, found]
    exact .refl _

theorem callbackCancelLinked {wait : CallbackWait grow sig} (entry : CallbackCancelImport wait reached)
    (empty : entry.liveTask.numBorrows = 0)
    {subtask : SubtaskId} (resolution : LowerCancelResolution reached.store entry.liveTask.caller subtask) :
    Steps profile ready (specDispatch ready impl) reached
      (List.replicate 9 .tau ++ List.replicate (resolution.callbackSteps + 1) .tau) (entry.resumed resolution) :=
  appendRun ((callbackCancelImport entry).1 empty) (callbackCancelResolve entry resolution)

theorem callbackCancelStarted {wait : CallbackWait grow sig} (entry : CallbackCancelImport wait reached)
    (empty : entry.liveTask.numBorrows = 0)
    {subtask : SubtaskId} (resolution : LowerCancelResolution reached.store entry.liveTask.caller subtask)
    (started : resolution.record.state = .started) {index : Nat} (indexed : resolution.record.index = some index) :
    Steps profile ready (specDispatch ready impl) reached
      (List.replicate 9 .tau ++ List.replicate (resolution.callbackSteps + 1) .tau) (entry.resumed resolution) ∧
    (entry.resumed resolution).store.subtask? subtask = some resolution.resolvedRecord ∧
    resolution.resolvedRecord.state = .cancelledBeforeReturned ∧ resolution.resolvedRecord.index = some index ∧
    resolution.resolvedRecord.common.pending = some (.subtask subtask) ∧
    resolution.resolvedRecord.lenders = resolution.record.lenders := by
  refine ⟨callbackCancelLinked entry empty resolution, resolution.live_resolved, ?_, indexed, ?_, rfl⟩
  · simp [LowerCancelResolution.resolvedRecord, LowerCancelResolution.cancelledState, started]
  · simp [LowerCancelResolution.resolvedRecord, indexed]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery
