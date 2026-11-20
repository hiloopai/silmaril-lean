module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Callback.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Callback
import Silmaril.Wasm.Component.Reference.Runtime.Task.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.AsyncRef
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall ComponentCall.Delivery

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start reached parked : Config (core3 grow) (HostState sig)}
  {rest : List (Activation (core3 grow) (HostState sig))}

theorem callbackCoreOnlyCut (wait : CallbackWait grow sig)
    {core : (core3 grow).Thread (CanonHost (core3 grow))} {count : Nat}
    (focused : start.ctl = ⟨some wait.thread, .core core wait.afterCore, wait.segments⟩ :: rest)
    (run : Steps profile ready (specDispatch ready impl) start (List.replicate count .core) reached) :
    ∃ next, reached = wait.coreAt start reached.store.core next rest := by
  induction count generalizing start reached core with
  | zero =>
    simp only [List.replicate_zero] at run
    cases run
    exact ⟨core, by cases start; simp_all [CallbackWait.coreAt]⟩
  | succ count ih =>
    simp only [List.replicate_succ] at run
    cases run with
    | cons step suffix =>
      cases step with
      | coreInternal atStep running transition =>
        rename_i stepThread stepCore stepCont stepSegments stepRest stepStore nextCore
        have heads := List.cons.inj (atStep.symm.trans focused)
        injection heads.1 with sameThread sameFocus sameSegments
        injection sameFocus with sameCore sameCont
        obtain ⟨next, cut⟩ := ih (core := nextCore) (by simp only [sameThread, sameCont, sameSegments, heads.2]) suffix
        exact ⟨next, cut⟩

private theorem exitSubtasks (wait : CallbackWait grow sig) (cut : Config (core3 grow) (HostState sig))
    (liveTask : Task (core3 grow)) (slot : Nat) :
    (wait.exitComplete cut liveTask slot rest).store.subtasks = cut.store.subtasks := by
  have frame := (cut.store.unregisterThreadSt_frame wait.taskId wait.thread slot).2.2.2.1
  unfold CallbackWait.exitComplete
  split <;> exact frame

private theorem appendRun {first mid last : Config (core3 grow) (HostState sig)} {leading trailing}
    (left : Steps profile ready (specDispatch ready impl) first leading mid)
    (right : Steps profile ready (specDispatch ready impl) mid trailing last) :
    Steps profile ready (specDispatch ready impl) first (leading ++ trailing) last := by
  induction left with
  | refl => exact right
  | cons step _ ih => exact .cons step (ih right)

theorem callbackCancelDeliversStarted {wait : CallbackWait grow sig}
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
        (cancel.cancelledReply exited .cancelledBeforeReturned) := by
  obtain ⟨resolve, liveRecord, cancelled, _, pending, _⟩ :=
    callbackCancelStarted (profile := profile) (ready := ready) (impl := impl) entry empty resolution started indexed
  obtain ⟨next, frame⟩ := callbackCoreOnlyCut wait rfl run
  let loop := wait.nextIteration cut (.exit, exitIndex) entry.rest
  let following := { wait with segments := .prog (fun result => .pure result) :: wait.segments }
  let liveTask := entry.liveTask.withState .resolved
  have returnedSteps : Steps profile ready (specDispatch ready impl) cut [.tau, .tau] loop := by
    simpa only [decoded] using callbackReturned (profile := profile) (ready := ready) (impl := impl) wait focused returned
  have live : loop.store.task? wait.taskId = some liveTask := by
    change cut.store.task? wait.taskId = some liveTask
    rw [frame]
    change ArenaField.tasks.get? (ArenaField.tasks.modify resolution.resolvedStore wait.taskId _) wait.taskId = _
    rw [ArenaField.get?_modify_self]
    have tasks : resolution.resolvedStore.tasks = reached.store.tasks := by
      unfold LowerCancelResolution.resolvedStore LowerCancelResolution.progressStore
      split <;> rfl
    change (resolution.resolvedStore.tasks.get? wait.taskId.idx).map _ = _
    rw [tasks]
    rw [show reached.store.tasks.get? wait.taskId.idx = some entry.liveTask from entry.taskRecord]
    rfl
  have threadLive : ArenaField.threads.get? loop.store wait.thread = some entry.liveThread := by
    change ArenaField.threads.get? cut.store wait.thread = _
    rw [frame]
    unfold CallbackWait.coreAt CallbackCancelImport.resumed LowerCancelResolution.resolvedStore
      LowerCancelResolution.progressStore
    split <;> exact entry.threadRecord
  have instanceLive : loop.store.inst? liveTask.inst = some entry.liveInst := by
    change cut.store.inst? entry.liveTask.inst = _
    rw [frame]
    unfold CallbackWait.coreAt CallbackCancelImport.resumed LowerCancelResolution.resolvedStore
      LowerCancelResolution.progressStore
    split <;> exact entry.instRecord
  let done := following.exitComplete loop liveTask slot entry.rest
  have exitSteps : Steps profile ready (specDispatch ready impl) loop
      (List.replicate (5 + (liveTask.ft.async_ && liveTask.needsExclusive).toNat) .tau) done :=
    callbackExitResolved following rfl live implicitThread rfl threadLive threadIndex instanceLive remove
  let exited := { done with store := StepDefs.threadStatusSt wait.thread .exited done.store, ctl := entry.rest }
  have unwind : Steps profile ready (specDispatch ready impl) done (List.replicate (depth + 2) .tau) exited :=
    unwindCallback (depth + 1) (by simp [done, CallbackWait.exitComplete, following, List.replicate_succ, identityFrames])
  have retained : exited.store.subtask? subtask = some resolution.resolvedRecord := by
    have subtasks : exited.store.subtasks = (entry.resumed resolution).store.subtasks := by
      change done.store.subtasks = _
      rw [exitSubtasks]
      change cut.store.subtasks = _
      rw [frame]
      rfl
    change exited.store.subtasks.get? subtask.idx = _
    exact (congrArg (fun arena => arena.get? subtask.idx) subtasks).trans liveRecord
  have finish := cancel.finish_cancelled_callback (profile := profile) (ready := ready) (impl := impl)
    exited resolution.resolvedRecord resumer retained (Or.inr cancelled) pending
  refine ⟨exited, ?_, retained, by simpa only [cancelled] using finish⟩
  have trace := appendRun resolve (appendRun run (appendRun returnedSteps (appendRun exitSteps unwind)))
  have lengths : 2 + ((5 + (liveTask.ft.async_ && liveTask.needsExclusive).toNat) + (depth + 2)) =
      depth + 9 + (entry.liveTask.ft.async_ && entry.liveTask.needsExclusive).toNat := by
    change 2 + ((5 + (entry.liveTask.ft.async_ && entry.liveTask.needsExclusive).toNat) + (depth + 2)) = _
    omega
  rw [← lengths]
  simpa only [List.replicate_add, List.append_assoc,
    show List.replicate 2 (.tau : Label (core3 grow) (HostState sig)) = [.tau, .tau] from rfl] using trace

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery
