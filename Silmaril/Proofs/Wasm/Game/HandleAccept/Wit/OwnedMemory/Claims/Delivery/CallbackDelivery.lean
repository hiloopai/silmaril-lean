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

theorem callbackExit (wait : CallbackWait grow sig) (exit : CallbackExit wait reached) :
    Steps profile ready (specDispatch ready impl) reached exit.labels exit.unwound ∧
      exit.unwound.store.subtasks = reached.store.subtasks := by
  have returned := callbackReturned (profile := profile) (ready := ready) (impl := impl) wait exit.focused exit.returned
  rw [exit.decoded] at returned
  have unregistered := callbackExitResolved (profile := profile) (ready := ready) (impl := impl)
    wait.exitFrame (reached := wait.nextIteration reached (.exit, exit.index) exit.rest)
    rfl exit.taskLive exit.implicitThread exit.resolved exit.threadLive exit.threadIndex exit.instanceLive exit.remove
  have unwind : Steps profile ready (specDispatch ready impl) exit.unregistered (List.replicate (exit.depth + 2) .tau)
      exit.unwound :=
    unwindCallback (exit.depth + 1) (by simp [CallbackExit.unregistered, CallbackWait.exitComplete, CallbackWait.exitFrame,
      List.replicate_succ, exit.frames])
  refine ⟨?_, exitSubtasks wait.exitFrame _ _ _⟩
  simpa only [CallbackExit.labels, List.append_assoc] using appendRun returned (appendRun unregistered unwind)

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
  let liveTask := entry.liveTask.withState .resolved
  have live : cut.store.task? wait.taskId = some liveTask := by
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
  have threadLive : ArenaField.threads.get? cut.store wait.thread = some entry.liveThread := by
    rw [frame]
    unfold CallbackWait.coreAt CallbackCancelImport.resumed LowerCancelResolution.resolvedStore
      LowerCancelResolution.progressStore
    split <;> exact entry.threadRecord
  have instanceLive : cut.store.inst? liveTask.inst = some entry.liveInst := by
    change cut.store.inst? entry.liveTask.inst = _
    rw [frame]
    unfold CallbackWait.coreAt CallbackCancelImport.resumed LowerCancelResolution.resolvedStore
      LowerCancelResolution.progressStore
    split <;> exact entry.instRecord
  let exit : CallbackExit wait cut :=
    ⟨core, entry.rest, values, exitIndex, depth, liveTask, entry.liveThread, slot, entry.liveInst, removed,
      focused, returned, decoded, live, implicitThread, rfl, threadLive, threadIndex, instanceLive, remove, identityFrames⟩
  obtain ⟨exitSteps, keeps⟩ := callbackExit (profile := profile) (ready := ready) (impl := impl) wait exit
  have retained : exit.unwound.store.subtask? subtask = some resolution.resolvedRecord := by
    refine (congrArg (fun arena => arena.get? subtask.idx) keeps).trans ?_
    rw [frame]
    exact liveRecord
  have finish := cancel.finish_cancelled_callback (profile := profile) (ready := ready) (impl := impl)
    exit.unwound resolution.resolvedRecord resumer retained (Or.inr cancelled) pending
  refine ⟨exit.unwound, ?_, retained, by simpa only [cancelled] using finish⟩
  have trace := appendRun resolve (appendRun run exitSteps)
  have lengths : 2 + ((5 + (liveTask.ft.async_ && liveTask.needsExclusive).toNat) + (depth + 2)) =
      depth + 9 + (entry.liveTask.ft.async_ && entry.liveTask.needsExclusive).toNat := by
    change 2 + ((5 + (entry.liveTask.ft.async_ && entry.liveTask.needsExclusive).toNat) + (depth + 2)) = _
    omega
  rw [← lengths]
  simpa only [CallbackExit.labels, exit, liveTask, Task.withState, List.replicate_add, List.append_assoc,
    show List.replicate 2 (.tau : Label (core3 grow) (HostState sig)) = [.tau, .tau] from rfl] using trace

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery
