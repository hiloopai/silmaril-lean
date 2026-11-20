module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Callback.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Callback
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackEarly
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackDelivery
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackResume
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.AsyncRef
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall ComponentCall.Delivery
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start reached parked : Config (core3 grow) (HostState sig)}
  {rest : List (Activation (core3 grow) (HostState sig))}

private theorem releasedKeeps (wait : CallbackWait grow sig) (store : CStore (core3 grow)) (target : SubtaskId) :
    (wait.released store).subtask? target = store.subtask? target := by
  unfold CallbackWait.released
  split <;> rfl

private theorem shuffledKeeps (wait : CallbackWait grow sig) {set : WsetId} (kind : wait.kind = .wait set)
    (store : CStore (core3 grow)) (record : WaitableSet) (permutation : List Nat) (target : SubtaskId) :
    (wait.shuffled store set record permutation).subtask? target = store.subtask? target := by
  simp only [CallbackWait.shuffled, CallbackWait.decrement, kind]
  rfl

private theorem stepsAppend {first middle last : Config (core3 grow) (HostState sig)} {leading trailing}
    (left : Steps profile ready (specDispatch ready impl) first leading middle)
    (right : Steps profile ready (specDispatch ready impl) middle trailing last) :
    Steps profile ready (specDispatch ready impl) first (leading ++ trailing) last := by
  induction left with
  | refl => exact right
  | cons step _ ih => exact .cons step (ih right)

theorem callbackEarlyYieldRetains (wait : CallbackWait grow sig) (kind : wait.kind = .yield)
    (available : wait.readyAt start = true) (early : Allowed profile (.earlyReturn wait.site) true)
    {liveTask : Task (core3 grow)} (live : (wait.early start rest).store.task? wait.taskId = some liveTask)
    (noCancel : liveTask.state ≠ .pendingCancel)
    {callback : (core3 grow).FuncAddr} (chosen : wait.task.opts.callback = some callback) (target : SubtaskId) :
    let suffix := wait.early start rest
    let called := wait.eventCall suffix suffix.store callback .none rest
    Steps profile ready (specDispatch ready impl) (wait.entry start rest)
      ([.tau, .tau, .choice (.earlyReturn wait.site) true] ++ List.replicate 3 .tau) called ∧
    called.store.subtask? target = start.store.subtask? target := by
  exact ⟨stepsAppend (callbackEarly wait available early) (callbackYieldNone wait kind rfl live noCancel chosen),
    releasedKeeps wait start.store target⟩

theorem callbackWaitOtherRetains (wait : CallbackWait grow sig) {set : WsetId} (kind : wait.kind = .wait set)
    (focused : reached.ctl = wait.saved :: rest)
    {liveTask : Task (core3 grow)} (live : reached.store.task? wait.taskId = some liveTask)
    (noCancel : liveTask.state ≠ .pendingCancel)
    {record : WaitableSet} (setLive : (wait.decrement reached.store).wset? set = some record)
    {permutation : List Nat} (allowed : Allowed profile (.shuffle record.elems.length) permutation)
    {selected : Waitable} (selects : (applyPerm permutation record.elems).find?
      (wait.shuffled reached.store set record permutation).waitableHasEvent = some selected)
    {taken : CStore (core3 grow)} {event : EventTuple}
    (take : (wait.shuffled reached.store set record permutation).takeWaitableEvent selected = (taken, some event))
    {callback : (core3 grow).FuncAddr} (chosen : wait.task.opts.callback = some callback)
    (target : SubtaskId) (other : selected ≠ .subtask target) :
    let called := wait.eventCall reached taken callback event rest
    Steps profile ready (specDispatch ready impl) reached
      (List.replicate 3 .tau ++ [.choice (.shuffle record.elems.length) permutation] ++ List.replicate 6 .tau) called ∧
    called.store.subtask? target = reached.store.subtask? target := by
  refine ⟨callbackWaitEvent wait kind focused live noCancel setLive allowed selects take chosen, ?_⟩
  let shuffled := wait.shuffled reached.store set record permutation
  have takenStore : shuffled.takeWaitableEventSt selected = taken := congrArg Prod.fst take
  change taken.subtask? target = reached.store.subtask? target
  rw [← takenStore, take_event_other shuffled selected target other, shuffledKeeps wait kind]

theorem callbackEarlyWaitRetains (wait : CallbackWait grow sig) {set : WsetId} (kind : wait.kind = .wait set)
    (available : wait.readyAt start = true) (early : Allowed profile (.earlyReturn wait.site) true)
    {liveTask : Task (core3 grow)} (live : (wait.early start rest).store.task? wait.taskId = some liveTask)
    (noCancel : liveTask.state ≠ .pendingCancel)
    {record : WaitableSet} (setLive : (wait.decrement (wait.early start rest).store).wset? set = some record)
    {permutation : List Nat} (allowed : Allowed profile (.shuffle record.elems.length) permutation)
    {selected : Waitable} (selects : (applyPerm permutation record.elems).find?
      (wait.shuffled (wait.early start rest).store set record permutation).waitableHasEvent = some selected)
    {taken : CStore (core3 grow)} {event : EventTuple}
    (take : (wait.shuffled (wait.early start rest).store set record permutation).takeWaitableEvent selected =
      (taken, some event))
    {callback : (core3 grow).FuncAddr} (chosen : wait.task.opts.callback = some callback)
    (target : SubtaskId) (other : selected ≠ .subtask target) :
    let called := wait.eventCall (wait.early start rest) taken callback event rest
    Steps profile ready (specDispatch ready impl) (wait.entry start rest)
      ([.tau, .tau, .choice (.earlyReturn wait.site) true] ++
        (List.replicate 3 .tau ++ [.choice (.shuffle record.elems.length) permutation] ++ List.replicate 6 .tau)) called ∧
    called.store.subtask? target = start.store.subtask? target := by
  obtain ⟨run, retained⟩ := callbackWaitOtherRetains (profile := profile) (ready := ready) (impl := impl) wait kind
    (reached := wait.early start rest) rfl live noCancel setLive allowed selects take chosen target other
  exact ⟨stepsAppend (callbackEarly wait available early) run, retained.trans (releasedKeeps wait start.store target)⟩

theorem callbackWaitTakesResolution (wait : CallbackWait grow sig) {set : WsetId} (kind : wait.kind = .wait set)
    (focused : reached.ctl = wait.saved :: rest)
    {liveTask : Task (core3 grow)} (live : reached.store.task? wait.taskId = some liveTask)
    (noCancel : liveTask.state ≠ .pendingCancel)
    {record : WaitableSet} (setLive : (wait.decrement reached.store).wset? set = some record)
    {permutation : List Nat} (allowed : Allowed profile (.shuffle record.elems.length) permutation)
    {target : SubtaskId} (selects : (applyPerm permutation record.elems).find?
      (wait.shuffled reached.store set record permutation).waitableHasEvent = some (.subtask target))
    {pendingRecord : Subtask} (tracked : reached.store.subtask? target = some pendingRecord)
    (resolved : pendingRecord.state.resolved = true) (pending : pendingRecord.common.pending = some (.subtask target))
    {callback : (core3 grow).FuncAddr} (chosen : wait.task.opts.callback = some callback) :
    let shuffled := wait.shuffled reached.store set record permutation
    let event : EventTuple := ⟨.subtask, pendingRecord.index.getD 0, pendingRecord.state.toNat⟩
    let called := wait.eventCall reached (cancelDelivered shuffled target) callback event rest
    Steps profile ready (specDispatch ready impl) reached
      (List.replicate 3 .tau ++ [.choice (.shuffle record.elems.length) permutation] ++ List.replicate 6 .tau) called ∧
    called.store.subtask? target = some { pendingRecord with
      common := { pendingRecord.common with pending := none }, lenders := none } := by
  obtain ⟨take, cleared⟩ := take_pending_resolution _ pendingRecord
    ((shuffledKeeps wait kind reached.store record permutation target).trans tracked) resolved pending
  exact ⟨callbackWaitEvent wait kind focused live noCancel setLive allowed selects take chosen, cleared⟩

private theorem resumeKeeps {wait : CallbackWait grow sig} (resume : CallbackResume wait reached) (target : SubtaskId) :
    resume.resumed.store.subtask? target = reached.store.subtask? target := by
  unfold CallbackResume.resumed
  split <;> rfl

theorem callbackTickResumes (wait : CallbackWait grow sig) (tick : SelectedTick wait.thread reached ready profile)
    (saved : reached.cont? wait.thread = some wait.saved) :
    Steps profile ready (specDispatch ready impl) reached (tick.selectionLabels ++ (wait.tickResume tick).labels)
      (wait.tickResume tick).resumed :=
  stepsAppend tick.selects_thread (resumeCallback (wait.tickResume tick) saved)

theorem callbackTrackedTick (wait : CallbackWait grow sig) (tick : SelectedTick wait.thread reached ready profile)
    {leading} (path : ParkedPrefix profile ready (specDispatch ready impl) wait.thread (wait.blocked start rest) leading reached) :
    Steps profile ready (specDispatch ready impl) (wait.blocked start rest)
      (leading ++ (tick.selectionLabels ++ (wait.tickResume tick).labels)) (wait.tickResume tick).resumed := by
  obtain ⟨run, kept⟩ := path.reaches
  exact stepsAppend run (callbackTickResumes wait tick (kept.trans (Config.cont?_setCont_self _ _ _)))

theorem closedCallbackPrefixReaches {labels target}
    (path : ClosedCallbackPrefix profile ready impl target start labels reached) :
    Steps profile ready (specDispatch ready impl) start labels reached ∧
      reached.store.subtask? target = start.store.subtask? target := by
  induction path with
  | done state => exact ⟨.refl state, rfl⟩
  | core wait focused run _ ih =>
    obtain ⟨_, frame⟩ := callbackCoreOnlyCut wait focused run
    exact ⟨stepsAppend run ih.1, ih.2.trans (congrArg (fun cut => cut.store.subtask? target) frame)⟩
  | nextWait wait focused returned decoded live noCancel selected _ ih =>
    exact ⟨stepsAppend (callbackNextWait wait focused returned decoded live noCancel selected) ih.1,
      ih.2.trans (releasedKeeps _ _ target)⟩
  | early wait available early _ ih =>
    exact ⟨stepsAppend (callbackEarly wait available early) ih.1, ih.2⟩
  | park wait availability _ ih =>
    exact ⟨stepsAppend (callbackBlocks wait availability) ih.1, ih.2⟩
  | resume resume saved _ ih =>
    exact ⟨stepsAppend (resumeCallback resume saved) ih.1, ih.2.trans (resumeKeeps resume target)⟩
  | tick wait tick saved _ ih =>
    exact ⟨stepsAppend (callbackTickResumes wait tick saved) ih.1, ih.2.trans (resumeKeeps (wait.tickResume tick) target)⟩
  | yieldNone wait kind focused live noCancel chosen _ ih =>
    exact ⟨stepsAppend (callbackYieldNone wait kind focused live noCancel chosen) ih.1, ih.2⟩
  | waitOther wait kind focused live noCancel setLive allowed selects take chosen other _ ih =>
    obtain ⟨run, retained⟩ := callbackWaitOtherRetains wait kind focused live noCancel setLive allowed selects take
      chosen target other
    exact ⟨stepsAppend run ih.1, ih.2.trans retained⟩

theorem callbackCancelDeliversAfterClosedPrefix {wait finalWait : CallbackWait grow sig}
    (entry : CallbackCancelImport wait reached) {subtask : SubtaskId} (cancel : ParkedCancel parked subtask)
    (empty : entry.liveTask.numBorrows = 0)
    (resolution : LowerCancelResolution reached.store entry.liveTask.caller subtask)
    (started : resolution.record.state = .started) {index : Nat} (indexed : resolution.record.index = some index)
    {cut labels} (path : ClosedCallbackPrefix profile ready impl subtask (entry.resumed resolution) labels cut)
    (exit : CallbackExit finalWait cut) (resumer : exit.rest = cancel.callbackTail) :
    Steps profile ready (specDispatch ready impl) reached
      ((List.replicate 9 .tau ++ List.replicate (resolution.callbackSteps + 1) .tau) ++ (labels ++ exit.labels))
      exit.unwound ∧
    exit.unwound.store.subtask? subtask = some resolution.resolvedRecord ∧
    Steps profile ready (specDispatch ready impl) exit.unwound (List.replicate 8 .tau)
      (cancel.cancelledReply exit.unwound .cancelledBeforeReturned) := by
  obtain ⟨resolve, atResume, cancelled, _, pending, _⟩ :=
    callbackCancelStarted (profile := profile) (ready := ready) (impl := impl) entry empty resolution started indexed
  obtain ⟨run, retained⟩ := closedCallbackPrefixReaches path
  obtain ⟨exitRun, frame⟩ := callbackExit (profile := profile) (ready := ready) (impl := impl) finalWait exit
  have atExit : exit.unwound.store.subtask? subtask = some resolution.resolvedRecord :=
    (congrArg (fun arena => arena.get? subtask.idx) frame).trans (retained.trans atResume)
  have reply := cancel.finish_cancelled_callback (profile := profile) (ready := ready) (impl := impl)
    exit.unwound resolution.resolvedRecord resumer atExit (Or.inr cancelled) pending
  exact ⟨stepsAppend resolve (stepsAppend run exitRun), atExit, by simpa only [cancelled] using reply⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery
