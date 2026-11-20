module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Callback.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackEarly

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.AsyncRef
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall ComponentCall.Delivery

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start reached : Config (core3 grow) (HostState sig)}
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

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery
