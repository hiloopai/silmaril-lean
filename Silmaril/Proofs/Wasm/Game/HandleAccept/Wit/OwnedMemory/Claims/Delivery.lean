module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall ComponentCall.Delivery

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {initial committed parked : Config (core3 grow) (HostState sig)} {subtask : SubtaskId} {index : Nat}

theorem retainingPath {labels}
    (path : Retaining profile ready (specDispatch ready impl) subtask index committed labels parked)
    (pending : PendingAt committed.store subtask index) :
    Steps profile ready (specDispatch ready impl) committed labels parked ∧ PendingAt parked.store subtask index := by
  induction path with
  | done => exact ⟨.refl _, pending⟩
  | step run keep _ ih =>
    obtain ⟨steps, queued⟩ := ih (keep pending)
    exact ⟨.cons run steps, queued⟩

theorem stepOfSubtasks {E : CoreEngine} {Host : Type} {hr : HostReady Host} {dispatch : Call E → P E Host (Ret E)}
    {state reached : Config E Host} {label} (run : Step profile hr dispatch state label reached)
    (same : reached.store.subtasks = state.store.subtasks) : Retaining profile hr dispatch subtask index state [label] reached := by
  refine .step run ?_ (.done _)
  intro ⟨record, live, returned, indexed, queued⟩
  refine ⟨record, ?_, returned, indexed, queued⟩
  exact (congrArg (fun arena => arena.get? subtask.idx) same).trans live

private theorem appendSteps {start middle reached : Config (core3 grow) (HostState sig)} {leading trailing}
    (first : Steps profile ready (specDispatch ready impl) start leading middle)
    (last : Steps profile ready (specDispatch ready impl) middle trailing reached) :
    Steps profile ready (specDispatch ready impl) start (leading ++ trailing) reached := by
  induction first with
  | refl => exact last
  | cons step _ ih => exact .cons step (ih last)

theorem resolutionIndexed (resolve : LinkedResolution initial subtask index) :
    Steps profile ready (specDispatch ready impl) initial (List.replicate 17 .tau) resolve.committed ∧
      PendingAt resolve.committed.store subtask index := by
  have run := resolve_linked_commit (prof := profile) (ready := ready) (dispatch := specDispatch ready impl)
    resolve.callee resolve.ticket resolve.caller resolve.tree resolve.writer subtask resolve.record resolve.context
    resolve.args resolve.position resolve.callerRecord resolve.live resolve.options resolve.pointer resolve.atCursor
    resolve.aligned resolve.bytes resolve.sized resolve.inBounds resolve.registered resolve.room resolve.focused
  have queued : resolve.record.index.isSome = true := by rw [resolve.indexed]; rfl
  dsimp only at run
  simp only [queued, ite_true, Bool.toNat_true] at run
  exact ⟨run.1, ⟨_, run.2, rfl, resolve.indexed, rfl⟩⟩

theorem resolutionPoll (resolve : LinkedResolution initial subtask index) {between}
    (path : Retaining profile ready (specDispatch ready impl) subtask index resolve.committed between parked)
    (poll : ParkedPoll parked subtask profile) :
    poll.steps index ready impl initial (List.replicate 17 .tau ++ between) := by
  obtain ⟨resolved, pending⟩ := resolutionIndexed (profile := profile) (ready := ready) (impl := impl) resolve
  obtain ⟨advanced, record, live, returned, indexed, queued⟩ := retainingPath path pending
  have leading := appendSteps resolved advanced
  have observed := parked_poll_returned (prof := profile) (ready := ready) impl poll.memory poll.slot poll.out poll.ws
    poll.thread poll.active poll.task poll.instance_ poll.core poll.next poll.focused poll.callout poll.liveThread poll.liveTask
    poll.liveInst poll.mayLeave poll.handle poll.set poll.perm subtask record index poll.setLive poll.member poll.allowed poll.selects
    live returned indexed queued
  unfold ParkedPoll.steps
  constructor
  · intro misaligned
    simpa only [List.append_assoc, ParkedPoll.delivered] using appendSteps leading (observed.1 misaligned)
  · intro size aligned sized
    have outcome := observed.2 size aligned sized
    constructor
    · intro bounded
      simpa only [List.append_assoc, ParkedPoll.delivered] using appendSteps leading (outcome.1 bounded)
    · intro outside
      simpa only [List.append_assoc, ParkedPoll.delivered] using appendSteps leading (outcome.2 outside)

theorem pendingJoin {E : CoreEngine} {store : CStore E} {subtask : SubtaskId}
    (pending : PendingAt store subtask index) (waitable : Waitable) (set : Option WsetId) :
    PendingAt (store.joinSt waitable set) subtask index := by
  obtain ⟨record, live, returned, indexed, queued⟩ := pending
  unfold CStore.joinSt
  split
  · exact ⟨record, live, returned, indexed, queued⟩
  · rename_i common found
    let base := match common.wset with
      | some old => ArenaField.wsets.modify store old fun x => { x with elems := x.elems.erase waitable }
      | none => store
    have baseLive : base.subtask? subtask = some record := by
      dsimp [base]
      split <;> exact live
    have kept : PendingAt (base.modifyWaitableCommon waitable fun common => { common with wset := set }) subtask index := by
      cases waitable with
      | end_ endpoint => exact ⟨record, baseLive, returned, indexed, queued⟩
      | subtask other =>
        by_cases same : other = subtask
        · subst other
          refine ⟨{ record with common := { record.common with wset := set } }, ?_, returned, indexed, queued⟩
          change ArenaField.subtasks.get? base subtask = _ at baseLive
          simp only [CStore.modifyWaitableCommon, CStore.subtask?, ArenaField.get?_modify_self, baseLive, Option.map_some]
        · refine ⟨record, ?_, returned, indexed, queued⟩
          exact (ArenaField.get?_modify_ne ArenaField.subtasks base _ same).trans baseLive
    cases set with
    | none => exact kept
    | some ws =>
      obtain ⟨reached, live, returned, indexed, queued⟩ := kept
      exact ⟨reached, live, returned, indexed, queued⟩

theorem joinStep {E : CoreEngine} {Host : Type} {hr : HostReady Host} {dispatch : Call E → P E Host (Ret E)}
    {state : Config E Host} {subtask : SubtaskId} {thread segments rest}
    (waitable : Waitable) (set : Option WsetId) (next : P E Host (Ret E))
    (focused : state.ctl = ⟨thread, .prog (Waitable.join waitable set >>= fun () => next), segments⟩ :: rest) :
    Retaining profile hr dispatch subtask index state [.tau]
      { state with store := state.store.joinSt waitable set, ctl := ⟨thread, .prog next, segments⟩ :: rest } :=
  .step (Step.modify focused) (fun pending => pendingJoin pending waitable set) (.done _)

theorem deliveredClears (poll : ParkedPoll parked subtask profile) (pending : PendingAt parked.store subtask index) :
    ∃ record, poll.delivered.subtask? subtask = some record ∧ record.common.pending = none ∧
      record.lenders = none ∧ record.state = .returned ∧ record.index = some index := by
  obtain ⟨record, live, returned, indexed, _⟩ := pending
  let shuffled := parked.store.wsetSetElemsSt poll.ws (applyPerm poll.perm poll.set.elems)
  let clear := fun common : WaitableCommon => { common with pending := none }
  let cleared := shuffled.modifyWaitableCommon (.subtask subtask) clear
  let event := { record with common := clear record.common }
  have selected : ArenaField.subtasks.get? shuffled subtask = some record := live
  have clearedAt : cleared.subtask? subtask = some event := by
    simp only [cleared, CStore.modifyWaitableCommon, CStore.subtask?, ArenaField.get?_modify_self,
      selected, Option.map_some, event]
  have frame (lenders : List HandleObjId) (start : CStore (core3 grow)) :
      (lenders.foldl (fun store handle => ArenaField.resHandles.modify store handle fun entry =>
        { entry with numLends := entry.numLends - 1 }) start).subtask? subtask = start.subtask? subtask := by
    induction lenders generalizing start with
    | nil => rfl
    | cons handle rest ih => exact ih (ArenaField.resHandles.modify start handle _)
  refine ⟨{ event with lenders := none }, ?_, rfl, rfl, returned, indexed⟩
  change (cleared.deliverResolveSt subtask).subtask? subtask = _
  rw [CStore.deliverResolveSt, clearedAt]
  rw [CStore.subtask?, ArenaField.get?_modify_self]
  exact congrArg (Option.map fun entry => { entry with lenders := none }) ((frame _ _).trans clearedAt)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery
