module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Thms
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

private theorem resolutionIndexedParked (resolve : LinkedResolution initial subtask index) :
    (∀ saved, ParkedPrefix profile ready (specDispatch ready impl) saved initial (List.replicate 17 .tau) resolve.committed) ∧
      PendingAt resolve.committed.store subtask index := by
  have run := resolve_linked_commit (prof := profile) (ready := ready) (dispatch := specDispatch ready impl)
    resolve.callee resolve.ticket resolve.caller resolve.tree resolve.writer subtask resolve.record resolve.context
    resolve.args resolve.position resolve.callerRecord resolve.live resolve.options resolve.pointer resolve.atCursor
    resolve.aligned resolve.bytes resolve.sized resolve.inBounds resolve.registered resolve.room resolve.focused
  have queued : resolve.record.index.isSome = true := by rw [resolve.indexed]; rfl
  dsimp only at run
  simp only [queued, ite_true, Bool.toNat_true] at run
  exact ⟨run.2.2, ⟨_, run.2.1, rfl, resolve.indexed, rfl⟩⟩

theorem resolutionIndexed (resolve : LinkedResolution initial subtask index) :
    Steps profile ready (specDispatch ready impl) initial (List.replicate 17 .tau) resolve.committed ∧
      PendingAt resolve.committed.store subtask index :=
  let run := resolutionIndexedParked (profile := profile) (ready := ready) (impl := impl) resolve
  ⟨(run.1 ⟨0⟩).reaches.1, run.2⟩

theorem retainingParked {labels saved}
    (path : ParkedRetaining profile ready (specDispatch ready impl) saved subtask index committed labels parked)
    (pending : PendingAt committed.store subtask index) :
    ParkedPrefix profile ready (specDispatch ready impl) saved committed labels parked ∧
      PendingAt parked.store subtask index := by
  induction path with
  | done => exact ⟨.done _, pending⟩
  | step run keepsSlot keepsEvent _ ih =>
    obtain ⟨prefixRun, stillPending⟩ := ih (keepsEvent pending)
    exact ⟨.step run keepsSlot prefixRun, stillPending⟩

theorem pollReturned (poll : ParkedPoll parked subtask profile) (pending : PendingAt parked.store subtask index) :
    poll.steps index ready impl parked [] := by
  obtain ⟨record, live, returned, indexed, queued⟩ := pending
  exact parked_poll_returned (prof := profile) (ready := ready) impl poll.memory poll.slot poll.out poll.ws
    poll.thread poll.active poll.task poll.instance_ poll.core poll.next poll.focused poll.callout poll.liveThread poll.liveTask
    poll.liveInst poll.mayLeave poll.handle poll.set poll.perm subtask record index poll.setLive poll.member poll.allowed poll.selects
    live returned indexed queued

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

private theorem consumeRecord (store : CStore (core3 grow)) (record : Subtask) (live : store.subtask? subtask = some record) :
    (cancelDelivered store subtask).subtask? subtask = some { record with
      common := { record.common with pending := none }
      lenders := none } := by
  let clear := fun common : WaitableCommon => { common with pending := none }
  let cleared := store.modifyWaitableCommon (.subtask subtask) clear
  let event := { record with common := clear record.common }
  have selected : ArenaField.subtasks.get? store subtask = some record := live
  have clearedAt : cleared.subtask? subtask = some event := by
    simp only [cleared, CStore.modifyWaitableCommon, CStore.subtask?, ArenaField.get?_modify_self,
      selected, Option.map_some, event]
  have frame (lenders : List HandleObjId) (start : CStore (core3 grow)) :
      (lenders.foldl (fun store handle => ArenaField.resHandles.modify store handle fun entry =>
        { entry with numLends := entry.numLends - 1 }) start).subtask? subtask = start.subtask? subtask := by
    induction lenders generalizing start with
    | nil => rfl
    | cons handle rest ih => exact ih (ArenaField.resHandles.modify start handle _)
  change (cleared.deliverResolveSt subtask).subtask? subtask = _
  rw [CStore.deliverResolveSt, clearedAt]
  rw [CStore.subtask?, ArenaField.get?_modify_self]
  exact congrArg (Option.map fun entry => { entry with lenders := none }) ((frame _ _).trans clearedAt)

theorem takePendingResolution (store : CStore (core3 grow)) (record : Subtask)
    (live : store.subtask? subtask = some record) (resolved : record.state.resolved = true)
    (pending : record.common.pending = some (.subtask subtask)) :
    store.takeWaitableEvent (.subtask subtask) =
      (cancelDelivered store subtask, some ⟨.subtask, record.index.getD 0, record.state.toNat⟩) ∧
    (cancelDelivered store subtask).subtask? subtask = some { record with
      common := { record.common with pending := none }, lenders := none } := by
  let erased := store.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none }
  have erasedLive : erased.subtask? subtask = some { record with common := { record.common with pending := none } } := by
    have lookup : ArenaField.subtasks.get? store subtask = some record := live
    simp only [erased, CStore.modifyWaitableCommon, CStore.subtask?, ArenaField.get?_modify_self, lookup, Option.map_some]
  refine ⟨?_, consumeRecord store record live⟩
  simp [CStore.takeWaitableEvent, live, pending, CStore.subtaskEvent, erasedLive, erased, resolved, cancelDelivered]

private theorem consumeClears (store : CStore (core3 grow)) (pending : PendingAt store subtask index) :
    ∃ record, (cancelDelivered store subtask).subtask? subtask = some record ∧ record.common.pending = none ∧
      record.lenders = none ∧ record.state = .returned ∧ record.index = some index := by
  obtain ⟨record, live, returned, indexed, _⟩ := pending
  exact ⟨_, consumeRecord store record live, rfl, rfl, returned, indexed⟩

theorem deliveredClears (poll : ParkedPoll parked subtask profile) (pending : PendingAt parked.store subtask index) :
    ∃ record, poll.delivered.subtask? subtask = some record ∧ record.common.pending = none ∧
      record.lenders = none ∧ record.state = .returned ∧ record.index = some index :=
  consumeClears (parked.store.wsetSetElemsSt poll.ws (applyPerm poll.perm poll.set.elems)) pending

private theorem incrementWaiters_keepsReady (store : CStore (core3 grow)) (ws : WsetId) :
    (store.wsetIncWaitingSt ws).wsetHasEvent ws = store.wsetHasEvent ws := by
  have sameEvent : (store.wsetIncWaitingSt ws).waitableHasEvent = store.waitableHasEvent := by
    funext waitable
    cases waitable <;> rfl
  have updated : (store.wsetIncWaitingSt ws).wset? ws =
      (store.wset? ws).map (fun entry => { entry with numWaiting := entry.numWaiting + 1 }) :=
    ArenaField.get?_modify_self _ _ _ _
  rw [CStore.wsetHasEvent, updated, sameEvent]
  cases live : store.wset? ws <;> simp only [CStore.wsetHasEvent, live, Option.map_some, Option.map_none]

private def waitEntry (wait : ParkedWait initial) : Config (core3 grow) (HostState sig) :=
  { initial with ctl := ⟨some wait.thread, .prog (do
      let event ← wsetWait wait.ws
      let code ← unpackEvent (Builtins.eventCx wait.memory wait.task.inst) (flatNat wait.out) event
      pure (.flat [i32Flat code])), .core wait.core wait.next :: wait.segments⟩ :: wait.rest }

private theorem enterWait (wait : ParkedWait initial) :
    Steps profile ready (specDispatch ready impl) initial (List.replicate 8 .tau) (waitEntry wait) := by
  have admitted : calloutEntry initial.store (some wait.thread) (.builtin (.waitableSetWait wait.memory) wait.task.inst) = none := by
    simp [calloutEntry, instOfThread?, wait.liveThread, wait.liveTask]
  refine .cons (.coreCallout wait.focused wait.callout) ?_
  refine .cons (.currentThread rfl) (.cons (.get rfl) ?_)
  simp [Prog.bind, admitted, calloutBody, builtinProg, withArgs2, Builtins.waitableSetWait, Builtins.enterWaitableBuiltin]
  refine .cons (.currentThread rfl) (.cons (.get rfl) ?_)
  simp [Prog.bind, getTask, getObj, wait.liveThread, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, wait.liveTask, getInst, getObj, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, wait.liveInst, wait.mayLeave, trapIf, handlesGet, getInst, getObj, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, wait.liveInst, wait.handle, orTrap, Builtins.expectWset, pure, Prog.bind_assoc, waitEntry]
  exact .refl _

theorem parkedWaitBlocks (wait : ParkedWait initial) (empty : initial.store.wsetHasEvent wait.ws = false) :
    Steps profile ready (specDispatch ready impl) initial (List.replicate 13 .tau) wait.blocked := by
  have emptyAfter := (incrementWaiters_keepsReady initial.store wait.ws).trans empty
  refine appendSteps (enterWait wait) ?_
  refine .cons (.modify rfl) (.cons (.currentThread rfl) (.cons (.get rfl) ?_))
  simp [waitEntry, ReadyCond.eval, emptyAfter, pure, Prog.bind, Thread.startWaiting, Prog.bind_assoc]
  refine .cons (.modify rfl) (.cons (.block rfl) ?_)
  exact .refl _

theorem parkedWaitReady (wait : ParkedWait initial) (available : initial.store.wsetHasEvent wait.ws = true)
    (early : Bool) (allowed : Allowed profile (.earlyReturn .waitableSetWait) early) :
    Steps profile ready (specDispatch ready impl) initial (ParkedWait.readyLabels early)
      (if early then wait.early else wait.blocked) := by
  have readyAfter := (incrementWaiters_keepsReady initial.store wait.ws).trans available
  refine appendSteps (trailing := [.tau, .tau, .tau, .choice (.earlyReturn .waitableSetWait) early] ++
      List.replicate (if early then 1 else 2) .tau) (enterWait wait) ?_
  refine .cons (.modify rfl) (.cons (.currentThread rfl) (.cons (.get rfl) ?_))
  simp [waitEntry, ReadyCond.eval, readyAfter, pure, Prog.bind, Prog.bind_assoc]
  refine .cons (Step.choose (ck := .earlyReturn .waitableSetWait) early rfl allowed) ?_
  cases early with
  | false =>
    simp [Prog.bind]
    refine .cons (.modify rfl) (.cons (.block rfl) (.refl _))
  | true =>
    simp [Prog.bind]
    exact .cons (.modify rfl) (.refl _)

theorem resumeWait {atResume : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
    (resume : WaitResume wait atResume) (saved : atResume.cont? wait.thread = some wait.saved) :
    Steps profile ready (specDispatch ready impl) atResume (List.replicate 4 .tau) resume.reached := by
  have read := Step.get (prof := profile) (hr := ready) (dispatch := specDispatch ready impl) resume.focused
  simp [Prog.bind, resume.waiting, Thread.stopWaiting] at read
  exact .cons read (.cons (.modify rfl) (.cons (.resumeThread rfl saved) (.cons (.modify rfl) (.refl _))))

theorem resumeTrackedWait {atResume : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
    (resume : WaitResume wait atResume) {leading}
    (prefixRun : ParkedPrefix profile ready (specDispatch ready impl) wait.thread wait.blocked leading atResume) :
    Steps profile ready (specDispatch ready impl) wait.blocked (leading ++ List.replicate 4 .tau) resume.reached := by
  obtain ⟨steps, kept⟩ := prefixRun.reaches
  exact appendSteps steps (resumeWait resume (kept.trans (Config.cont?_setCont_self _ _ _)))

theorem resumeWaitEmpty {atResume : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
    (resume : WaitResume wait atResume) {leading}
    (prefixRun : ParkedPrefix profile ready (specDispatch ready impl) wait.thread wait.blocked leading atResume)
    (record : WaitableSet) (perm : List Nat) (live : resume.reached.store.wset? wait.ws = some record)
    (empty : resume.reached.store.wsetHasEvent wait.ws = false) (allowed : Allowed profile (.shuffle record.elems.length) perm) :
    Steps profile ready (specDispatch ready impl) wait.blocked
      ((leading ++ List.replicate 4 .tau) ++ [.tau, .choice (.shuffle record.elems.length) perm, .tau, .tau,
        .trap (.internal "WaitableSet.get_pending_event: no pending event")])
      (StepDefs.trapCfg { resume.reached with
        store := resume.reached.store.wsetSetElemsSt wait.ws (applyPerm perm record.elems) }) := by
  let reply : EventTuple → Session grow sig (Ret (core3 grow)) := fun event => do
    let code ← unpackEvent (Builtins.eventCx wait.memory wait.task.inst) (flatNat wait.out) event
    pure (.flat [i32Flat code])
  exact appendSteps (resumeTrackedWait resume prefixRun)
    (get_shuffles_empty (config := resume.reached) wait.ws record perm live empty allowed reply rfl)

theorem selectedTickWaiting {atHost : Config (core3 grow) (HostState sig)} {thread : ThreadId}
    (tick : SelectedTick thread atHost ready profile) : tick.atResume.store.threadIs Thread.waiting thread = true := by
  have member : thread ∈ (StepDefs.enterHostSt atHost.store).candidates (ready atHost.host) := by
    rw [tick.candidates]
    have picked : (tick.first :: tick.others)[tick.pick.val]'(by simpa only [List.length_cons] using tick.pick.isLt) ∈
        tick.first :: tick.others := List.getElem_mem _
    simpa only [tick.selected] using picked
  have available := (List.mem_filter.mp member).2
  let entered := StepDefs.enterHostSt atHost.store
  change entered.threadReady (ready atHost.host) thread = true at available
  change entered.threadIs Thread.waiting thread = true
  unfold CStore.threadReady CStore.threadIs at available
  unfold CStore.threadIs
  cases live : entered.thread? thread with
  | none => simp [live] at available
  | some record =>
    rw [live] at available
    cases condition : record.readyCond <;> simp [Thread.ready, Thread.waiting, condition] at available ⊢
    exact available.1

theorem selectTick {atHost : Config (core3 grow) (HostState sig)} {thread : ThreadId}
    (tick : SelectedTick thread atHost ready profile) :
    Steps profile ready (specDispatch ready impl) atHost tick.selectionLabels tick.atResume := by
  refine .cons (.hostTick tick.hostReady) (.cons (.modify rfl) (.cons (.get rfl) (.cons (.hostGet rfl) ?_)))
  simp [Prog.bind, tick.candidates, pickTick, Prog.bind_assoc]
  let resumePick : Fin (tick.others.length + 1) → Session grow sig (Ret (core3 grow)) := fun pick =>
    Thread.resume ((tick.first :: tick.others)[pick.val]'(by simpa only [List.length_cons] using pick.isLt)) >>=
      fun () => modifyStore StepDefs.leaveHostSt >>= fun () => pure .unit
  refine .cons (Step.choose (ck := .tickPick tick.others.length) (k := resumePick) tick.pick rfl tick.allowed) ?_
  simp only [resumePick, tick.selected]
  exact .refl _

theorem resumeWaitTick {atHost : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
    (tick : WaitTick wait atHost ready profile) (saved : atHost.cont? wait.thread = some wait.saved) :
    Steps profile ready (specDispatch ready impl) atHost tick.labels tick.reached :=
  appendSteps (selectTick tick) (resumeWait (atResume := tick.atResume)
    ⟨none, _, [], [], rfl, selectedTickWaiting tick⟩ saved)

private theorem waitDelivery {reached : Config (core3 grow) (HostState sig)} {wait : ParkedWait parked}
    (delivery : WaitDelivery wait reached profile subtask)
    (focused : reached.ctl = ⟨some wait.thread, .prog wait.takeEvent,
      .core wait.core wait.next :: wait.segments⟩ :: reached.ctl.drop 1)
    (pending : PendingAt reached.store subtask index) {labels}
    (prefixRun : Steps profile ready (specDispatch ready impl) initial labels reached) :
    delivery.outcomes index ready impl initial labels := by
  obtain ⟨record, live, returned, indexed, queued⟩ := pending
  let cx := Builtins.eventCx (E := core3 grow) wait.memory wait.task.inst
  let reply : Nat → Session grow sig (Ret (core3 grow)) := fun code => pure (.flat [i32Flat code])
  let handleEvent := fun event => unpackEvent cx (flatNat wait.out) event >>= reply
  let event : EventTuple := ⟨.subtask, index, SubtaskState.returned.toNat⟩
  let consumed := { reached with
    store := delivery.delivered
    ctl := ⟨some wait.thread, .prog (handleEvent event), .core wait.core wait.next :: wait.segments⟩ :: reached.ctl.drop 1 }
  have taken : Steps profile ready (specDispatch ready impl) reached delivery.labels consumed :=
    get_delivers_returned (config := reached) wait.ws delivery.set delivery.perm subtask record index
      delivery.setLive delivery.allowed delivery.selects live returned indexed queued handleEvent
      (by simpa [ParkedWait.takeEvent, handleEvent, reply, cx, pure] using focused)
  have leading := appendSteps prefixRun taken
  constructor
  · intro misaligned
    exact appendSteps leading (unpack_event_bad_alignment (config := consumed) cx (flatNat wait.out) event misaligned reply rfl)
  · intro size aligned sized
    constructor
    · intro bounded
      have write := unpack_event_write (prof := profile) (ready := ready) (dispatch := specDispatch ready impl)
        (config := consumed) cx (flatNat wait.out) wait.memory size event aligned rfl sized bounded reply rfl
      exact appendSteps leading (appendSteps write (.cons (.popCore rfl) (.refl _)))
    · intro outside
      exact appendSteps leading (unpack_event_bad_range (config := consumed) cx (flatNat wait.out) wait.memory size event
        aligned rfl sized outside reply rfl)

theorem waitDeliveryAtSelection {wait : ParkedWait parked} (delivery : WaitDelivery wait initial profile subtask)
    (focused : initial.ctl = ⟨some wait.thread, .prog wait.takeEvent,
      .core wait.core wait.next :: wait.segments⟩ :: initial.ctl.drop 1)
    (pending : PendingAt initial.store subtask index) : delivery.outcomes index ready impl initial [] :=
  waitDelivery delivery focused pending (.refl _)

theorem earlyWaitDelivery (wait : ParkedWait initial) (available : initial.store.wsetHasEvent wait.ws = true)
    (allowed : Allowed profile (.earlyReturn .waitableSetWait) true)
    (delivery : WaitDelivery wait wait.early profile subtask) (pending : PendingAt initial.store subtask index) :
    delivery.outcomes index ready impl initial (ParkedWait.readyLabels true) :=
  waitDelivery delivery rfl pending (parkedWaitReady wait available true allowed)

theorem resumedWaitDelivery {atResume : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
    (resume : WaitResume wait atResume) {leading}
    (prefixRun : ParkedRetaining profile ready (specDispatch ready impl) wait.thread subtask index
      wait.blocked leading atResume)
    (pending : PendingAt wait.blocked.store subtask index)
    (delivery : WaitDelivery wait resume.reached profile subtask) :
    delivery.outcomes index ready impl wait.blocked (leading ++ List.replicate 4 .tau) := by
  obtain ⟨kept, queued⟩ := retainingParked prefixRun pending
  exact waitDelivery delivery rfl queued (resumeTrackedWait resume kept)

theorem resolutionWait {atHost : Config (core3 grow) (HostState sig)} {wait : ParkedWait parked}
    {tick : WaitTick wait atHost ready profile} (delivery : WaitDelivery wait tick.reached profile subtask)
    (resolve : LinkedResolution initial subtask index) {between}
    (path : Retaining profile ready (specDispatch ready impl) subtask index resolve.committed between atHost)
    (saved : atHost.cont? wait.thread = some wait.saved) :
    delivery.outcomes index ready impl initial ((List.replicate 17 .tau ++ between) ++ tick.labels) := by
  obtain ⟨commitRun, queued⟩ := resolutionIndexed (profile := profile) (ready := ready) (impl := impl) resolve
  obtain ⟨replay, pending⟩ := retainingPath path queued
  exact waitDelivery delivery rfl pending (appendSteps (appendSteps commitRun replay) (resumeWaitTick tick saved))

theorem blockedResolutionWait {atHost resolving : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
    {tick : WaitTick wait atHost ready profile} (delivery : WaitDelivery wait tick.reached profile subtask)
    (empty : initial.store.wsetHasEvent wait.ws = false) {whileBlocked between}
    (runs : ParkedPrefix profile ready (specDispatch ready impl) wait.thread wait.blocked whileBlocked resolving)
    (resolve : LinkedResolution resolving subtask index)
    (path : ParkedRetaining profile ready (specDispatch ready impl) wait.thread subtask index resolve.committed between atHost) :
    delivery.outcomes index ready impl initial
      ((((List.replicate 13 .tau ++ whileBlocked) ++ List.replicate 17 .tau) ++ between) ++ tick.labels) := by
  obtain ⟨commitRun, queued⟩ := resolutionIndexedParked (profile := profile) (ready := ready) (impl := impl) resolve
  obtain ⟨replay, pending⟩ := retainingParked path queued
  obtain ⟨before, keptBefore⟩ := runs.reaches
  obtain ⟨commits, keptCommit⟩ := (commitRun wait.thread).reaches
  obtain ⟨after, keptAfter⟩ := replay.reaches
  have saved : atHost.cont? wait.thread = some wait.saved := by
    rw [keptAfter, keptCommit, keptBefore]
    exact Config.cont?_setCont_self _ _ _
  have blocked := parkedWaitBlocks (profile := profile) (ready := ready) (impl := impl) wait empty
  exact waitDelivery delivery rfl pending
    (appendSteps (appendSteps (appendSteps (appendSteps blocked before) commits) after) (resumeWaitTick tick saved))

private def cancelResultWords (subtask : SubtaskId) (resolved : Bool) : Session grow sig (List FlatValue) :=
  if resolved then Builtins.subtaskCancelDeliver subtask else pure [i32Flat (subtaskCancelResult none)]

private theorem cancelEntry (cancel : ParkedCancel parked subtask) (record : Subtask)
    (live : parked.store.subtask? subtask = some record)
    (notDelivered : record.lenders.isSome = true) (notRequested : record.cancellationRequested = false)
    (notJoined : record.common.wset = none) :
    Steps profile ready (specDispatch ready impl) parked (List.replicate 11 .tau)
      { parked with ctl := ⟨some cancel.thread, .prog ((if record.state.resolved then Builtins.subtaskCancelDeliver subtask
          else Builtins.subtaskCancelRequest cancel.async_ subtask record.onCancel >>= cancelResultWords subtask) >>=
        fun words => pure (.flat words)),
        .core cancel.core cancel.next :: cancel.segments⟩ :: cancel.rest } := by
  have admitted : calloutEntry parked.store (some cancel.thread) (.builtin (.subtaskCancel cancel.async_) cancel.task.inst) = none := by
    simp [calloutEntry, instOfThread?, cancel.liveThread, cancel.liveTask]
  have arena : ArenaField.subtasks.get? parked.store subtask = some record := live
  have canDeliver : parked.store.subtaskResolveDelivered subtask = false := by
    simp only [CStore.subtaskResolveDelivered, live]
    cases l : record.lenders <;> simp [l] at notDelivered ⊢
  have outside : ((parked.store.waitableCommon? (.subtask subtask)).bind (·.wset)).isSome = false := by
    simp [CStore.waitableCommon?, live, notJoined]
  refine .cons (.coreCallout cancel.focused cancel.callout) (.cons (.currentThread rfl) (.cons (.get rfl) ?_))
  simp [Prog.bind, admitted, calloutBody, builtinProg, withArgs1, Builtins.subtaskCancel, Builtins.enterWaitableBuiltin]
  refine .cons (.currentThread rfl) (.cons (.get rfl) ?_)
  simp [Prog.bind, getTask, getObj, cancel.liveThread, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, cancel.liveTask, getInst, getObj, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, cancel.liveInst, cancel.mayLeave, trapIf, handlesGet, getInst, getObj, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, cancel.liveInst, cancel.handle, orTrap, Builtins.expectSubtask, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, canDeliver, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, arena, notRequested]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, outside, pure]
  exact .refl _

theorem cancelRequests (cancel : ParkedCancel parked subtask) (record : Subtask)
    (live : parked.store.subtask? subtask = some record) (unresolved : record.state.resolved = false)
    (notDelivered : record.lenders.isSome = true) (notRequested : record.cancellationRequested = false)
    (notJoined : record.common.wset = none) :
    Steps profile ready (specDispatch ready impl) parked (List.replicate 14 .tau)
      (cancel.callbackEntry record ready impl) := by
  have admission := cancelEntry (profile := profile) (ready := ready) (impl := impl) cancel record live
    notDelivered notRequested notJoined
  simp only [unresolved, Bool.false_eq_true, ite_false] at admission
  have normalize : ((Builtins.subtaskCancelRequest cancel.async_ subtask record.onCancel >>= cancelResultWords subtask) >>=
      fun words => pure (.flat words) : Session grow sig (Ret (core3 grow))) = (do
      let thread ← currentThreadId
      modifyStore (Builtins.WaitableSt.requestCancel subtask thread)
      let returned ← callRet (.onCancel record.onCancel)
      cancel.afterCallback returned) := by
    simp only [Builtins.subtaskCancelRequest, ParkedCancel.afterCallback, ParkedCancel.finish, callUnit, ParkedCancel.result,
      cancelResultWords, bind_assoc]
    congr 1
    funext runningThread
    congr 1
    funext ignored
    congr 1
    funext returned
    cases returned <;> rfl
  rw [normalize] at admission
  refine appendSteps admission (.cons (.currentThread rfl) (.cons (.modify rfl) (.cons (.call rfl) ?_)))
  change Steps profile ready (specDispatch ready impl) _ [] _
  exact .refl _

private def reentryAt (cancel : ParkedCancel parked subtask) (request : TaskCancelAdmission cancel) :
    Config (core3 grow) (HostState sig) :=
  { parked with
    store := request.markedStore
    ctl := ⟨some cancel.thread, .prog (Thread.resume request.implicitThread >>= fun () => pure .unit),
      .prog cancel.afterCallback :: .core cancel.core cancel.next :: cancel.segments⟩ :: cancel.rest }

private theorem taskCancelResume (cancel : ParkedCancel parked subtask) (request : TaskCancelAdmission cancel)
    {callee : Activation (core3 grow) (HostState sig)} (saved : parked.cont? request.implicitThread = some callee) :
    Steps profile ready (specDispatch ready impl) (reentryAt cancel request)
      (List.replicate (if request.waiting then 3 else 2) .tau) (request.reentered callee) := by
  have focus : (reentryAt cancel request).ctl =
      ⟨some cancel.thread, .prog (Thread.resume request.implicitThread >>= fun () => pure .unit),
        .prog cancel.afterCallback :: .core cancel.core cancel.next :: cancel.segments⟩ :: cancel.rest := rfl
  have waitingAt : (reentryAt cancel request).store.threadIs Thread.waiting request.implicitThread = request.waiting := rfl
  have read := Step.get (prof := profile) (hr := ready) (dispatch := specDispatch ready impl) focus
  cases waiting : request.waiting with
  | false =>
    simp [Prog.bind, waitingAt, waiting, pure] at read
    simp only [TaskCancelAdmission.reentered, waiting, Bool.false_eq_true, ite_false]
    exact .cons read (.cons (.resumeThread rfl saved) (.refl _))
  | true =>
    simp [Prog.bind, waitingAt, waiting, Thread.stopWaiting] at read
    simp only [TaskCancelAdmission.reentered, waiting, ite_true]
    exact .cons read (.cons (.modify rfl) (.cons (.resumeThread rfl saved) (.refl _)))

theorem taskCancelReenters (cancel : ParkedCancel parked subtask) (request : TaskCancelAdmission cancel)
    (mode : TaskCancelReentry request ready) {callee : Activation (core3 grow) (HostState sig)}
    (saved : parked.cont? request.implicitThread = some callee) :
    Steps profile ready (specDispatch ready impl) parked (List.replicate request.reentrySteps .tau)
      (request.reentered callee) := by
  let marked := cancel.callbackEntry request.record ready impl
  have taskLive : ArenaField.tasks.get? (cancel.callbackEntry request.record ready impl).store
      request.taskId = some request.callee := request.taskLive
  have threadLive : ArenaField.threads.get? ((cancel.callbackEntry request.record ready impl).store.setTaskState
      request.taskId .pendingCancel) request.implicitThread = some request.implicitState := request.threadLive
  have called : marked.ctl = ⟨some cancel.thread, .prog (do
      Task.requestCancellation ready request.taskId
      pure .unit), .prog cancel.afterCallback :: .core cancel.core cancel.next :: cancel.segments⟩ :: cancel.rest := by
    simp [marked, ParkedCancel.callbackEntry, request.callback, specDispatch, dispatch, onCancelProg]
  have requested := cancelRequests (profile := profile) (ready := ready) (impl := impl) cancel request.record request.live
    request.unresolved request.notDelivered request.notRequested request.notJoined
  have selected : Steps profile ready (specDispatch ready impl) parked
      (List.replicate (if request.callee.state = .initial then 16 else 19) .tau) (reentryAt cancel request) := by
    cases mode with
    | initial state =>
      rw [ite_eq_left state]
      refine appendSteps requested (.cons (.get called) ?_)
      simp [Prog.bind, taskLive, state, request.implicitLive, orTrap, pure]
      exact .cons (.modify rfl) (.refl _)
    | started state cancellable available =>
      have different : request.callee.state ≠ .initial := by simp [state]
      change CStore.threadReady (ready (cancel.callbackEntry request.record ready impl).host)
        ((cancel.callbackEntry request.record ready impl).store.setTaskState request.taskId .pendingCancel)
        request.implicitThread = true at available
      rw [ite_eq_right different]
      refine appendSteps requested (.cons (.get called) ?_)
      simp [Prog.bind, taskLive, state, request.implicitLive, orTrap, pure, Prog.bind_assoc]
      refine .cons (.modify rfl) (.cons (.get rfl) ?_)
      simp [Prog.bind, threadLive, pure]
      refine .cons (.get rfl) (.cons (.hostGet rfl) ?_)
      simp [Prog.bind, cancellable, available, pure]
      exact .refl _
  rw [TaskCancelAdmission.reentrySteps, List.replicate_add]
  exact appendSteps selected (taskCancelResume cancel request saved)

variable {thread : ThreadId} {taskId : TaskId} {atWait : Config (core3 grow) (HostState sig)}

theorem k1GateSteps {atGate : Config (core3 grow) (HostState sig)} (entry : K1GateEntry atGate thread taskId) :
    Steps profile ready (specDispatch ready impl) atGate (List.replicate 4 .tau) entry.waitingEntry := by
  have liveTask : ArenaField.tasks.get? atGate.store taskId = some entry.task := entry.liveTask
  have marked : ArenaField.tasks.get? (atGate.store.setImplicitThread taskId thread) taskId = some entry.markedTask := by
    simp only [CStore.setImplicitThread, ArenaField.get?_modify_self, liveTask, Option.map_some, K1GateEntry.markedTask]
  have liveInst : ArenaField.insts.get? (atGate.store.setImplicitThread taskId thread) entry.markedTask.inst = some entry.instance_ :=
    entry.liveInst
  have asyncMarked : entry.markedTask.ft.async_ = true := entry.asynchronous
  have sameExclusive : entry.markedTask.needsExclusive = entry.task.needsExclusive := rfl
  have gated : entry.instance_.hasBackpressure entry.markedTask.needsExclusive = true ∨
      0 < entry.instance_.numWaitingToEnter := by
    rw [sameExclusive]
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using entry.gated
  have start := Step.currentThread (prof := profile) (hr := ready) (dispatch := specDispatch ready impl) entry.focused
  simp [Prog.bind, pure, Prog.bind_assoc] at start
  refine .cons start (.cons (.modify rfl) (.cons (.get rfl) ?_))
  simp [Prog.bind, marked, asyncMarked, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, liveInst, Quirks.none, gated, pure, Prog.bind_assoc, K1GateEntry.waitingEntry]
  exact .refl _

theorem k1Blocks (wait : K1Wait atWait thread taskId) (unready : wait.condition.eval (fun _ => false) wait.incremented = false) :
    Steps profile ready (specDispatch ready impl) atWait (List.replicate 5 .tau) wait.blocked := by
  have enter := Step.modify (prof := profile) (hr := ready) (dispatch := specDispatch ready impl) wait.focused
  refine .cons enter (.cons (.currentThread rfl) (.cons (.get rfl) ?_))
  change ReadyCond.eval (fun _ => false) (ArenaOps.updateSt ArenaField.insts wait.instance_
    InstState.incWaitingToEnter atWait.store) (.backpressure wait.instance_ wait.exclusive) = false at unready
  simp [Prog.bind, unready, pure, Thread.startWaiting, Prog.bind_assoc]
  exact .cons (.modify rfl) (.cons (.block rfl) (.refl _))

theorem liftK1Gate {atGate : Config (core3 grow) (HostState sig)} (callee : (core3 grow).FuncAddr)
    (task : Task (core3 grow)) (instance_ : InstState) (rest : List (Activation (core3 grow) (HostState sig)))
    (focused : atGate.ctl = ⟨some thread, .prog (liftThreadBody .spec .none taskId callee), []⟩ :: rest)
    (liveTask : atGate.store.task? taskId = some task) (asynchronous : task.ft.async_ = true)
    (liveInst : atGate.store.inst? task.inst = some instance_)
    (gated : (instance_.hasBackpressure task.needsExclusive || decide (instance_.numWaitingToEnter > 0)) = true) :
    ∃ entry : K1GateEntry atGate thread taskId,
      Steps profile ready (specDispatch ready impl) atGate (List.replicate 4 .tau) entry.waitingEntry ∧
      entry.wait.next false = .pure .unit ∧ entry.wait.segments = [] ∧ entry.next = liftAdmissionTail taskId callee := by
  have body : liftThreadBody .spec .none taskId callee =
      (Task.enterImplicitThread .none taskId >>= liftAdmissionTail (sig := sig) taskId callee) := rfl
  let entry : K1GateEntry atGate thread taskId :=
    ⟨task, instance_, liftAdmissionTail taskId callee, [], rest, by rw [focused, body], liveTask, asynchronous, liveInst, gated⟩
  exact ⟨entry, k1GateSteps entry, rfl, rfl, rfl⟩

private def k1Check (wait : K1Wait atWait thread taskId) (atResume : Config (core3 grow) (HostState sig))
    (task : Task (core3 grow)) (rest : List (Activation (core3 grow) (HostState sig))) :
    Config (core3 grow) (HostState sig) :=
  { atResume with
    store := wait.deliveredStore atResume.store
    ctl := ⟨some thread, .prog (trapIf (decide (task.numBorrows > 0)) .borrowsRemain >>= fun () =>
      callRet (.onResolve task.caller none) >>= wait.afterResolve), wait.segments⟩ :: rest }

private theorem k1CheckRun (wait : K1Wait atWait thread taskId) {atResume : Config (core3 grow) (HostState sig)}
    {task : Task (core3 grow)} {rest} (focused : atResume.ctl = wait.saved :: rest)
    (live : atResume.store.task? taskId = some task) (pending : task.state = .pendingCancel) :
    Steps profile ready (specDispatch ready impl) atResume (List.replicate 4 .tau) (k1Check wait atResume task rest) := by
  have decLive : ArenaField.tasks.get? (ArenaOps.updateSt ArenaField.insts wait.instance_
      InstState.decWaitingToEnter atResume.store) taskId = some task := live
  have delivered : ArenaField.tasks.get? ((ArenaOps.updateSt ArenaField.insts wait.instance_
      InstState.decWaitingToEnter atResume.store).setTaskState taskId .cancelDelivered) taskId =
      some (task.withState .cancelDelivered) := by
    simp only [CStore.setTaskState, ArenaField.get?_modify_self, decLive, Option.map_some]
  have cancelTail : (callUnit (.onResolve task.caller none)).bind (fun () =>
      (modifyStore (CStore.setTaskState taskId .resolved)).bind (fun () => wait.next false)) =
      (callRet (.onResolve task.caller none)).bind wait.afterResolve := by
    simp [callUnit, callRet, perform, Eff, Prog.lift, Prog.bind, pure]
    apply congrArg (fun tail => Prog.op (S := Eff (core3 grow) (HostState sig))
      (.call (.onResolve task.caller none)) tail)
    funext returned
    cases returned <;> first | rfl | (simp [K1Wait.afterResolve, internal, trap, Eff, Prog.bind]; funext failure; cases failure)
  have start := Step.modify (prof := profile) (hr := ready) (dispatch := specDispatch ready impl) focused
  refine .cons start (.cons (.get rfl) ?_)
  simp [Prog.bind, decLive, pending, pure, Prog.bind_assoc]
  refine .cons (.modify rfl) (.cons (.get rfl) ?_)
  simp [Prog.bind, delivered, Task.withState, trapIf, pure, Prog.bind_assoc, k1Check, cancelTail]
  exact .refl _

theorem k1CancelOutcomes (wait : K1Wait atWait thread taskId) {atResume : Config (core3 grow) (HostState sig)}
    {task : Task (core3 grow)} {rest} (focused : atResume.ctl = wait.saved :: rest)
    (live : atResume.store.task? taskId = some task) (pending : task.state = .pendingCancel) :
    (task.numBorrows = 0 → Steps profile ready (specDispatch ready impl) atResume (List.replicate 5 .tau)
      (wait.resolveEntry atResume task.caller ready impl rest)) ∧
    (task.numBorrows > 0 → Steps profile ready (specDispatch ready impl) atResume
      (List.replicate 4 .tau ++ [.trap .borrowsRemain]) (wait.borrowTrap atResume)) := by
  have leading := k1CheckRun (profile := profile) (ready := ready) (impl := impl) wait focused live pending
  constructor
  · intro empty
    refine appendSteps leading (.cons (.call ?_) (.refl _))
    simp [k1Check, trapIf, empty, callRet, perform]
    rfl
  · intro borrows
    have trapped : (k1Check wait atResume task rest).ctl =
        ⟨some thread, .prog (trap .borrowsRemain), wait.segments⟩ :: rest := by
      simp only [k1Check, trapIf, decide_eq_true borrows, ite_true, Prog.bind_eq, trap]
      simp [Eff, Prog.bind]
      apply congrArg (fun tail => Focus.prog (Prog.op (S := Eff (core3 grow) (HostState sig))
        (.trap .borrowsRemain) tail))
      funext failure
      cases failure
    exact appendSteps leading (.cons (.trap trapped) (.refl _))

theorem k1LowerCancel (wait : K1Wait atWait thread taskId) (atResume : Config (core3 grow) (HostState sig))
    {caller : CallerId} (resolution : LowerCancelResolution (wait.deliveredStore atResume.store) caller subtask)
    (rest : List (Activation (core3 grow) (HostState sig))) :
    Steps profile ready (specDispatch ready impl) (wait.resolveEntry atResume caller ready impl rest)
      (List.replicate resolution.callbackSteps .tau) (resolution.continued wait atResume rest) := by
  have live : ArenaField.subtasks.get? (wait.deliveredStore atResume.store) subtask = some resolution.record := resolution.live
  let progressRecord := { resolution.record with common := { resolution.record.common with pending := some (.subtask subtask) } }
  have queued : ArenaField.subtasks.get? ((wait.deliveredStore atResume.store).setPendingSt
      (.subtask subtask) (.subtask subtask)) subtask = some progressRecord := by
    simp only [CStore.setPendingSt, CStore.modifyWaitableCommon, ArenaField.get?_modify_self, live, Option.map_some, progressRecord]
  have focused : (wait.resolveEntry atResume caller ready impl rest).ctl = ⟨some thread,
      .prog (callerOnResolve .spec .none caller none), .prog wait.afterResolve :: wait.segments⟩ :: rest := by
    rfl
  have selectState : (if resolution.record.state = .starting then
      Subtask.resolve (E := core3 grow) (σ := HostState sig) subtask .cancelledBeforeStarted []
      else Subtask.resolve subtask .cancelledBeforeReturned []) = Subtask.resolve subtask resolution.cancelledState [] := by
    unfold LowerCancelResolution.cancelledState
    split <;> rfl
  have read := Step.get (prof := profile) (hr := ready) (dispatch := specDispatch ready impl) focused
  simp [Prog.bind, K1Wait.resolveEntry, resolution.callerLive, pure] at read
  cases found : resolution.record.index <;>
    simp only [LowerCancelResolution.callbackSteps, found, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
      ite_false, ite_true] <;>
    refine .cons read (.cons (.get rfl) ?_) <;>
    simp [Prog.bind, resolution.callerLive, pure, Quirks.none, Prog.bind_assoc]
  · refine .cons (.get rfl) ?_
    simp [Prog.bind, live, found, pure]
    refine .cons (.get rfl) ?_
    simp [Prog.bind, live, pure, selectState]
    refine .cons (.modify rfl) (.cons (.popProg rfl) (.cons (.modify rfl) ?_))
    simp [LowerCancelResolution.continued, LowerCancelResolution.resolvedStore, LowerCancelResolution.progressStore, found]
    exact .refl _
  · refine .cons (.get rfl) ?_
    simp [Prog.bind, live, found, pure]
    refine .cons (.modify rfl) (.cons (.get rfl) ?_)
    simp [Prog.bind, queued, progressRecord, pure, selectState]
    refine .cons (.modify rfl) (.cons (.popProg rfl) (.cons (.modify rfl) ?_))
    simp [LowerCancelResolution.continued, LowerCancelResolution.resolvedStore, LowerCancelResolution.progressStore, found]
    exact .refl _

theorem lowerCancelRecord {store : CStore (core3 grow)} {caller : CallerId}
    (resolution : LowerCancelResolution store caller subtask) :
    resolution.resolvedStore.subtask? subtask = some resolution.resolvedRecord := by
  have live : ArenaField.subtasks.get? store subtask = some resolution.record := resolution.live
  cases indexed : resolution.record.index <;>
    simp [LowerCancelResolution.resolvedStore, LowerCancelResolution.resolvedRecord, LowerCancelResolution.progressStore,
      CStore.subtask?, CStore.subtaskResolveSt, CStore.setPendingSt, CStore.modifyWaitableCommon,
      ArenaField.get?_modify_self, live, indexed]

theorem lowerCancelNotReturned {store : CStore (core3 grow)} {caller : CallerId}
    (resolution : LowerCancelResolution store caller subtask) (index : Nat) :
    ¬ PendingAt resolution.resolvedStore subtask index := by
  intro pending
  obtain ⟨record, live, returned, _, _⟩ := pending
  rw [lowerCancelRecord resolution, Option.some.injEq] at live
  subst record
  by_cases starting : resolution.record.state = .starting <;>
    simp [LowerCancelResolution.resolvedRecord, LowerCancelResolution.cancelledState, starting] at returned

theorem cancelCallbackDelivers (cancel : ParkedCancel parked subtask) (atExit : Config (core3 grow) (HostState sig))
    (record : Subtask) (focused : atExit.ctl = cancel.callbackTail)
    (live : atExit.store.subtask? subtask = some record)
    (cancelled : record.state = .cancelledBeforeStarted ∨ record.state = .cancelledBeforeReturned)
    (pending : record.common.pending = some (.subtask subtask)) :
    Steps profile ready (specDispatch ready impl) atExit (List.replicate 8 .tau) (cancel.cancelledReply atExit record.state) := by
  have resolved : record.state.resolved = true := by rcases cancelled with state | state <;> simp [state, SubtaskState.resolved]
  have readyBefore : atExit.store.subtaskResolved subtask = true := by simp [CStore.subtaskResolved, live, resolved]
  let cleared := atExit.store.setSyncWaiterSt (.subtask subtask) none
  let current := { record with common := { record.common with hasSyncWaiter := false, syncOwner := none } }
  have before : ArenaField.subtasks.get? atExit.store subtask = some record := live
  have clearedLive : cleared.subtask? subtask = some current := by
    simp only [cleared, CStore.setSyncWaiterSt, CStore.modifyWaitableCommon, CStore.subtask?, ArenaField.get?_modify_self,
      before, Option.map_some, current]
    rfl
  have readyAfter : cleared.subtaskResolved subtask = true := by simp [CStore.subtaskResolved, clearedLive, current, resolved]
  obtain ⟨take, final⟩ := takePendingResolution cleared current clearedLive resolved pending
  change ArenaField.subtasks.get? (cancelDelivered cleared subtask) subtask = _ at final
  simp only [cleared] at readyAfter take final
  have returned := Step.popProg (prof := profile) (hr := ready) (dispatch := specDispatch ready impl) focused
  refine .cons returned (.cons (.get rfl) ?_)
  simp [Prog.bind, readyBefore, pure]
  refine .cons (.modify rfl) (.cons (.get rfl) ?_)
  simp [Prog.bind, readyAfter, ParkedCancel.result, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, take, pure]
  refine .cons (.modify rfl) (.cons (.get rfl) ?_)
  simp [Prog.bind, CStore.takeWaitableEventSt, take, final, pure, current]
  exact .cons (.popCore rfl) (.refl _)

theorem initialK1Cancel {caller : ParkedCancel parked subtask} (request : TaskCancelAdmission caller)
    (wait : K1Wait atWait request.implicitThread request.taskId) {between}
    (path : ParkedPrefix profile ready (specDispatch ready impl) request.implicitThread wait.blocked between parked)
    (initialTask : request.callee.state = .initial) :
    (request.callee.numBorrows = 0 → Steps profile ready (specDispatch ready impl) parked
      (List.replicate request.reentrySteps .tau ++ List.replicate 5 .tau)
      (wait.resolveEntry (request.reentered wait.saved) request.callee.caller ready impl caller.callbackTail)) ∧
    (request.callee.numBorrows > 0 → Steps profile ready (specDispatch ready impl) parked
      (List.replicate request.reentrySteps .tau ++ (List.replicate 4 .tau ++ [.trap .borrowsRemain]))
      (wait.borrowTrap (request.reentered wait.saved))) := by
  have saved := path.reaches.2.trans (Config.cont?_setCont_self _ _ _)
  have entered := taskCancelReenters (profile := profile) (ready := ready) (impl := impl) caller request (.initial initialTask) saved
  have marked : request.markedStore.task? request.taskId = some (request.callee.withState .pendingCancel) := by
    change ArenaField.tasks.get? (ArenaField.tasks.modify (Builtins.WaitableSt.requestCancel subtask caller.thread
      parked.store) request.taskId _) request.taskId = _
    rw [ArenaField.get?_modify_self]
    have live : ArenaField.tasks.get? (Builtins.WaitableSt.requestCancel subtask caller.thread parked.store)
      request.taskId = some request.callee := request.taskLive
    rw [live]
    rfl
  have reached : (request.reentered wait.saved).store.task? request.taskId =
      some (request.callee.withState .pendingCancel) := by
    unfold TaskCancelAdmission.reentered
    split <;> exact marked
  obtain ⟨returned, trapped⟩ := k1CancelOutcomes (profile := profile) (ready := ready) (impl := impl) wait rfl reached rfl
  exact ⟨fun empty => appendSteps entered (returned empty), fun borrows => appendSteps entered (trapped borrows)⟩

theorem initialK1Lower {cancel : ParkedCancel parked subtask} (request : TaskCancelAdmission cancel)
    (wait : K1Wait atWait request.implicitThread request.taskId) {between}
    (path : ParkedPrefix profile ready (specDispatch ready impl) request.implicitThread wait.blocked between parked)
    (initialTask : request.callee.state = .initial) (empty : request.callee.numBorrows = 0)
    (starting : request.record.state = .starting)
    {context : LiftLowerContext (core3 grow)} {args position ft maxParams maxResults}
    (linked : ArenaField.callers.get? parked.store request.callee.caller =
      some (.lower subtask context args position ft maxParams maxResults)) :
    ∃ resolution : LowerCancelResolution (wait.deliveredStore (request.reentered wait.saved).store) request.callee.caller subtask,
      Steps profile ready (specDispatch ready impl) parked
        (List.replicate request.reentrySteps .tau ++ List.replicate 5 .tau ++ List.replicate resolution.callbackSteps .tau)
        (resolution.continued wait (request.reentered wait.saved) cancel.callbackTail) ∧
      resolution.resolvedRecord.state = .cancelledBeforeStarted ∧ resolution.record.index = request.record.index := by
  have reachedCaller : ArenaField.callers.get? (wait.deliveredStore (request.reentered wait.saved).store)
      request.callee.caller = some (.lower subtask context args position ft maxParams maxResults) := by
    unfold K1Wait.deliveredStore TaskCancelAdmission.reentered
    split <;> exact linked
  let marked := { request.record with
    cancellationRequested := true
    common := { request.record.common with hasSyncWaiter := true, syncOwner := some cancel.thread } }
  have markedLive : (request.markedStore).subtask? subtask = some marked := by
    change ArenaField.subtasks.get? (ArenaField.subtasks.modify parked.store subtask _) subtask = _
    rw [ArenaField.get?_modify_self]
    have live : ArenaField.subtasks.get? parked.store subtask = some request.record := request.live
    rw [live]
    rfl
  have reachedSubtask : (wait.deliveredStore (request.reentered wait.saved).store).subtask? subtask = some marked := by
    unfold K1Wait.deliveredStore TaskCancelAdmission.reentered
    split <;> exact markedLive
  let resolution : LowerCancelResolution (wait.deliveredStore (request.reentered wait.saved).store)
      request.callee.caller subtask :=
    ⟨context, args, position, ft, maxParams, maxResults, marked, reachedCaller, reachedSubtask, rfl, .inl starting⟩
  refine ⟨resolution, appendSteps ((initialK1Cancel request wait path initialTask).1 empty)
    (k1LowerCancel wait _ resolution _), ?_, rfl⟩
  simp [resolution, LowerCancelResolution.resolvedRecord, LowerCancelResolution.cancelledState, marked, starting]

theorem initialK1Delivers {cancel : ParkedCancel parked subtask} (request : TaskCancelAdmission cancel)
    (wait : K1Wait atWait request.implicitThread request.taskId) {between}
    (path : ParkedPrefix profile ready (specDispatch ready impl) request.implicitThread wait.blocked between parked)
    (initialTask : request.callee.state = .initial) (empty : request.callee.numBorrows = 0)
    (starting : request.record.state = .starting) (indexed : request.record.index = some index)
    (cancelledTail : wait.next false = .pure .unit) (emptySegments : wait.segments = [])
    {context : LiftLowerContext (core3 grow)} {args position ft maxParams maxResults}
    (linked : ArenaField.callers.get? parked.store request.callee.caller =
      some (.lower subtask context args position ft maxParams maxResults)) :
    ∃ exited,
      Steps profile ready (specDispatch ready impl) parked
        (List.replicate request.reentrySteps .tau ++ List.replicate 13 .tau ++ [.tau]) exited ∧
      Steps profile ready (specDispatch ready impl) exited (List.replicate 8 .tau)
        (cancel.cancelledReply exited .cancelledBeforeStarted) := by
  obtain ⟨resolution, resolved, cancelled, sameIndex⟩ := initialK1Lower request wait path initialTask empty starting linked
  let atResume := request.reentered wait.saved
  let exited := { atResume with
    store := StepDefs.threadStatusSt request.implicitThread .exited (resolution.resolvedStore.setTaskState request.taskId .resolved)
    ctl := cancel.callbackTail }
  have exit : Step profile ready (specDispatch ready impl) (resolution.continued wait atResume cancel.callbackTail) .tau exited :=
    Step.threadExit (r := .unit) (by simp [LowerCancelResolution.continued, cancelledTail, emptySegments])
  have live : exited.store.subtask? subtask = some resolution.resolvedRecord := lowerCancelRecord resolution
  have pending : resolution.resolvedRecord.common.pending = some (.subtask subtask) := by
    simp [LowerCancelResolution.resolvedRecord, sameIndex, indexed]
  have run := cancelCallbackDelivers (profile := profile) (ready := ready) (impl := impl)
    cancel exited resolution.resolvedRecord rfl live (.inl cancelled) pending
  refine ⟨exited, ?_, by simpa only [cancelled] using run⟩
  have cut := appendSteps resolved (.cons exit (.refl _))
  simpa only [LowerCancelResolution.callbackSteps, sameIndex, indexed, Option.isSome_some, ite_true,
    ← List.replicate_add, List.append_assoc] using cut

private theorem startedCancelMarked (cancel : ParkedCancel parked subtask) (request : StartedCancel cancel) :
    request.callbackReturned.store.subtask? subtask = some { request.record with
      cancellationRequested := true
      common := { request.record.common with hasSyncWaiter := true, syncOwner := some cancel.thread } } := by
  change ArenaField.subtasks.get? (ArenaField.subtasks.modify parked.store subtask _) subtask = _
  rw [ArenaField.get?_modify_self]
  have requestLive := request.live
  rw [CStore.subtask?] at requestLive
  rw [requestLive]
  rfl

theorem cancelStartedReturns (cancel : ParkedCancel parked subtask) (request : StartedCancel cancel) :
    Steps profile ready (specDispatch ready impl) parked (List.replicate 20 .tau) request.callbackReturned := by
  let marked := cancel.callbackEntry request.record ready impl
  have taskLive : ArenaField.tasks.get? (cancel.callbackEntry request.record ready impl).store
      request.taskId = some request.callee := request.taskLive
  have threadLive : ArenaField.threads.get? ((cancel.callbackEntry request.record ready impl).store.setTaskState
      request.taskId .pendingCancel) request.implicitThread = some request.implicitState := request.threadLive
  have called : marked.ctl = ⟨some cancel.thread, .prog (do
      Task.requestCancellation ready request.taskId
      pure .unit), .prog cancel.afterCallback :: .core cancel.core cancel.next :: cancel.segments⟩ :: cancel.rest := by
    simp [marked, ParkedCancel.callbackEntry, request.callback, specDispatch, dispatch, onCancelProg]
  have requested := cancelRequests (profile := profile) (ready := ready) (impl := impl) cancel request.record request.live
    request.unresolved request.notDelivered request.notRequested request.notJoined
  refine appendSteps requested (.cons (.get called) ?_)
  simp [Prog.bind, taskLive, request.started, request.implicitLive, orTrap, pure, Prog.bind_assoc]
  refine .cons (.modify rfl) (.cons (.get rfl) ?_)
  simp [Prog.bind, threadLive, pure]
  refine .cons (.get rfl) (.cons (.hostGet rfl) ?_)
  simp [Prog.bind, request.notCancellable, pure]
  exact .cons (.popProg rfl) (.refl _)

theorem cancelStartedBlocked (cancel : ParkedCancel parked subtask) (request : StartedCancel cancel)
    (asynchronous : cancel.async_ = true) :
    Steps profile ready (specDispatch ready impl) parked (List.replicate 24 .tau) request.resumed := by
  have live := startedCancelMarked cancel request
  have stillUnresolved : request.settledStore.subtaskResolved subtask = false := by
    change (request.callbackReturned.store.setSyncWaiterSt (.subtask subtask) none).subtaskResolved subtask = false
    simp only [CStore.subtaskResolved, CStore.setSyncWaiterSt, CStore.modifyWaitableCommon, CStore.subtask?,
      ArenaField.get?_modify_self, show ArenaField.subtasks.get? request.callbackReturned.store subtask = _ from live,
      Option.map_some, request.unresolved]
  change (request.toTaskCancelAdmission.markedStore.setSyncWaiterSt (.subtask subtask) none).subtaskResolved subtask = false
    at stillUnresolved
  refine appendSteps (cancelStartedReturns cancel request) (.cons (.get rfl) ?_)
  simp [StartedCancel.callbackReturned, ParkedCancel.afterCallback, Builtins.subtaskCancelSyncWait,
    Prog.bind, asynchronous, pure, ParkedCancel.finish]
  refine .cons (.modify rfl) (.cons (.get rfl) ?_)
  simp [Prog.bind, stillUnresolved, ParkedCancel.result, pure]
  exact .cons (.popCore rfl) (.refl _)

def startedCancelWait (cancel : ParkedCancel parked subtask) (request : StartedCancel cancel)
    (synchronous : cancel.async_ = false) : SyncCancelWait cancel request.callbackReturned :=
  ⟨synchronous, by simp only [CStore.subtaskResolved, startedCancelMarked cancel request,
    request.unresolved], cancel.rest, rfl⟩

theorem syncCancelBlocks {atReturn} (cancel : ParkedCancel parked subtask) (wait : SyncCancelWait cancel atReturn) :
    Steps profile ready (specDispatch ready impl) atReturn (List.replicate 5 .tau) wait.blocked := by
  have read := Step.get (prof := profile) (hr := ready) (dispatch := specDispatch ready impl) wait.focused
  simp [Prog.bind, pure, wait.synchronous,
    wait.unresolved, Thread.waitUntilGuest, Thread.waitUntil, Prog.bind_assoc] at read
  refine .cons read (.cons (.currentThread rfl) (.cons (.get rfl) ?_))
  simp [ReadyCond.eval, wait.unresolved, Prog.bind, pure, Thread.startWaiting]
  exact .cons (.modify rfl) (.cons (.block rfl) (.refl _))

theorem startedCancelBlocks (cancel : ParkedCancel parked subtask) (request : StartedCancel cancel)
    (synchronous : cancel.async_ = false) :
    Steps profile ready (specDispatch ready impl) parked (List.replicate 25 .tau)
      (startedCancelWait cancel request synchronous).blocked := by
  rw [show (25 : Nat) = 20 + 5 by rfl, List.replicate_add]
  exact appendSteps (cancelStartedReturns cancel request)
    (syncCancelBlocks cancel (startedCancelWait cancel request synchronous))

theorem resumeSyncCancel {atResume} (cancel : ParkedCancel parked subtask)
    (resume : SyncCancelResume cancel atResume) (saved : atResume.cont? cancel.thread = some cancel.saved) :
    Steps profile ready (specDispatch ready impl) atResume (List.replicate 3 .tau) resume.reached := by
  have read := Step.get (prof := profile) (hr := ready) (dispatch := specDispatch ready impl) resume.focused
  simp [Prog.bind, resume.waiting, Thread.stopWaiting] at read
  exact .cons read (.cons (.modify rfl) (.cons (.resumeThread rfl saved) (.refl _)))

theorem syncCancelResumes {atReturn atResume leading} (cancel : ParkedCancel parked subtask)
    (wait : SyncCancelWait cancel atReturn) (resume : SyncCancelResume cancel atResume)
    (prefixRun : ParkedPrefix profile ready (specDispatch ready impl) cancel.thread wait.blocked leading atResume) :
    Steps profile ready (specDispatch ready impl) wait.blocked (leading ++ List.replicate 3 .tau) resume.reached := by
  have saved : wait.blocked.cont? cancel.thread = some cancel.saved := Config.cont?_setCont_self _ _ _
  obtain ⟨run, reached⟩ := prefixRun.reaches
  exact appendSteps run (resumeSyncCancel cancel resume (reached.trans saved))

theorem syncCancelDelivers {atResume} (cancel : ParkedCancel parked subtask)
    (resume : SyncCancelResume cancel atResume) (pending : PendingAt atResume.store subtask index) :
    Steps profile ready (specDispatch ready impl) resume.reached (List.replicate 6 .tau) resume.delivered := by
  obtain ⟨record, live, returned, indexed, queued⟩ := pending
  let cleared := resume.reached.store.setSyncWaiterSt (.subtask subtask) none
  let changed := { record with common := { record.common with hasSyncWaiter := false, syncOwner := none } }
  have before : ArenaField.subtasks.get? resume.reached.store subtask = some record := live
  have clearedLive : cleared.subtask? subtask = some changed := by
    simp only [cleared, changed, CStore.setSyncWaiterSt, CStore.modifyWaitableCommon, CStore.subtask?,
      ArenaField.get?_modify_self, before, Option.map_some]
    rfl
  have resolved : cleared.subtaskResolved subtask = true := by
    simp [CStore.subtaskResolved, clearedLive, changed, returned, SubtaskState.resolved]
  let reply : EventTuple → Session grow sig (Ret (core3 grow)) := fun _ => do
    let current ← getObj ArenaField.subtasks subtask
    pure (.flat [i32Flat (subtaskCancelResult (some current.state))])
  let activations := ⟨resume.thread, .prog resume.resumeAfter, resume.segments⟩ :: resume.rest
  let entered := { resume.reached with
    store := cleared
    ctl := ⟨some cancel.thread, .prog (Waitable.getPendingEvent (.subtask subtask) >>= reply),
      .core cancel.core cancel.next :: cancel.segments⟩ :: activations }
  have enter : Steps profile ready (specDispatch ready impl) resume.reached (List.replicate 2 .tau) entered := by
    refine .cons (.modify rfl) (.cons (.get rfl) ?_)
    simp [Prog.bind, cleared, resolved, ParkedCancel.result, Builtins.subtaskCancelDeliver,
      Prog.bind_assoc, reply, entered, pure]
    exact .refl _
  have take := deliver_pending (prof := profile) (ready := ready) (dispatch := specDispatch ready impl)
    (config := entered) subtask changed index clearedLive returned indexed queued reply rfl
  obtain ⟨settled, settledLive, _, _, state, _⟩ := consumeClears cleared ⟨changed, clearedLive, returned, indexed, queued⟩
  have lookup : ArenaField.subtasks.get? (cancelDelivered cleared subtask) subtask = some settled := settledLive
  simp only [cancelDelivered] at lookup
  refine appendSteps (appendSteps enter take) (.cons (.get rfl) ?_)
  simp [entered, Prog.bind, lookup, pure, state]
  exact .cons (.popCore rfl) (.refl _)

theorem syncCancelLinkedTick {atReturn resolving atHost whileBlocked between}
    (cancel : ParkedCancel parked subtask) (wait : SyncCancelWait cancel atReturn)
    (runs : ParkedPrefix profile ready (specDispatch ready impl) cancel.thread wait.blocked whileBlocked resolving)
    (resolve : LinkedResolution resolving subtask index)
    (path : ParkedRetaining profile ready (specDispatch ready impl) cancel.thread subtask index resolve.committed between atHost)
    (tick : SelectedTick cancel.thread atHost ready profile) :
    Steps profile ready (specDispatch ready impl) atReturn
      (List.replicate 5 .tau ++ whileBlocked ++ List.replicate 17 .tau ++ between ++
        tick.selectionLabels ++ List.replicate 9 .tau)
      (SyncCancelResume.afterTick tick (selectedTickWaiting tick)).delivered := by
  obtain ⟨commitRun, queued⟩ := resolutionIndexedParked (profile := profile) (ready := ready) (impl := impl) resolve
  obtain ⟨replay, pending⟩ := retainingParked path queued
  obtain ⟨before, keptBefore⟩ := runs.reaches
  obtain ⟨commits, keptCommit⟩ := (commitRun cancel.thread).reaches
  obtain ⟨after, keptAfter⟩ := replay.reaches
  have saved : atHost.cont? cancel.thread = some cancel.saved :=
    keptAfter.trans (keptCommit.trans (keptBefore.trans (Config.cont?_setCont_self _ _ _)))
  let resume := SyncCancelResume.afterTick (cancel := cancel) tick (selectedTickWaiting tick)
  have deliver := appendSteps (profile := profile) (ready := ready) (impl := impl)
    (resumeSyncCancel cancel resume saved) (syncCancelDelivers cancel resume pending)
  simpa only [List.append_assoc, ← List.replicate_add] using
    appendSteps (appendSteps (appendSteps (appendSteps (appendSteps (syncCancelBlocks cancel wait) before) commits)
    after) (selectTick tick)) deliver

theorem startedCancelLinkedTick {resolving atHost whileBlocked between} (cancel : ParkedCancel parked subtask)
    (request : StartedCancel cancel) (synchronous : cancel.async_ = false)
    (runs : ParkedPrefix profile ready (specDispatch ready impl) cancel.thread
      (startedCancelWait cancel request synchronous).blocked whileBlocked resolving)
    (resolve : LinkedResolution resolving subtask index)
    (path : ParkedRetaining profile ready (specDispatch ready impl) cancel.thread subtask index resolve.committed between atHost)
    (tick : SelectedTick cancel.thread atHost ready profile) :
    Steps profile ready (specDispatch ready impl) parked
      (List.replicate 25 .tau ++ whileBlocked ++ List.replicate 17 .tau ++ between ++
        tick.selectionLabels ++ List.replicate 9 .tau)
      (SyncCancelResume.afterTick tick (selectedTickWaiting tick)).delivered := by
  have run := syncCancelLinkedTick (impl := impl) cancel (startedCancelWait cancel request synchronous) runs resolve path tick
  have full := appendSteps (cancelStartedReturns cancel request) run
  rw [show (25 : Nat) = 20 + 5 by rfl, List.replicate_add]
  simpa only [List.append_assoc] using full

theorem cancelReturned (cancel : ParkedCancel parked subtask) (pending : PendingAt parked.store subtask index)
    (available : CancelAvailable parked.store subtask) :
    Steps profile ready (specDispatch ready impl) parked (List.replicate 15 .tau) cancel.resumed := by
  obtain ⟨record, live, returned, indexed, queued⟩ := pending
  obtain ⟨other, atSlot, notDelivered, notRequested, notJoined⟩ := available
  rw [live] at atSlot
  cases atSlot
  obtain ⟨settled, cleared, _, _, state, _⟩ := consumeClears parked.store ⟨record, live, returned, indexed, queued⟩
  let reply : EventTuple → Session grow sig (Ret (core3 grow)) := fun _ => do
    let current ← getObj ArenaField.subtasks subtask
    pure (.flat [i32Flat (subtaskCancelResult (some current.state))])
  let entered := { parked with ctl := ⟨some cancel.thread, .prog (Waitable.getPendingEvent (.subtask subtask) >>= reply),
    .core cancel.core cancel.next :: cancel.segments⟩ :: cancel.rest }
  have enter : Steps profile ready (specDispatch ready impl) parked (List.replicate 11 .tau) entered := by
    simpa [entered, returned, SubtaskState.resolved, Builtins.subtaskCancelDeliver, reply,
      Prog.bind_assoc, pure] using
      cancelEntry (profile := profile) (ready := ready) (impl := impl) cancel record live
        notDelivered notRequested notJoined
  have take := deliver_pending (prof := profile) (ready := ready) (dispatch := specDispatch ready impl)
    (config := entered) subtask record index live returned indexed queued reply rfl
  refine appendSteps (appendSteps enter take) (.cons (.get rfl) ?_)
  have settledAt : ArenaField.subtasks.get? (cancelDelivered parked.store subtask) subtask = some settled := cleared
  simp only [cancelDelivered] at settledAt
  simp [entered, Prog.bind, settledAt, pure, state]
  exact .cons (.popCore rfl) (.refl _)

theorem cancelClears (cancel : ParkedCancel parked subtask) (pending : PendingAt parked.store subtask index) :
    ∃ record, cancel.resumed.store.subtask? subtask = some record ∧ record.common.pending = none ∧
      record.lenders = none ∧ record.state = .returned ∧ record.index = some index :=
  consumeClears parked.store pending

theorem resolutionCancel (resolve : LinkedResolution initial subtask index) {between}
    (path : Retaining profile ready (specDispatch ready impl) subtask index resolve.committed between parked)
    (cancel : ParkedCancel parked subtask) (available : CancelAvailable parked.store subtask) :
    Steps profile ready (specDispatch ready impl) initial ((List.replicate 17 .tau ++ between) ++ List.replicate 15 .tau)
      cancel.resumed := by
  obtain ⟨commitRun, queued⟩ := resolutionIndexed (profile := profile) (ready := ready) (impl := impl) resolve
  obtain ⟨replay, pending⟩ := retainingPath path queued
  exact appendSteps (appendSteps commitRun replay) (cancelReturned cancel pending available)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery
