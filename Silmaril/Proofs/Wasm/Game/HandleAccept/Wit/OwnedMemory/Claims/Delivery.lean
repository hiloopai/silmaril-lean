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

private theorem consumeClears (store : CStore (core3 grow)) (pending : PendingAt store subtask index) :
    ∃ record, (cancelDelivered store subtask).subtask? subtask = some record ∧ record.common.pending = none ∧
      record.lenders = none ∧ record.state = .returned ∧ record.index = some index := by
  obtain ⟨record, live, returned, indexed, _⟩ := pending
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
  refine ⟨{ event with lenders := none }, ?_, rfl, rfl, returned, indexed⟩
  change (cleared.deliverResolveSt subtask).subtask? subtask = _
  rw [CStore.deliverResolveSt, clearedAt]
  rw [CStore.subtask?, ArenaField.get?_modify_self]
  exact congrArg (Option.map fun entry => { entry with lenders := none }) ((frame _ _).trans clearedAt)

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

private theorem resumeWait {atResume : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
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

private theorem selectTick {atHost : Config (core3 grow) (HostState sig)} {thread : ThreadId}
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
  change (((Builtins.WaitableSt.requestCancel subtask cancel.thread parked.store).setTaskState request.taskId
    .pendingCancel).setSyncWaiterSt (.subtask subtask) none).subtaskResolved subtask = false at stillUnresolved
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

private theorem resumeSyncCancel {atResume} (cancel : ParkedCancel parked subtask)
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
