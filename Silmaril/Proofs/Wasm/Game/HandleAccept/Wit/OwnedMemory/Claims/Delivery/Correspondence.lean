module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.AsyncRef
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall.Delivery ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start finish : State grow sig}

private def pollOnHost {target : SubtaskId} (poll : ParkedPoll start target profile) (other : HostState sig) :
    ParkedPoll (HostFrame.replace start other) target profile :=
  { poll with toPollAdmission := { poll.toPollAdmission with focused := poll.focused } }

private def waitOnHost (wait : ParkedWait start) (other : HostState sig) : ParkedWait (HostFrame.replace start other) :=
  { wait with focused := wait.focused }

private def cancelOnHost {target : SubtaskId} (cancel : ParkedCancel start target) (other : HostState sig) :
    ParkedCancel (HostFrame.replace start other) target :=
  { cancel with focused := cancel.focused }

private def cancelResumeOnHost {initial atResume : State grow sig} {target : SubtaskId}
    {cancel : ParkedCancel initial target} (resume : SyncCancelResume cancel atResume) (other : HostState sig) :
    SyncCancelResume cancel (HostFrame.replace atResume other) :=
  { resume with focused := resume.focused }

private def liftOnHost (site : LiftSite grow sig) (other : HostState sig) : LiftSite grow sig :=
  { site with start := HostFrame.replace site.start other, focused := site.focused }

private def returnOnHost (site : StackfulReturn start) (other : HostState sig) : StackfulReturn (HostFrame.replace start other) :=
  { site with focused := site.focused, returned := site.returned }

private def exitOnHost {site : StackfulReturn start} (exit : StackfulExit site) (other : HostState sig) :
    StackfulExit (returnOnHost site other) :=
  { exit with taskLive := exit.taskLive, remove := exit.remove }

theorem neutralStep {action labels} (edge : Transition profile ready impl start action labels finish)
    (neutral : JournalNeutralAction action) (other : HostState sig) :
    Transition profile ready impl (HostFrame.replace start other) action labels (HostFrame.replace finish other) := by
  cases edge <;> try contradiction
  case invoke available fresh => exact .invoke available fresh
  case invokePrologue focused => exact .invokePrologue focused
  case liftedLookup focused lookup => exact .liftedLookup focused lookup
  case liftLaunch site => exact .liftLaunch (liftOnHost site other)
  case liftAdmit site admission =>
    exact .liftAdmit (liftOnHost site other) { admission with live := admission.live }
  case liftArguments site live => exact .liftArguments (liftOnHost site other) live
  case invokeReturn focused =>
    have replay := Transition.invokeReturn (profile := profile) (ready := ready) (impl := impl)
      (start := HostFrame.replace start other) focused
    cases call : start.pending.getLast?.map (·.1) <;>
      simpa [StepDefs.hostFinish, StepDefs.lastCall?, HostFrame.replace, call, Config.setCancel] using replay
  case stackfulComplete exit => exact .stackfulComplete (exitOnHost exit other)
  case stackfulUnresolved =>
    exact .stackfulUnresolved (returnOnHost (by assumption) other) (by assumption) (by assumption) (by assumption) (by assumption)
  case stackfulExit exit empty => exact .stackfulExit (exitOnHost exit other) empty
  case coreInternal focused running steps => exact .coreInternal focused running steps
  case coreReturned focused returned => exact .coreReturned focused returned
  case coreTrap focused trapped => exact .coreTrap focused trapped
  case coreReply focused => exact .coreReply focused
  case poll poll pending branch =>
    cases branch with
    | unaligned bad => exact .poll (pollOnHost poll other) pending (.unaligned bad)
    | outside aligned sized bad => exact .poll (pollOnHost poll other) pending (.outside aligned sized bad)
    | inside aligned sized fits => exact .poll (pollOnHost poll other) pending (.inside aligned sized fits)
  case waitBlock wait empty => exact .waitBlock (waitOnHost wait other) empty
  case waitReady early allowed wait available =>
    cases early
    · exact .waitReady (waitOnHost wait other) available false allowed
    · exact .waitReady (waitOnHost wait other) available true allowed
  case waitResume resume saved =>
    exact .waitResume (start := HostFrame.replace _ other) { resume with focused := resume.focused } saved
  case waitTake delivery focused pending branch =>
    cases branch with
    | unaligned bad =>
      exact .waitTake (start := HostFrame.replace _ other) { delivery with setLive := delivery.setLive } focused pending (.unaligned bad)
    | outside aligned sized bad =>
      exact .waitTake (start := HostFrame.replace _ other) { delivery with setLive := delivery.setLive } focused pending (.outside aligned sized bad)
    | inside aligned sized fits =>
      exact .waitTake (start := HostFrame.replace _ other) { delivery with setLive := delivery.setLive } focused pending (.inside aligned sized fits)
  case cancelReturned cancel pending available => exact .cancelReturned (cancelOnHost cancel other) pending available
  case cancelReply cancel record cancelled pending focused live =>
    exact .cancelReply cancel record focused live cancelled pending
  case cancelPark wait => exact .cancelPark (start := HostFrame.replace _ other) { wait with focused := wait.focused }
  case cancelResume resume saved => exact .cancelResume (cancelResumeOnHost resume other) saved
  case cancelTake resume pending => exact .cancelTake (cancelResumeOnHost resume other) pending

theorem neutralRun {actions labels} (path : Run profile ready impl start actions labels finish)
    (neutral : ∀ action ∈ actions, JournalNeutralAction action) (other : HostState sig) :
    Run profile ready impl (HostFrame.replace start other) actions labels (HostFrame.replace finish other) := by
  induction path with
  | stop _ => exact .stop _
  | next edge _ ih => exact .next (neutralStep edge (neutral _ (.head _)) other) (ih fun _ present => neutral _ (.tail _ present))

private theorem equalLists {Elem : Type} {relation : Elem → Elem → Prop} {left right : List Elem}
    (equal : ∀ {lhs rhs}, relation lhs rhs → lhs = rhs) (related : List.Forall₂ relation left right) : left = right := by
  induction related with
  | nil => rfl
  | cons head _ ih => rw [equal head, ih]

private theorem sameActive {left right : Activation (core3 grow) (HostState sig)}
    (related : ReturnFrame.Related.Active (fun _ _ => False) left right) : left = right := by
  cases related with
  | mk frames =>
    have same := equalLists (fun segment => by cases segment with
      | same => rfl
      | swap impossible => exact False.elim impossible) frames
    cases same
    rfl

private theorem sameSaved {left right : Option (Activation (core3 grow) (HostState sig))}
    (related : ReturnFrame.Related.Saved (fun _ _ => False) left right) : left = right := by
  cases related with
  | none => rfl
  | some active => exact congrArg some (sameActive active)

private theorem sameMachine {left right : State grow sig}
    (related : ReturnFrame.Related.Paired (fun _ _ => False) left right) : right = left := by
  cases related with
  | mk active blocked =>
    have activeEq := equalLists (fun related => sameActive related) active
    have savedEq := equalLists (fun related => sameSaved related) blocked
    cases left
    dsimp only at activeEq savedEq ⊢
    subst_vars
    rfl

theorem replyRejoin {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route} {value : route.output.Result}
    {reached reference left right : State grow sig}
    (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference left right) :
    right = HostFrame.replace left right.host :=
  sameMachine replies.2.2.2.2.2

theorem afterGive {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route} {value : route.output.Result}
    {reached reference left right : State grow sig} {actions labels}
    (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference left right)
    (tail : Run profile ready impl left actions labels finish) (neutral : ∀ action ∈ actions, JournalNeutralAction action) :
    Run profile ready impl right actions labels (HostFrame.replace finish right.host) := by
  exact replyRejoin replies ▸ neutralRun tail neutral right.host

private theorem appendSteps {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {start middle finish : State grow sig} {leading trailing : Trace grow sig}
    (first : Steps profile ready dispatch start leading middle) (tail : Steps profile ready dispatch middle trailing finish) :
    Steps profile ready dispatch start (leading ++ trailing) finish := by
  induction first with
  | refl => exact tail
  | cons step _ ih => exact .cons step (ih tail)

theorem giveThenDelivery {bindings : List (Binding sig)} {callees : List (ComponentCall.Callee sig)}
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (value : route.output.Result)
    {reached reference : State grow sig}
    (comparison : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference)
    (agreement : GiveBodyAgreement profile ready bindings callees site reached reference)
    (select : ∀ left right, LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference left right →
      ∃ actions labels last, Run profile ready (ComponentCall.hostWithComponent bindings callees) left actions labels last ∧
        ∀ action ∈ actions, JournalNeutralAction action) :
    ∃ actions checked canonical last,
      Run profile ready (ComponentCall.hostWithComponent bindings callees) site.checked (.give route .returned :: actions) checked last ∧
      Steps profile ready (Dispatch.linked ready bindings callees) (site.reference site.referenceReply) canonical
        (HostFrame.replace last reference.host) ∧ PayloadPrefix.visible checked = PayloadPrefix.visible canonical := by
  obtain ⟨checkLabels, canonLabels, left, right, checkRun, canonRun, seen, replies⟩ :=
    Transition.give_returned site value comparison agreement
  obtain ⟨actions, labels, last, tail, neutral⟩ := select left right replies
  have canonical := (afterGive replies tail neutral).steps
  rw [show right.host = reference.host from replies.2.2.2.2.1] at canonical
  refine ⟨_, _, _, last, .next checkRun tail, appendSteps canonRun canonical, ?_⟩
  unfold PayloadPrefix.visible at seen ⊢
  simp only [List.filter_append, List.filter_cons, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil, seen]

theorem replayJournal {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))} {labels}
    (path : Steps profile ready dispatch start labels finish) (incoming : HostState sig) :
    JournalReplay profile ready dispatch start incoming labels finish := by
  rcases HostFrame.steps incoming path with ⟨_, replayed⟩ | ⟨_, _, _, _, _, _, _, split, baseline, replayed, read, baselineRead, replayedRead, tail⟩
  · exact .complete replayed
  · exact .read split baseline replayed read baselineRead replayedRead tail

theorem completeJournal {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))} {incoming labels}
    (path : JournalReplay profile ready dispatch start incoming labels finish)
    (agrees : ReachedReadsAgree (profile := profile) (ready := ready) dispatch start incoming labels finish) :
    ∃ outgoing, Steps profile ready dispatch (HostFrame.replace start incoming) labels (HostFrame.replace finish outgoing) := by
  cases path with
  | complete run => exact ⟨_, run⟩
  | read split baseline replayed read baselineRead _ tail =>
    cases read with
    | mk focused different => exact False.elim (different (agrees split baseline replayed baselineRead tail focused))

theorem completeRejoin {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))} {incoming labels}
    {checked : State grow sig} (path : JournalReplay profile ready dispatch start incoming labels finish)
    (aligned : finish = HostFrame.replace checked finish.host)
    (agrees : ReachedReadsAgree (profile := profile) (ready := ready) dispatch start incoming labels finish) :
    ∃ reached, Steps profile ready dispatch (HostFrame.replace start incoming) labels reached ∧
      reached = HostFrame.replace checked reached.host := by
  obtain ⟨outgoing, run⟩ := completeJournal path agrees
  have rejoined := congrArg (HostFrame.replace · outgoing) aligned
  exact ⟨_, run, rejoined⟩

theorem readFreeAgreement {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))} {incoming labels}
    (closed : ReadFreeThrough (profile := profile) (ready := ready) dispatch start labels finish) :
    ReachedReadsAgree (profile := profile) (ready := ready) dispatch start incoming labels finish := by
  intro leading label trailing reached reachedHost next split baseline replayed head tail thread read frames rest focused
  exact False.elim (closed split baseline (.cons head tail) focused)

private theorem entrySilent {route : GiveEffectRoute} {labels}
    (entry : Transition profile ready impl start (.give route .entered) labels finish) :
    PayloadPrefix.visible labels = [] := by
  cases entry with
  | giveEntry _ _ silent _ _ _ => exact silent
  | giveStopped _ _ _ _ _ _ stopped => cases stopped

theorem nextReturnedGive {bindings : List (Binding sig)} {callees : List (ComponentCall.Callee sig)}
    {route : GiveEffectRoute} {left right : State grow sig}
    (aligned : right = HostFrame.replace left right.host)
    (site : PayloadRoot.Site grow sig route) {actions labels entryLabels}
    (between : Run profile ready (ComponentCall.hostWithComponent bindings callees) left actions labels site.start)
    (neutral : ∀ action ∈ actions, JournalNeutralAction action)
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees) site.start (.give route .entered)
      entryLabels site.checked)
    (value : route.output.Result) {reached reference : State grow sig}
    (comparison : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference)
    (agreement : GiveBodyAgreement profile ready bindings callees site reached reference) :
    let parked := HostFrame.replace site.start right.host
    let dispatch := Dispatch.linked ready bindings callees
    ∃ checkedLabels canonicalLabels checked baseline,
      Run profile ready (ComponentCall.hostWithComponent bindings callees) left
        (actions ++ [.give route .entered, .give route .returned]) checkedLabels checked ∧
      Steps profile ready dispatch right labels parked ∧
      Steps profile ready dispatch (site.reference site.referenceReply) canonicalLabels baseline ∧
      PayloadPrefix.visible checkedLabels = PayloadPrefix.visible (labels ++ canonicalLabels) ∧
      baseline = HostFrame.replace checked baseline.host ∧
      JournalReplay profile ready dispatch (site.reference site.referenceReply) parked.host canonicalLabels baseline := by
  obtain ⟨checkLabels, canonLabels, checked, baseline, returned, canonRun, seen, replies⟩ :=
    Transition.give_returned site value comparison agreement
  have noEntry := entrySilent entry
  have prior : Steps profile ready (Dispatch.linked ready bindings callees) right labels (HostFrame.replace site.start right.host) :=
    aligned ▸ (neutralRun between neutral right.host).steps
  have joined := replyRejoin replies
  have checkedRun := between.append (.next entry (.next returned (.stop _)))
  refine ⟨_, _, _, _, checkedRun, prior, canonRun, ?_, joined, replayJournal canonRun _⟩
  simp only [PayloadPrefix.visible, List.filter_append] at noEntry seen ⊢
  simp [noEntry, seen]

theorem commitOnJournal {target index} (resolve : LinkedResolution start target index) (other : HostState sig)
    {writer : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.State sig}
    (registered : other.writer.register resolve.tree = .ok writer)
    (sameHandle : writer.accepted.length = resolve.writer.accepted.length) :
    ∃ reached, Transition profile ready impl (HostFrame.replace start other) (.commit target index) (List.replicate 17 .tau) reached ∧
      reached = HostFrame.replace resolve.committed reached.host ∧ PendingAt reached.store target index ∧
      reached.host = (({ other with writer } : HostState sig).record (.published resolve.ticket writer.accepted.length)).record
        (.returned resolve.ticket writer.accepted.length) := by
  let replay : LinkedResolution (HostFrame.replace start other) target index :=
    { resolve with writer, registered, room := sameHandle ▸ resolve.room }
  refine ⟨replay.committed, .commit replay, ?_, (replay.indexed_steps (profile := profile) (ready := ready) (impl := impl)).2, rfl⟩
  simp only [LinkedResolution.committed, replay, sameHandle, HostFrame.replace]

theorem commitPaired {target index} (resolve : LinkedResolution start target index) {other : State grow sig}
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} (paired : HostFrame.Related.Paired older start other)
    {writer : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.State sig}
    (registered : other.host.writer.register resolve.tree = .ok writer)
    (sameHandle : writer.accepted.length = resolve.writer.accepted.length) :
    ∃ reached, Transition profile ready impl other (.commit target index) (List.replicate 17 .tau) reached ∧
      HostFrame.Related.Paired older resolve.committed reached ∧ PendingAt reached.store target index ∧
      reached.host = (({ other.host with writer } : HostState sig).record (.published resolve.ticket writer.accepted.length)).record
        (.returned resolve.ticket writer.accepted.length) := by
  let reachedHost := (({ other.host with writer } : HostState sig).record (.published resolve.ticket writer.accepted.length)).record
    (.returned resolve.ticket writer.accepted.length)
  obtain ⟨segments, rest, focused, framed⟩ :=
    paired.retarget resolve.focused (.prog (.pure (.cancel .none))) resolve.committed.host reachedHost
  have store := paired.data.1
  let replay : LinkedResolution other target index :=
    { resolve with
      writer, registered, segments, rest, focused
      room := by rw [sameHandle]; exact resolve.room
      callerRecord := by rw [← store]; exact resolve.callerRecord
      live := by rw [← store]; exact resolve.live
      sized := by rw [← store]; exact resolve.sized }
  have stillPaired : HostFrame.Related.Paired older resolve.committed replay.committed := by
    have updated := framed.set_store resolve.committed.store
    simp only [LinkedResolution.committed, replay, reachedHost] at updated ⊢
    simpa only [← store, sameHandle] using updated
  exact ⟨replay.committed, .commit replay, stillPaired,
    (replay.indexed_steps (profile := profile) (ready := ready) (impl := impl)).2, rfl⟩

theorem pollPaired {target index result suffix} (poll : ParkedPoll start target profile)
    (pending : PendingAt start.store target index)
    (branch : BufferBranch start.store poll.memory (flatNat poll.out) result suffix)
    {other : State grow sig} {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) :
    ∃ reached, Transition profile ready impl other (.poll target index result) (pollLabels poll ++ suffix) reached ∧
      HostFrame.Related.Paired older
        (result.finish (pollReply poll index) { start with store := StepDefs.lockdownSt poll.delivered, ctl := [] }) reached ∧
      reached.host = other.host := by
  let written := (pollReply poll index).store
  let resumed := (core3 grow).resume written.core poll.core (.values [i32Flat EventCode.subtask.toNat])
  obtain ⟨segments, rest, focused, framed⟩ :=
    paired.retarget poll.focused (.core resumed poll.next) start.host other.host
  have store := paired.data.1
  let replay : ParkedPoll other target profile :=
    { poll with
      toPollAdmission :=
        { poll.toPollAdmission with
          segments, rest, focused
          callout := by rw [← store]; exact poll.callout
          liveThread := by rw [← store]; exact poll.liveThread
          liveTask := by rw [← store]; exact poll.liveTask
          liveInst := by rw [← store]; exact poll.liveInst }
      setLive := by
        change other.store.wset? poll.ws = some poll.set
        exact store ▸ poll.setLive
      selects := by
        change (applyPerm poll.perm poll.set.elems).find?
          (other.store.wsetSetElemsSt poll.ws (applyPerm poll.perm poll.set.elems)).waitableHasEvent = some (.subtask target)
        exact store ▸ poll.selects }
  have delivered : replay.delivered = poll.delivered := by
    simp only [ParkedPoll.delivered, replay, ← store]
  have replayBranch : BufferBranch other.store replay.memory (flatNat replay.out) result suffix := by
    rw [← store]
    exact branch
  refine ⟨_, .poll replay (store ▸ pending) replayBranch, ?_, ?_⟩
  · cases result with
    | replied =>
      simpa only [BufferResult.finish, pollReply, replay, delivered, resumed, written] using framed.set_store written
    | trapped _ =>
      simpa only [BufferResult.finish, delivered] using paired.clear_control.set_store (StepDefs.lockdownSt poll.delivered)
  · cases result <;> rfl

private def waitAtFrames {initial : State grow sig} (wait : ParkedWait initial)
    (segments : List (Seg (core3 grow) (HostState sig))) :
    ParkedWait { initial with ctl := ⟨some wait.thread, .core wait.core wait.next, segments⟩ :: wait.rest } :=
  { wait with segments, focused := rfl }

private def replayWait (wait : ParkedWait start) {other : State grow sig}
    (store : start.store = other.store) {segments rest}
    (focused : other.ctl = ⟨some wait.thread, .core wait.core wait.next, segments⟩ :: rest) : ParkedWait other :=
  { wait with
    segments, rest, focused
    callout := by rw [← store]; exact wait.callout
    liveThread := by rw [← store]; exact wait.liveThread
    liveTask := by rw [← store]; exact wait.liveTask
    liveInst := by rw [← store]; exact wait.liveInst }

private theorem waitParkPaired (wait : ParkedWait start) {other : State grow sig}
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} (paired : HostFrame.Related.Paired older start other) :
    ∃ replay : ParkedWait other, replay.ws = wait.ws ∧ replay.thread = wait.thread ∧
      HostFrame.Related.Paired older wait.blocked replay.blocked := by
  have aligned : ReturnFrame.Related.Paired older (HostFrame.replace start other.host) other := paired
  obtain ⟨_, _, focused, framed⟩ := aligned.park_core wait.focused wait.saved.focus
  let replay := replayWait wait paired.data.1 focused
  refine ⟨replay, rfl, rfl, ?_⟩
  have result := framed.set_store wait.blocked.store
  simpa only [ParkedWait.blocked, ParkedWait.saved, ParkedWait.takeEvent, HostFrame.Related.Paired, HostFrame.replace,
    replay, replayWait, Config.setCont, ← paired.data.1] using result

theorem waitBlockPaired (wait : ParkedWait start) (empty : start.store.wsetHasEvent wait.ws = false)
    {other : State grow sig} {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) :
    ∃ reached, Transition profile ready impl other (.waitEnter wait.thread false) (List.replicate 13 .tau) reached ∧
      HostFrame.Related.Paired older wait.blocked reached := by
  obtain ⟨replay, waitable, caller, paired'⟩ := waitParkPaired wait paired
  have empty' : other.store.wsetHasEvent replay.ws = false := by rw [waitable, ← paired.data.1]; exact empty
  exact ⟨replay.blocked, caller ▸ Transition.waitBlock replay empty', paired'⟩

theorem waitReadyPaired (wait : ParkedWait start) (available : start.store.wsetHasEvent wait.ws = true)
    (early : Bool) (allowed : Allowed profile (.earlyReturn .waitableSetWait) early)
    {other : State grow sig} {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) :
    ∃ reached, Transition profile ready impl other (.waitEnter wait.thread early) (ParkedWait.readyLabels early) reached ∧
      HostFrame.Related.Paired older (if early then wait.early else wait.blocked) reached := by
  cases early with
  | false =>
    obtain ⟨replay, waitable, caller, paired'⟩ := waitParkPaired wait paired
    have available' : other.store.wsetHasEvent replay.ws = true := by rw [waitable, ← paired.data.1]; exact available
    exact ⟨replay.blocked, caller ▸ Transition.waitReady replay available' false allowed, paired'⟩
  | true =>
    have aligned : ReturnFrame.Related.Paired older (HostFrame.replace start other.host) other := paired
    obtain ⟨_, _, focused, framed⟩ := aligned.push_shared wait.focused (.prog wait.takeEvent) (.core wait.core wait.next)
    let replay := replayWait wait paired.data.1 focused
    refine ⟨replay.early, .waitReady replay (paired.data.1 ▸ available) true allowed, ?_⟩
    change HostFrame.Related.Paired older wait.early replay.early
    have result := framed.set_store wait.early.store
    simpa only [ParkedWait.early, ParkedWait.takeEvent, HostFrame.Related.Paired, HostFrame.replace,
      replay, replayWait, ← paired.data.1] using result

theorem waitResumePaired {initial : State grow sig} {wait : ParkedWait initial} (resume : WaitResume wait start)
    (saved : start.cont? wait.thread = some wait.saved)
    {other : State grow sig} {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) :
    ∃ reached, Transition profile ready impl other (.waitResume wait.thread) (List.replicate 4 .tau) reached ∧
      HostFrame.Related.Paired older resume.reached reached := by
  have aligned : ReturnFrame.Related.Paired older (HostFrame.replace start other.host) other := paired
  obtain ⟨segments, rest, savedFrames, focused, otherSaved, framed⟩ :=
    aligned.resume_core resume.focused (show start.cont? wait.thread = some ⟨some wait.thread,
       wait.saved.focus, .core wait.core wait.next :: wait.segments⟩ from saved) (.prog resume.resumeAfter) (.prog wait.takeEvent)
  let replay : WaitResume (waitAtFrames wait savedFrames) other :=
    { resume with segments, rest, focused, waiting := paired.data.1 ▸ resume.waiting }
  refine ⟨replay.reached, .waitResume replay otherSaved, ?_⟩
  have result := framed.set_store resume.reached.store
  simpa only [WaitResume.reached, ParkedWait.takeEvent, HostFrame.Related.Paired, HostFrame.replace, replay, waitAtFrames,
    Config.setCont, ← paired.data.1] using result

theorem waitTakePaired {initial : State grow sig} {wait : ParkedWait initial} {target index result suffix}
    (delivery : WaitDelivery wait start profile target)
    (focused : start.ctl = ⟨some wait.thread, .prog wait.takeEvent, .core wait.core wait.next :: wait.segments⟩ :: start.ctl.drop 1)
    (pending : PendingAt start.store target index)
    (branch : BufferBranch delivery.delivered wait.memory (flatNat wait.out) result suffix)
    {other : State grow sig} {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) :
    ∃ reached, Transition profile ready impl other (.wait target index result) (delivery.labels ++ suffix) reached ∧
      HostFrame.Related.Paired older
        (result.finish (delivery.resumed index) { start with store := StepDefs.lockdownSt delivery.delivered, ctl := [] }) reached ∧
      reached.host = other.host := by
  let written := (delivery.resumed index).store
  let resumed := (core3 grow).resume written.core wait.core (.values [i32Flat EventCode.subtask.toNat])
  obtain ⟨frames, rest, atOther, framed⟩ :=
    paired.retarget_core_frame focused (.core resumed wait.next) start.host other.host
  have store := paired.data.1
  let replay : WaitDelivery (waitAtFrames wait frames) other profile target :=
    { delivery with
      setLive := store ▸ delivery.setLive
      selects := store ▸ delivery.selects }
  have replayFocus : other.ctl = ⟨some wait.thread, .prog (waitAtFrames wait frames).takeEvent,
      .core wait.core wait.next :: frames⟩ :: other.ctl.drop 1 := by
    rw [atOther]
    rfl
  have delivered : replay.delivered = delivery.delivered := by
    simp only [WaitDelivery.delivered, replay, waitAtFrames, ← store]
  have replayBranch : BufferBranch replay.delivered wait.memory (flatNat wait.out) result suffix := by
    rw [delivered]
    exact branch
  refine ⟨_, .waitTake replay replayFocus (store ▸ pending) replayBranch, ?_, ?_⟩
  · cases result with
    | replied =>
      have control : other.ctl.drop 1 = rest := by rw [atOther]; rfl
      simp only [BufferResult.finish, WaitDelivery.resumed, waitAtFrames, control]
      erw [delivered]
      exact framed.set_store written
    | trapped _ =>
      simpa only [BufferResult.finish, delivered] using paired.clear_control.set_store (StepDefs.lockdownSt delivery.delivered)
  · cases result <;> rfl

theorem cancelReturnedPaired {target index} (cancel : ParkedCancel start target)
    (pending : PendingAt start.store target index) (available : CancelAvailable start.store target)
    {other : State grow sig} {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) :
    ∃ reached, Transition profile ready impl other (.cancel target .returned) (List.replicate 15 .tau) reached ∧
      HostFrame.Related.Paired older cancel.resumed reached ∧ reached.host = other.host := by
  let delivered := cancelDelivered start.store target
  let resumed := (core3 grow).resume delivered.core cancel.core (.values [i32Flat (subtaskCancelResult (some .returned))])
  obtain ⟨segments, rest, focused, framed⟩ :=
    paired.retarget cancel.focused (.core resumed cancel.next) start.host other.host
  have store := paired.data.1
  let replay : ParkedCancel other target :=
    { cancel with
      segments, rest, focused
      callout := by rw [← store]; exact cancel.callout
      liveThread := by rw [← store]; exact cancel.liveThread
      liveTask := by rw [← store]; exact cancel.liveTask
      liveInst := by rw [← store]; exact cancel.liveInst }
  refine ⟨_, .cancelReturned replay (store ▸ pending) (store ▸ available), ?_, rfl⟩
  simpa only [ParkedCancel.resumed, replay, resumed, delivered, ← store] using framed.set_store delivered

private theorem tickCandidates (other : HostState sig) (agrees : TickReadsAgree ready start other) :
    (StepDefs.enterHostSt start.store).candidates (ready start.host) =
      (StepDefs.enterHostSt start.store).candidates (ready other) := by
  unfold CStore.candidates
  apply List.filter_congr
  intro thread member
  simp only [CStore.threadReady, CStore.threadIs]
  split
  · rename_i entry found
    unfold Thread.ready
    cases blocked : entry.blocked
    · rfl
    cases condition : entry.readyCond with
    | none => rfl
    | some predicate =>
      cases predicate <;> try rfl
      rename_i query
      simp only [ReadyCond.eval, agrees thread member entry found blocked query condition]
  · rfl

theorem tickOnJournal {thread} (tick : SelectedTick thread start ready profile) (other : HostState sig)
    (agrees : TickReadsAgree ready start other) :
    Transition profile ready impl (HostFrame.replace start other) (.tick thread) tick.selectionLabels
      (HostFrame.replace tick.atResume other) := by
  let replay : SelectedTick thread (HostFrame.replace start other) ready profile :=
    { tick with hostReady := tick.hostReady, candidates := (tickCandidates other agrees).symm.trans tick.candidates }
  exact .tick replay

theorem interleavingRuns {actions labels incoming outgoing}
    (path : JournalInterleaving profile ready impl start incoming actions labels finish outgoing) :
    Run profile ready impl start actions labels finish ∧
      Run profile ready impl (HostFrame.replace start incoming) actions labels (HostFrame.replace finish outgoing) := by
  induction path with
  | stop => exact ⟨.stop _, .stop _⟩
  | neutral edge closed _ ih => exact ⟨.next edge ih.1, .next (neutralStep edge closed _) ih.2⟩
  | tick tick agrees _ ih => exact ⟨.next (.tick tick) ih.1, .next (tickOnJournal tick _ agrees) ih.2⟩
  | commit resolve registered sameHandle _ ih =>
    obtain ⟨reached, edge, aligned, _, host⟩ := commitOnJournal resolve _ registered sameHandle
    have endpoint := aligned.trans (congrArg (HostFrame.replace resolve.committed) host)
    exact ⟨.next (.commit resolve) ih.1, .next (endpoint ▸ edge) ih.2⟩

theorem interleavedCut {bindings : List (Binding sig)} {callees : List (ComponentCall.Callee sig)}
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {actions labels incoming outgoing entryLabels phase checkLabels canonLabels reached reference}
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start incoming actions labels site.start outgoing)
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees) site.start (.give route .entered)
      entryLabels site.checked)
    (checked : Transition profile ready (ComponentCall.hostWithComponent bindings callees) site.checked (.give route phase)
      checkLabels reached)
    (canonical : Steps profile ready (Dispatch.linked ready bindings callees) (site.reference site.referenceReply) canonLabels reference)
    (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels) :
    let dispatch := Dispatch.linked ready bindings callees
    ∃ checkedLabels,
      Run profile ready (ComponentCall.hostWithComponent bindings callees) start
        (actions ++ [.give route .entered, .give route phase]) checkedLabels reached ∧
      Steps profile ready dispatch (HostFrame.replace start incoming) labels (HostFrame.replace site.start outgoing) ∧
      PayloadPrefix.visible checkedLabels = PayloadPrefix.visible (labels ++ canonLabels) ∧
      JournalReplay profile ready dispatch (site.reference site.referenceReply) outgoing canonLabels reference := by
  obtain ⟨checkedPath, canonicalPath⟩ := interleavingRuns between
  have noEntry := entrySilent entry
  refine ⟨_, checkedPath.append (.next entry (.next checked (.stop _))), canonicalPath.steps, ?_, replayJournal canonical outgoing⟩
  simp only [PayloadPrefix.visible, List.filter_append] at noEntry seen ⊢
  simp [noEntry, seen]

theorem interleavingAppend {middle : State grow sig} {incoming middleHost outgoing first rest leading trailing}
    (firstPath : JournalInterleaving profile ready impl start incoming first leading middle middleHost)
    (restPath : JournalInterleaving profile ready impl middle middleHost rest trailing finish outgoing) :
    JournalInterleaving profile ready impl start incoming (first ++ rest) (leading ++ trailing) finish outgoing := by
  induction firstPath with
  | stop => exact restPath
  | neutral edge closed _ ih =>
    simpa only [List.cons_append, List.append_assoc] using JournalInterleaving.neutral edge closed (ih restPath)
  | commit resolve registered sameHandle _ ih =>
    simpa only [List.cons_append, List.append_assoc] using JournalInterleaving.commit resolve registered sameHandle (ih restPath)
  | tick tick agrees _ ih =>
    simpa only [List.cons_append, List.append_assoc] using JournalInterleaving.tick tick agrees (ih restPath)

theorem ofNeutralRun {actions labels} (run : Run profile ready impl start actions labels finish)
    (closed : ∀ action ∈ actions, JournalNeutralAction action) (other : HostState sig) :
    JournalInterleaving profile ready impl start other actions labels finish other := by
  induction run with
  | stop state => exact .stop state other
  | next edge _ ih => exact .neutral edge (closed _ (.head _)) (ih fun _ member => closed _ (.tail _ member))

theorem stackfulCompletion {reached : State grow sig} {site : StackfulReturn reached} {incoming outgoing actions labels}
    (run : JournalInterleaving profile ready impl start incoming actions labels reached outgoing)
    (exit : StackfulExit site) (empty : site.segments = []) :
    JournalInterleaving profile ready impl start incoming (actions ++ [.stackfulComplete site.taskId, .workerExit site.thread])
      (labels ++ (exit.labels ++ [.tau])) exit.finished outgoing := by
  have tail : JournalInterleaving profile ready impl reached outgoing [.stackfulComplete site.taskId, .workerExit site.thread]
      (exit.labels ++ [.tau]) exit.finished outgoing :=
    .neutral (.stackfulComplete exit) trivial (.neutral (.stackfulExit exit empty) trivial (.stop _ _))
  exact interleavingAppend run tail

theorem interleavedGive {bindings : List (Binding sig)} {callees : List (ComponentCall.Callee sig)}
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) {actions labels incoming outgoing entryLabels}
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start incoming actions labels site.start outgoing)
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees) site.start (.give route .entered)
      entryLabels site.checked)
    (value : route.output.Result) {reached reference : State grow sig}
    (comparison : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference)
    (agreement : GiveBodyAgreement profile ready bindings callees site reached reference) :
    let dispatch := Dispatch.linked ready bindings callees
    ∃ checkedLabels canonicalLabels checked baseline,
      Run profile ready (ComponentCall.hostWithComponent bindings callees) start
        (actions ++ [.give route .entered, .give route .returned]) checkedLabels checked ∧
      Steps profile ready dispatch (HostFrame.replace start incoming) labels (HostFrame.replace site.start outgoing) ∧
      Steps profile ready dispatch (site.reference site.referenceReply) canonicalLabels baseline ∧
      PayloadPrefix.visible checkedLabels = PayloadPrefix.visible (labels ++ canonicalLabels) ∧
      baseline = HostFrame.replace checked baseline.host ∧
      JournalReplay profile ready dispatch (site.reference site.referenceReply) outgoing canonicalLabels baseline := by
  obtain ⟨checkLabels, canonLabels, checked, baseline, returned, canonRun, seen, replies⟩ :=
    Transition.give_returned site value comparison agreement
  have seenReply : PayloadPrefix.visible (checkLabels ++ [.tau, .tau, .tau]) =
      PayloadPrefix.visible (canonLabels ++ [.tau]) := by simpa [PayloadPrefix.visible] using seen
  obtain ⟨labels, checkedPath, canonicalPath, visible, replay⟩ := interleavedCut site between entry returned canonRun seenReply
  exact ⟨labels, _, checked, baseline, checkedPath, canonicalPath, canonRun, visible, replyRejoin replies, replay⟩

theorem interleavedStop {bindings : List (Binding sig)} {callees : List (ComponentCall.Callee sig)}
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {actions labels incoming outgoing entryLabels phase checkLabels canonLabels reached reference}
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start incoming actions labels site.start outgoing)
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees) site.start (.give route .entered)
      entryLabels site.checked)
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (stop : GiveStop site check phase canonLabels reached reference) (sameStore : reached.store = reference.store)
    (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
    (checked : Steps profile ready (Dispatch.coreOnly ready bindings) site.checked checkLabels reached)
    (canonical : Steps profile ready (Dispatch.coreOnly ready bindings) (site.reference site.referenceReply) canonLabels reference)
    (agreement : GiveCutDispatch profile ready bindings callees site) :
    let dispatch := Dispatch.linked ready bindings callees
    ∃ checkedLabels,
      Run profile ready (ComponentCall.hostWithComponent bindings callees) start
        (actions ++ [.give route .entered, .give route phase]) checkedLabels reached ∧
      Steps profile ready dispatch (HostFrame.replace start incoming) labels (HostFrame.replace site.start outgoing) ∧
      Steps profile ready dispatch (site.reference site.referenceReply) canonLabels reference ∧
      PayloadPrefix.visible checkedLabels = PayloadPrefix.visible (labels ++ canonLabels) ∧
      JournalReplay profile ready dispatch (site.reference site.referenceReply) outgoing canonLabels reference := by
  obtain ⟨checkPath, canonPath⟩ := agreement stop sameStore seen checked canonical
  obtain ⟨labels, checkRun, canonRun, visible, replay⟩ := interleavedCut site between entry
    (.giveStopped site rfl checkPath canonPath seen sameStore stop) canonPath.steps seen
  exact ⟨labels, checkRun, canonRun, canonPath.steps, visible, replay⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence
