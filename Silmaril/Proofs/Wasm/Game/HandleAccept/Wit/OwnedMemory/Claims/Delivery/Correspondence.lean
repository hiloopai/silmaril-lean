module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
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

theorem neutralStep {action labels} (edge : Transition profile ready impl start action labels finish)
    (neutral : JournalNeutralAction action) (other : HostState sig) :
    Transition profile ready impl (HostFrame.replace start other) action labels (HostFrame.replace finish other) := by
  cases edge <;> try contradiction
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
