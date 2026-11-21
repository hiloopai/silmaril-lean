module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Callback.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.CollectionVisit.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Wasm.Component.Reference.Runtime.Task.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall (Callee hostWithComponent)
open ComponentCall.Delivery ComponentCall.Delivery.FiniteSession
open PayloadPrefix (Cursor)
open Stored.Endpoints.RecordLower

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start middle finish : State grow sig}

theorem collectionAllocatorPrefix {bindings : List (Binding sig)}
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {destination : RecordDestination} {inst : InstId} {type element : Stored.TypeOf}
    {entries : List Stored.Endpoints.RecordLower.Field} {index : Nat} {output : Stored.Lower.Output}
    {left right last : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {checkNext canonNext returned seen protectedReturn}
    (replay : LinkedCallback.CollectionReplayFor profile ready bindings older destination inst type element
      entries index output left right check canon checkNext canonNext returned) :
    let area := ABI.layout destination.width element
    let mode := Stored.Endpoints.RecordLower.CanonicalTree.EntryMode.forOutput destination.width type output
    let first := PayloadPrefix.checkedCollectionResume destination inst entries area index output checkNext
    let second := PayloadPrefix.canonicalCollectionResume destination inst entries area output canonNext mode
    let entered := PayloadPrefix.collectionEntry destination inst area entries.length (Dispatch.coreOnly ready bindings) left check first
    let reference := PayloadPrefix.collectionEntry destination inst area entries.length (Dispatch.coreOnly ready bindings) right canon second
    let changes := ReturnFrame.Extend older first second
    LinkedCallback.PrefixFor profile ready bindings protectedReturn entered seen last →
    (∀ first second, changes first second → protectedReturn first) →
    ∃ other mark checkLabels canonLabels,
      Steps profile ready (Dispatch.coreOnly ready bindings) entered checkLabels last ∧
      Steps profile ready (Dispatch.coreOnly ready bindings) reference canonLabels other ∧
      AllocatorCut profile ready bindings older changes entered reference last other checkLabels canonLabels mark := by
  dsimp only
  intro path covers
  obtain ⟨checkLabels, canonLabels, other, mark, checked, canonical, seenCheck, seenCanon, paired, outside, checkTrack, canonTrack, _⟩ :=
    replay.2.2 path covers
  exact ⟨other, mark, checkLabels, canonLabels, checked.steps, canonical.steps,
    ⟨checkTrack, canonTrack, paired, outside, seenCheck.trans seenCanon.symm⟩⟩

theorem collectionInstallLinked {bindings : List (Binding sig)} {callees : List (Callee sig)}
    {destination : RecordDestination} {inst : InstId} {type element : Stored.TypeOf}
    {entries : List Field} {index : Nat} {output : Stored.Lower.Output}
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {checkNext canonNext}
    (width : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (prepared : Stored.OwnedMemory.Claims.Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = check.control (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let area := ABI.layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width type output
    let first := PayloadPrefix.checkedCollectionResume destination inst entries area index output checkNext
    let second := PayloadPrefix.canonicalCollectionResume destination inst entries area output canonNext mode
    let entered := PayloadPrefix.collectionEntry destination inst area entries.length (Dispatch.coreOnly ready bindings) left check first
    let reference := PayloadPrefix.collectionEntry destination inst area entries.length (Dispatch.coreOnly ready bindings) right canon second
    Steps profile ready (Dispatch.linked ready bindings callees) left [.tau, .tau, .tau] entered ∧
      Steps profile ready (Dispatch.linked ready bindings callees) right [.tau, .tau] reference := by
  obtain ⟨checked, canonical⟩ := PayloadPrefix.collection_install_tracks
    (profile := profile) (ready := ready) (dispatch := Dispatch.linked ready bindings callees)
    destination inst type element entries output index left right check canon checkNext canonNext width prepared checkAt canonAt 0
  exact ⟨(ReturnFrame.Occurrence.prefix_survives checked).1, (ReturnFrame.Occurrence.prefix_survives canonical).1⟩

theorem allocatorSaved {bindings : List (Binding sig)} {older changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right reached reference : State grow sig} {checkLabels canonLabels slot depth}
    (cut : AllocatorCut profile ready bindings older changes left right reached reference checkLabels canonLabels (some (.saved slot depth))) :
    ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage reached) (.saved slot depth) =
      ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage left) (.active 0 0) ∧
    ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage reference) (.saved slot depth) =
      ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage right) (.active 0 0) := by
  obtain ⟨_, checkedAt, checked⟩ := cut.checked.survives
  obtain ⟨_, canonicalAt, canonical⟩ := cut.canonical.survives
  exact ⟨(ReturnFrame.Occurrence.prefix_survives checked).2.trans (congrArg _ (Option.some.inj checkedAt).symm),
    (ReturnFrame.Occurrence.prefix_survives canonical).2.trans (congrArg _ (Option.some.inj canonicalAt).symm)⟩

private theorem appendSteps {leading trailing}
    (left : Steps profile ready (specDispatch ready impl) start leading middle)
    (right : Steps profile ready (specDispatch ready impl) middle trailing finish) :
    Steps profile ready (specDispatch ready impl) start (leading ++ trailing) finish := by
  induction left with
  | refl => exact right
  | cons step _ ih => exact .cons step (ih right)

theorem liftLaunchSteps (site : LiftSite grow sig) :
    Steps profile ready (specDispatch ready impl) site.start [.tau, .tau, .tau, .tau, .tau] site.launched := by
  let taskData := liftTaskData site.fnType site.opts site.inst site.caller
  let task := site.storeAndTask.2
  let thread := site.storeAndThread.2
  let body := ThreadBody.liftImplicit task site.core
  let finish := fun _ : Unit => liftAfterThread (grow := grow) (sig := sig) task site.fnType.async_
  let install := fun target => Thread.resume target >>= finish
  let installProg : Session grow sig (Ret (core3 grow)) := .op (.newThread body) install
  let update := ArenaOps.allocSt ArenaField.tasks taskData
  let taskAt := fun (store : CStore (core3 grow)) => (ArenaField.tasks.alloc store taskData).2
  let readProg : CStore (core3 grow) → Session grow sig (Ret (core3 grow)) := fun store => .op (.modify update) fun _ =>
    .op (.newThread (.liftImplicit (taskAt store) site.core)) fun (target : ThreadId) =>
      Thread.resume target >>= fun _ => liftAfterThread (grow := grow) (sig := sig) (taskAt store) site.fnType.async_
  have readAt : site.start.ctl = ⟨site.parent, .prog (.op .get readProg), site.frames⟩ :: site.rest := site.focused
  let read := { site.start with ctl := ⟨site.parent, .prog (readProg site.start.store), site.frames⟩ :: site.rest }
  let allocated := { read with
    store := site.storeAndTask.1
    ctl := ⟨site.parent, .prog installProg, site.frames⟩ :: site.rest }
  let saved := { (allocated.setCont thread (some site.activation)) with
    store := site.storeAndThread.1
    ctl := ⟨site.parent, .prog (install thread), site.frames⟩ :: site.rest }
  have savedRun : Step profile ready (specDispatch ready impl) allocated .tau saved :=
    .newThread (m := allocated) (b := body) (k := install) (t := thread) rfl rfl
  have notWaiting : saved.store.threadIs Thread.waiting thread = false := by
    change site.storeAndThread.1.threadIs Thread.waiting site.storeAndThread.2 = false
    rw [CStore.threadIs, CStore.thread?, LiftSite.storeAndThread, ArenaField.get?_alloc_self]
    rfl
  let afterRead := fun store : CStore (core3 grow) =>
    ((if store.threadIs Thread.waiting thread then Thread.stopWaiting thread else pure ()) >>= fun _ => resumeThread thread) >>= finish
  let activating := { saved with ctl := ⟨site.parent, .prog (afterRead saved.store), site.frames⟩ :: site.rest }
  have readRun : Step profile ready (specDispatch ready impl) saved .tau activating := .get rfl
  have resumeAt : activating.ctl = ⟨site.parent, .prog (.op (.resumeThread thread) finish), site.frames⟩ :: site.rest := by
    simp only [activating, afterRead, notWaiting, Bool.false_eq_true, ite_false]
    rfl
  have savedAt : activating.cont? thread = some site.activation := Config.cont?_setCont_self ..
  exact .cons (.get readAt) (.cons (.modify rfl) (.cons savedRun (.cons readRun
    (.cons (.resumeThread resumeAt savedAt) (.refl _)))))

theorem invokeBackpressure {call func args core fnType opts inst instance_}
    (live : start.store.inst? inst = some instance_) (asyncMode : fnType.async_ = true)
    (pressure : instance_.hasBackpressure (liftTaskData (grow := grow) fnType opts inst (invokeCaller start)).needsExclusive = true) :
    let site := LiftSite.ofInvoke start call func args core fnType opts inst
    ∃ (entry : K1GateEntry site.launched site.storeAndThread.2 site.storeAndTask.2) (after : State grow sig),
      Steps profile ready (specDispatch ready impl) site.launched (List.replicate 9 .tau) entry.wait.blocked ∧
      Transition profile ready impl entry.wait.blocked (.invokeReturn (.task site.storeAndTask.2)) [.tau, .tau, .tau] after ∧
      after.cont? site.storeAndThread.2 = some entry.wait.saved := by
  let site := LiftSite.ofInvoke start call func args core fnType opts inst
  let task := liftTaskData fnType opts inst (invokeCaller start)
  have taskLive : site.launched.store.task? site.storeAndTask.2 = some task :=
    ArenaField.get?_alloc_self ArenaField.tasks site.start.store task
  have pressured : instance_.hasBackpressure task.needsExclusive = true := pressure
  obtain ⟨entry, gateSteps, _, _⟩ := lift_k1_gate (profile := profile) (ready := ready) (impl := impl)
    core task instance_ _ (atGate := site.launched) (thread := site.storeAndThread.2) rfl taskLive asyncMode live (by simp [pressured])
  have sameTask : entry.task = task := Option.some.inj (entry.liveTask.symm.trans taskLive)
  have reachedInstance : entry.waitingEntry.store.inst? entry.task.inst = some instance_ := by
    change site.launched.store.inst? entry.task.inst = some instance_
    rw [sameTask]
    exact live
  have reachedPressure : instance_.hasBackpressure entry.task.needsExclusive = true := by
    simpa only [sameTask] using pressure
  have unready : entry.wait.condition.eval (fun _ => false) entry.wait.incremented = false := by
    unfold K1Wait.condition K1Wait.incremented ReadyCond.eval
    change (match ArenaField.insts.get? (ArenaField.insts.modify entry.waitingEntry.store entry.task.inst
      InstState.incWaitingToEnter) entry.task.inst with
      | some reached => !reached.hasBackpressure entry.task.needsExclusive
      | none => false) = false
    rw [ArenaField.get?_modify_self, show ArenaField.insts.get? entry.waitingEntry.store entry.task.inst = _ from reachedInstance]
    change (!instance_.hasBackpressure entry.task.needsExclusive) = false
    rw [reachedPressure]
    rfl
  have outer : entry.rest = [⟨none, .prog (liftAfterThread site.storeAndTask.2 fnType.async_), [.prog invokeReturn]⟩] :=
    (congrArg List.tail entry.focused).symm
  have returned : entry.wait.blocked.ctl = [⟨none, .prog (.pure (.cancel (.task site.storeAndTask.2))), [.prog invokeReturn]⟩] := by
    change entry.rest = _
    rw [outer, asyncMode]
    rfl
  refine ⟨entry, _, appendSteps gateSteps (entry.wait.blocks unready), .invokeReturn returned, ?_⟩
  unfold StepDefs.hostFinish
  split <;> exact Config.cont?_setCont_self entry.waitingEntry site.storeAndThread.2 (some entry.wait.saved)

theorem liftAdmission (site : LiftSite grow sig) (admission : LiftAdmission site) :
    Steps profile ready (specDispatch ready impl) site.launched (List.replicate site.admissionLength .tau) site.onStart := by
  let task := site.storeAndTask.2
  let thread := site.storeAndThread.2
  let base := site.launched.store.setImplicitThread task thread
  have liveTask : ArenaField.tasks.get? site.launched.store task = some (liftTaskData site.fnType site.opts site.inst site.caller) :=
    ArenaField.get?_alloc_self ArenaField.tasks site.start.store _
  have marked : ArenaField.tasks.get? base task = some site.markedTask := by
    simp only [base, CStore.setImplicitThread, ArenaField.get?_modify_self, liveTask, Option.map_some, LiftSite.markedTask, thread]
  have liveInst : ArenaField.insts.get? base site.inst = some admission.instance_ := admission.live
  dsimp only [base] at marked liveInst
  have entryTask : ArenaField.tasks.get? site.entryStore task = some site.markedTask := by
    unfold LiftSite.entryStore
    split <;> exact marked
  have entryInst : ArenaField.insts.get? site.entryStore site.inst = some (site.entryInstance admission.instance_) := by
    unfold LiftSite.entryStore LiftSite.entryInstance
    change (ArenaField.insts.get? (if site.fnType.async_ && site.markedTask.needsExclusive then _ else base) site.inst) =
      some (if site.fnType.async_ && site.markedTask.needsExclusive then _ else _)
    split
    · rw [ArenaField.get?_modify_self, liveInst, Option.map_some]
    · exact liveInst
  have registered : ArenaField.tasks.get? (site.entryStore.registerThreadSt task thread) task = some site.registeredTask := by
    simp only [CStore.registerThreadSt, CStore.task?, CStore.inst?, entryTask,
      show site.markedTask.inst = site.inst from rfl, entryInst, Option.bind_some]
    rw [show (site.entryInstance admission.instance_).addThread? thread = _ from admission.capacity]
    change ArenaField.tasks.get? (ArenaField.tasks.modify site.entryStore task
      (fun reached => { reached with threads := reached.threads ++ [thread] })) task = some site.registeredTask
    rw [ArenaField.get?_modify_self, entryTask, Option.map_some]
    rfl
  have focused : site.launched.ctl = ⟨some thread, .prog (liftThreadBody .spec .none task site.core), []⟩ :: site.workerTail := rfl
  cases asyncMode : site.fnType.async_ <;> cases exclusive : site.markedTask.needsExclusive
  all_goals
    have mode : site.markedTask.ft.async_ = _ := asyncMode
    simp only [LiftSite.admissionLength, asyncMode, exclusive, Bool.false_and, Bool.true_and, Bool.false_eq_true,
      ite_false, ite_true]
    have first := Step.currentThread (prof := profile) (hr := ready) (dispatch := specDispatch ready impl) focused
    refine .cons first (.cons (.modify rfl) (.cons (.get rfl) ?_))
    simp [Prog.bind, marked, mode, pure]
    try
      have cleared : ¬ (admission.instance_.hasBackpressure site.markedTask.needsExclusive = true ∨
          0 < admission.instance_.numWaitingToEnter) := by
        simpa using admission.ungated asyncMode
      rw [exclusive] at cleared
      refine .cons (.get rfl) ?_
      simp [Prog.bind, pure, liveInst, show site.markedTask.inst = site.inst from rfl, Quirks.none, exclusive, cleared]
      try refine .cons (.modify rfl) ?_
    simp [LiftSite.entryStore, asyncMode, exclusive] at entryTask entryInst registered
    simp [Task.registerThread, Prog.bind]
    refine .cons (.get rfl) ?_
    dsimp only [thread, task] at entryTask entryInst registered ⊢
    simp [Prog.bind, pure, ArenaOps.updateSt, entryTask, show site.markedTask.inst = site.inst from rfl]
    refine .cons (.get rfl) ?_
    simp [Prog.bind, pure, entryInst, admission.capacity]
    refine .cons (.modify rfl) (.cons (.get rfl) ?_)
    simp [Prog.bind, pure, registered, Task.start]
    refine .cons (.get rfl) ?_
    simp [Prog.bind, pure, registered]
    refine .cons (.modify rfl) ?_
    unfold LiftSite.onStart LiftSite.argumentsTail
    simp [LiftSite.entryStore, Prog.bind, asyncMode, exclusive]
    refine Steps.refl _

theorem liftArguments (site : LiftSite grow sig) {call args}
    (live : ArenaField.callers.get? site.start.store site.caller = some (.host call args 0)) :
    Steps profile ready (specDispatch ready impl) site.onStart [.tau, .tau, .obs (.started call), .tau]
      (site.withArguments args) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, callerFrame⟩ :=
    CStore.registerThreadSt_frame site.storeAndTask.2 site.storeAndThread.2 site.entryStore
  have reached : ArenaField.callers.get? site.onStart.store site.registeredTask.caller = some (.host call args 0) := by
    change ((site.entryStore.registerThreadSt site.storeAndTask.2 site.storeAndThread.2).callers.get? _) = _
    rw [callerFrame]
    unfold LiftSite.entryStore
    split <;> exact live
  refine .cons (.call rfl) (.cons (.get rfl) ?_)
  simp [Prog.bind, pure, reached]
  exact .cons (.emit rfl) (.cons (.popProg rfl) (.refl _))

theorem liftEmptyCore (site : LiftSite grow sig) (empty : paramTypes site.registeredTask.ft = []) :
    ∃ next, Steps profile ready (specDispatch ready impl) (site.withArguments []) [.tau, .tau] (site.coreEntered [] next) := by
  suffices path : ∃ (read : CStore (core3 grow) → Session grow sig (Ret (core3 grow))),
      (site.withArguments []).ctl = ⟨some site.storeAndThread.2, .prog (.op .get read), []⟩ :: site.workerTail ∧
      ∃ next, read site.onStart.store = .op (.callCore site.core []) next by
    obtain ⟨read, focus, next, call⟩ := path
    have sameStore : (site.withArguments []).store = site.onStart.store := rfl
    exact ⟨next, .cons (.get focus) (.cons (.callCore (by rw [sameStore, call])) (.refl _))⟩
  refine ⟨_, rfl, ?_⟩
  cases mode : site.registeredTask.opts.async_ <;> cases callback : site.registeredTask.opts.callback <;>
    simp [Prog.bind, pure, ABI.flattenTypes, lowerFlatTypes, liftSyncTail, *] <;> exact ⟨_, rfl⟩

theorem allocatorSession {route : GiveEffectRoute} {bindings : List (Binding sig)} {callees : List (Callee sig)}
    {site : PayloadRoot.Site grow sig route} {older changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {beforeCheck beforeCanon left right reached reference : State grow sig}
    {checkEntryLabels canonEntryLabels checkLabels canonLabels mark}
    (checkEntry : Dispatch.Compatible profile ready bindings callees site.checked checkEntryLabels beforeCheck)
    (canonEntry : Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonEntryLabels beforeCanon)
    (seenEntry : PayloadPrefix.visible checkEntryLabels = PayloadPrefix.visible canonEntryLabels)
    (checkInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCheck [.tau, .tau, .tau] left)
    (canonInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCanon [.tau, .tau] right)
    (checked : Dispatch.Compatible profile ready bindings callees left checkLabels reached)
    (canonical : Dispatch.Compatible profile ready bindings callees right canonLabels reference)
    (cut : AllocatorCut profile ready bindings older changes left right reached reference checkLabels canonLabels mark) :
    let checkTrace := checkEntryLabels ++ [.tau, .tau, .tau] ++ checkLabels
    let canonTrace := canonEntryLabels ++ [.tau, .tau] ++ canonLabels
    Transition profile ready (hostWithComponent bindings callees) site.checked (.give route (.allocatorPrefix mark)) checkTrace reached ∧
      Steps profile ready (Dispatch.linked ready bindings callees) (site.reference site.referenceReply) canonTrace reference ∧
      PayloadPrefix.visible checkTrace = PayloadPrefix.visible canonTrace := by
  refine ⟨.giveAllocatorPrefix site rfl checkEntry canonEntry seenEntry checkInstall canonInstall checked canonical cut,
    appendSteps (appendSteps canonEntry.steps canonInstall) canonical.steps, ?_⟩
  have visibleAppend (front back : Trace grow sig) :
      PayloadPrefix.visible (front ++ back) = PayloadPrefix.visible front ++ PayloadPrefix.visible back :=
    List.filter_append ..
  simp only [visibleAppend]
  change (PayloadPrefix.visible checkEntryLabels ++ [] ++ PayloadPrefix.visible checkLabels) =
    (PayloadPrefix.visible canonEntryLabels ++ [] ++ PayloadPrefix.visible canonLabels)
  rw [seenEntry, cut.seen]

private theorem invokePrologueSteps {call func args}
    (focused : start.ctl = [.ofProg none (StepDefs.invokeProg call func args)]) :
    Steps profile ready (specDispatch ready impl) start [.tau, .tau, .tau] (invokeCall start call func args) := by
  let read : CStore (core3 grow) → P (core3 grow) (HostState sig) (Ret (core3 grow)) := fun store =>
    .op (.modify (ArenaOps.allocSt ArenaField.callers (.host call args 0))) fun _ =>
      .op (.modify StepDefs.enterHostSt) fun _ =>
        .op (.call (.funcInst func (invokeCaller { start with store }))) invokeReturn
  refine .cons (.get (th := none) (segs := []) (rest := []) (k := read) ?_) ?_
  · rw [focused]
    rfl
  exact .cons (.modify rfl) (.cons (.modify rfl) (.refl _))

private theorem invokeReturnSteps {cancel}
    (focused : start.ctl = [⟨none, .prog (.pure (.cancel cancel)), [.prog invokeReturn]⟩]) :
    Steps profile ready (specDispatch ready impl) start [.tau, .tau, .tau]
      (StepDefs.hostFinish (.cancel cancel) [] { start with store := StepDefs.leaveHostSt start.store }) := by
  exact .cons (.popProg focused) (.cons (.modify rfl) (.cons (.hostDone rfl) (.refl _)))

theorem transitionSteps {action leading} (edge : Transition profile ready impl start action leading finish) :
    Steps profile ready (specDispatch ready impl) start leading finish := by
  cases edge with
  | invoke hostReady fresh => exact .cons (.hostInvoke hostReady fresh) (.refl _)
  | invokePrologue focused => exact invokePrologueSteps focused
  | liftedLookup focused lookup => exact Dispatch.liftedLookup_steps focused lookup
  | liftLaunch site => exact liftLaunchSteps site
  | liftAdmit site admission => exact liftAdmission site admission
  | liftArguments site live => exact liftArguments site live
  | invokeReturn focused => exact invokeReturnSteps focused
  | tick tick => exact tick.selects_thread
  | coreInternal focused running step => exact .cons (.coreInternal focused running step) (.refl _)
  | coreReturned focused returned => exact .cons (.coreReturned focused returned) (.refl _)
  | coreTrap focused trapped => exact .cons (.coreTrap focused trapped) (.refl _)
  | commit resolve => exact (resolve.indexed_steps (profile := profile) (ready := ready) (impl := impl)).1
  | poll poll pending branch =>
    have outcomes := poll.delivers_returned (ready := ready) (impl := impl) pending
    cases branch with
    | unaligned bad => exact outcomes.1 bad
    | outside aligned sized bad => exact (outcomes.2 _ aligned sized).2 bad
    | inside aligned sized fits => exact (outcomes.2 _ aligned sized).1 fits
  | waitBlock wait empty => exact wait.blocks empty
  | waitReady wait available early allowed => exact wait.ready_choice available early allowed
  | waitResume resume saved => exact resume.resumes saved
  | waitTake delivery focused pending branch =>
    have outcomes := delivery.at_selection (ready := ready) (impl := impl) focused pending
    cases branch with
    | unaligned bad => exact outcomes.1 bad
    | outside aligned sized bad => exact (outcomes.2 _ aligned sized).2 bad
    | inside aligned sized fits => exact (outcomes.2 _ aligned sized).1 fits
  | cancelReturned cancel pending available => exact cancel.delivers_returned pending available
  | cancelReply cancel record focused live cancelled pending =>
    exact cancel.finish_cancelled_callback _ record focused live cancelled pending
  | cancelRequest cancel record live unresolved notDelivered notRequested notJoined =>
    exact cancel.requests record live unresolved notDelivered notRequested notJoined
  | cancelReentry request mode saved => exact request.reenters mode saved
  | cancelCallbackDone request => exact request.returns_from_callback
  | cancelPark wait => exact wait.blocks
  | cancelResume resume saved => exact resume.resumes saved
  | cancelTake resume pending => exact resume.delivers_returned pending
  | callbackCancelled wait focused live pending chosen => exact wait.cancel_calls_core focused live pending chosen
  | callbackPark wait availability => exact wait.parks availability
  | callbackResume resume saved => exact resume.resumes saved
  | callbackTake wait kind focused live noCancel setLive allowed selects tracked resolved pending chosen =>
    exact (wait.wait_takes_resolution (ready := ready) (impl := impl) kind focused live noCancel setLive allowed
      selects tracked resolved pending chosen).1
  | callbackResolveCancel entry empty resolution started indexed =>
    exact (entry.resolves_started (profile := profile) (ready := ready) (impl := impl) empty resolution started indexed).1
  | callbackBorrowTrap entry borrows =>
    exact (entry.enters_resolution (profile := profile) (ready := ready) (impl := impl)).2 borrows
  | callbackExit exit => exact (exit.unwinds (profile := profile) (ready := ready) (impl := impl)).1
  | closedCallback path => exact path.reaches.1
  | giveEntry _ _ _ _ _ run => exact run
  | giveRefused site _ issue _ run => exact site.refusal_resumes issue run
  | givePlacementTrap _ _ _ _ _ run => exact run
  | giveReturned _ _ overlay checked _ _ replies =>
    subst impl
    exact appendSteps checked.steps (replies.1 _)
  | giveStopped _ overlay checked _ _ _ _ =>
    subst impl
    exact checked.steps
  | giveRefusalReply site control caller =>
    exact Plain.give_completion_steps _ (by simpa [PayloadRoot.Site.reply, Cursor.control, caller] using control)
  | giveAllocatorPrefix _ overlay checkEntry _ _ checkInstall _ checked _ _ =>
    subst impl
    exact appendSteps (appendSteps checkEntry.steps checkInstall) checked.steps

theorem runSteps {actions labels} (path : Run profile ready impl start actions labels finish) :
    Steps profile ready (specDispatch ready impl) start labels finish := by
  induction path with
  | stop => exact .refl _
  | next edge _ ih => exact appendSteps (transitionSteps edge) ih

theorem giveBodyCut {bindings : List (Binding sig)} {callees : List (Callee sig)} {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) {check canon : Cursor (E := core3 grow) (HostState sig)} {keep}
    (path : PayloadPrefix.ReachesKeeping profile ready (Dispatch.coreOnly ready bindings) keep site.checked
      (site.reference site.referenceReply) check canon site.reply site.referenceReply)
    (dispatch : GiveCutDispatch profile ready bindings callees site) :
    GiveBodyCut profile ready bindings callees site check canon := by
  obtain ⟨outcome, checkLabels, canonLabels, reached, reference, checked, canonical, stores, seen, _, cut⟩ := path
  cases outcome with
  | returned value => exact .returned checked canonical seen stores cut.1 cut.2
  | refused issue =>
    have stopped : GiveStop site check (.bodyRefused issue) canonLabels reached reference := .refused cut
    obtain ⟨lhs, rhs⟩ := dispatch stopped stores seen checked canonical
    exact .stopped stopped (.giveStopped site rfl lhs rhs seen stores stopped)
  | trapped reason =>
    have stopped : GiveStop site check (.bodyTrap reason) canonLabels reached reference := .trapped cut.1 cut.2.1 cut.2.2
    obtain ⟨lhs, rhs⟩ := dispatch stopped stores seen checked canonical
    exact .stopped stopped (.giveStopped site rfl lhs rhs seen stores stopped)

theorem giveRefusalReply {bindings : List (Binding sig)} {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) {check : Cursor (E := core3 grow) (HostState sig)} {issue labels}
    (control : start.ctl = check.control (site.reply (.error issue)))
    (path : ReturnFrame.Occurrence.Prefix profile ready (Dispatch.coreOnly ready bindings)
      site.checked (.active 0 0) labels start (.active 0 0)) :
    ∃ segments, Transition profile ready impl start (.give route (.refusalReplied issue)) [.tau, .tau, .tau]
      (refusedBodyReply site start check segments issue) := by
  obtain ⟨segments, caller⟩ := site.reached_caller control path
  exact ⟨segments, .giveRefusalReply site control caller⟩

theorem giveCollectionCut {bindings : List (Binding sig)} {callees : List (Callee sig)} {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {type : Stored.TypeOf} {area : ABI.Layout} {entries : List Stored.Endpoints.RecordLower.Field}
    {index pointer : Nat} {left right last : State grow sig} {check : Cursor (E := core3 grow) (HostState sig)}
    {seen checkLabels canonLabels}
    (entry : Steps profile ready (Dispatch.coreOnly ready bindings) site.checked checkLabels left)
    (referenceEntry : Steps profile ready (Dispatch.coreOnly ready bindings) (site.reference site.referenceReply) canonLabels right)
    (seenEntry : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
    (cut : LinkedCallback.CollectionVisit.Outcome profile ready bindings older site.destination site.inst type area entries index pointer
      route.output left right last check site.reply site.referenceReply seen
      (LinkedCallback.CollectionVisit.reachesNext profile ready bindings left.store site.reply site.referenceReply))
    (dispatch : GiveCutDispatch profile ready bindings callees site) :
    ∃ canon, GiveBodyCut profile ready bindings callees site check canon := by
  obtain ⟨canon, path⟩ := cut.reaches
  exact ⟨canon, giveBodyCut site (PayloadPrefix.ReachesKeeping.prepend entry referenceEntry seenEntry path) dispatch⟩

theorem invokeLifted {call func args core fnType opts inst}
    (hostReady : StepDefs.HostReadyCfg start) (fresh : ∀ entry ∈ start.pending, entry.1 ≠ call)
    (lookup : start.store.func? func = some (.lifted core fnType opts inst)) :
    Run profile ready impl start [.invoke call func, .invokePrologue call func, .liftedLookup func (invokeCaller start)]
      [.host (.invoke call func args), .tau, .tau, .tau, .tau, .tau]
      (invokeLift start call func args core fnType opts inst) := by
  let reached := invokeCall (invokeStart start call func args) call func args
  have selected : reached.store.func? func = some (.lifted core fnType opts inst) := lookup
  exact .next (.invoke hostReady fresh) (.next (.invokePrologue rfl) (.next (.liftedLookup rfl selected) (.stop _)))

theorem runAppend {first second leading trailing} (left : Run profile ready impl start first leading middle)
    (right : Run profile ready impl middle second trailing finish) :
    Run profile ready impl start (first ++ second) (leading ++ trailing) finish := by
  induction left with
  | stop => exact right
  | next edge _ ih => simpa only [List.cons_append, List.append_assoc] using Run.next edge (ih right)

theorem runEmptyCore {site : LiftSite grow sig} {actions labels}
    (run : Run profile ready impl start actions labels (site.withArguments []))
    (empty : paramTypes site.registeredTask.ft = []) :
    ∃ next, Steps profile ready (specDispatch ready impl) start (labels ++ [.tau, .tau]) (site.coreEntered [] next) := by
  obtain ⟨next, core⟩ := liftEmptyCore site empty
  exact ⟨next, appendSteps (runSteps run) core⟩

theorem closedRecord {target labels} (edge : Transition profile ready impl start (.closedCallback target) labels finish) :
    finish.store.subtask? target = start.store.subtask? target := by
  cases edge with
  | closedCallback path => exact path.reaches.2

theorem takenRecord {target event labels}
    (edge : Transition profile ready impl start (.callbackTake target event) labels finish) :
    ∃ record, start.store.subtask? target = some record ∧
      finish.store.subtask? target = some { record with common := { record.common with pending := none }, lenders := none } := by
  cases edge with
  | callbackTake wait kind focused live noCancel setLive allowed selects tracked resolved pending chosen =>
    exact ⟨_, tracked, (wait.wait_takes_resolution (ready := ready) (impl := impl) kind focused live noCancel setLive allowed
      selects tracked resolved pending chosen).2⟩

theorem giveRoot {route : GiveEffectRoute} {bindings : List (Binding sig)} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) {body : Prop} (cut : PayloadRoot.Cut site profile ready bindings body impl) :
    ∃ phase labels finish, Transition profile ready impl site.start (.give route phase) labels finish ∧
      (phase = .entered → finish = site.checked ∧ body) := by
  cases cut with
  | refused issue silent run =>
    exact ⟨.refused issue, _, _, .giveRefused site linked issue silent run, fun equal => by cases equal⟩
  | placementTrap reason count verdict run =>
    exact ⟨.placementTrap reason, _, _, .givePlacementTrap site linked reason count verdict run, fun equal => by cases equal⟩
  | placed silent verdict prepared run body =>
    exact ⟨.entered, _, _, .giveEntry site linked silent verdict prepared run, fun _ => ⟨rfl, body⟩⟩

theorem giveReturned {route : GiveEffectRoute} {bindings : List (Binding sig)} {callees : List (ComponentCall.Callee sig)}
    (site : PayloadRoot.Site grow sig route) (value : route.output.Result) {reached reference : State grow sig}
    (comparison : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference)
    (agreement : GiveBodyAgreement profile ready bindings callees site reached reference) :
    ∃ checkLabels canonLabels left right,
      Transition profile ready (ComponentCall.hostWithComponent bindings callees) site.checked (.give route .returned)
        (checkLabels ++ [.tau, .tau, .tau]) left ∧
      Steps profile ready (Dispatch.linked ready bindings callees) (site.reference site.referenceReply) (canonLabels ++ [.tau]) right ∧
      PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
      LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference left right := by
  obtain ⟨⟨checkLabels, canonLabels, seen, checked, canonical⟩, left, right, replies⟩ := comparison
  obtain ⟨checkRun, canonRun⟩ := agreement checkLabels canonLabels checked canonical
  exact ⟨checkLabels, canonLabels, left, right, .giveReturned site value rfl checkRun canonRun seen replies,
    appendSteps canonRun.steps (replies.2.1 _), seen, replies⟩

theorem startedCancelDelivery {initial atHost : State grow sig} {target : SubtaskId} {index : Nat}
    {cancel : ParkedCancel initial target} (request : StartedCancel cancel) (synchronous : cancel.async_ = false)
    {actions labels} (interleaving : Run profile ready impl (request.syncWait synchronous).blocked actions labels atHost)
    (occurrence : ReturnFrame.Occurrence.ParkedPrefix profile ready (specDispatch ready impl) cancel.thread
      (request.syncWait synchronous).blocked labels atHost)
    (tick : SelectedTick cancel.thread atHost ready profile) (pending : PendingAt atHost.store target index) :
    let resume := SyncCancelResume.afterTick tick tick.waiting
    Run profile ready impl initial
      (.cancelCallbackDone target :: .cancelPark target :: (actions ++ [.tick cancel.thread, .cancelResume target, .cancel target .returned]))
      (List.replicate 20 .tau ++ (List.replicate 5 .tau ++ (labels ++
        (tick.selectionLabels ++ (List.replicate 3 .tau ++ List.replicate 6 .tau))))) resume.delivered := by
  let resume : SyncCancelResume cancel tick.atResume := SyncCancelResume.afterTick tick tick.waiting
  have saved : tick.atResume.cont? cancel.thread = some cancel.saved :=
    occurrence.reaches.2.trans (Config.cont?_setCont_self _ _ _)
  have wakes : Run profile ready impl atHost [.tick cancel.thread, .cancelResume target, .cancel target .returned]
      (tick.selectionLabels ++ (List.replicate 3 .tau ++ List.replicate 6 .tau)) resume.delivered := by
    refine .next (.tick tick) (.next (.cancelResume resume saved) ?_)
    exact .next (.cancelTake resume pending) (.stop _)
  exact .next (.cancelCallbackDone request) (.next (.cancelPark (request.syncWait synchronous)) (runAppend interleaving wakes))

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession
