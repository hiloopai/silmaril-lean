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

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall (Callee)
open ComponentCall.Delivery ComponentCall.Delivery.FiniteSession
open PayloadPrefix (Cursor)

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start middle finish : State grow sig}

private theorem appendSteps {leading trailing}
    (left : Steps profile ready (specDispatch ready impl) start leading middle)
    (right : Steps profile ready (specDispatch ready impl) middle trailing finish) :
    Steps profile ready (specDispatch ready impl) start (leading ++ trailing) finish := by
  induction left with
  | refl => exact right
  | cons step _ ih => exact .cons step (ih right)

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
