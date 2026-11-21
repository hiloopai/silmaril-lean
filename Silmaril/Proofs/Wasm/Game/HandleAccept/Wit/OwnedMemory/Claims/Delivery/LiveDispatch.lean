module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch
open PayloadRoot ComponentCall.Delivery ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {route : GiveEffectRoute}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {bindings : List (Binding sig)}

private theorem readStore {Result : Type} (next : CStore (core3 grow) → Session grow sig Result)
    (store : CStore (core3 grow)) (other : HostState sig) (thread : Option ThreadId) :
    Plain.runBody (getStore.bind next) store other (some thread) = Plain.runBody (next store) store other (some thread) := rfl

private theorem readSelection {Result : Type} (handle : BitVec IntType.i32.width)
    (next : Option (Stored.OwnedMemory.Tree sig) → Session grow sig Result) (store : CStore (core3 grow))
    (other : HostState sig) (thread : Option ThreadId) :
    Plain.runBody ((select handle).bind next) store other (some thread) =
      Plain.runBody (next (Stored.Endpoints.Core.childFromHistory other.writer.accepted handle))
        store other (some thread) := rfl

private theorem admitAt {Result : Type} (site : Site grow sig route) (linked : site.Linked bindings)
    (other : HostState sig) (selection : Session grow sig (Except Issue Result)) :
    Plain.runBody (admit site.inst selection) site.start.store other (some site.thread) =
      Plain.runBody selection site.start.store other (some site.thread) := by
  simp only [admit, Prog.bind_eq, Plain.runBody_currentInst, linked.caller, readStore,
    bne_self_eq_false, linked.mayLeave, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]

private theorem entryWith {Result : Type} (site : Site grow sig route) (linked : site.Linked bindings)
    (other : HostState sig) (selection : Session grow sig (Except Issue Result)) (selected : Result)
    (next : Except Issue Result → Session grow sig (List FlatValue))
    (words : (LiveDispatch.host bindings base).embedder site.name site.functionType (route.args site.handle) =
      admit site.inst selection >>= next)
    (evaluation : Plain.runBody selection site.start.store other (some site.thread) =
      (site.start.store, other, .ok (.ok selected)))
    (body : (next (.ok selected) >>= fun reply => pure (.flat reply)) = site.referenceProgram >>= site.referenceReply) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) (HostFrame.replace site.start other)
        labels (HostFrame.replace (site.reference site.referenceReply) other) := by
  let impl := LiveDispatch.host bindings base
  let finish : Except Issue Result → Session grow sig (Ret (core3 grow)) :=
    fun result => next result >>= fun reply => pure (.flat reply)
  let start := HostFrame.replace site.start other
  let active := { start with ctl := site.cursor.control (admit site.inst selection >>= finish) }
  obtain ⟨labels, silent, run⟩ := Plain.runBody_thread_steps (admit site.inst selection) active site.start.store other
    (.ok selected) finish site.thread _ site.rest profile ready (specDispatch ready impl) rfl
    ((admitAt site linked other selection).trans evaluation)
  have installed : calloutBody Limits.spec Quirks.none ready impl site.start.store site.thread
      (.embedder site.name site.functionType) (route.args site.handle) = admit site.inst selection >>= finish := by
    simp only [calloutBody, Plain.thread_may_leave linked.caller linked.mayLeave, ite_true,
      show impl.embedder site.name site.functionType (route.args site.handle) = _ from words, Prog.bind_eq, Prog.bind_assoc]
    rfl
  refine ⟨.tau :: .tau :: .tau :: labels, ?_, ?_⟩
  · apply List.all_eq_true.mpr
    intro label member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | rfl | member
    · rfl
    · rfl
    · rfl
    · have tau := List.all_eq_true.mp silent label member
      cases label <;> first | rfl | contradiction
  · apply Plain.prepend_embedder_callout (start := start) linked.parked linked.calling
    rw [show start.store = site.start.store from rfl, installed]
    simpa only [active, start, finish, Site.cursor, PayloadPrefix.Cursor.control, HostFrame.replace, Site.reference, body] using run

theorem entry (site : Site grow sig route) (linked : site.Linked bindings) (other : HostState sig)
    (selected : Stored.Endpoints.Core.childFromHistory other.writer.accepted site.handle = some site.tree) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) (HostFrame.replace site.start other)
        labels (HostFrame.replace (site.reference site.referenceReply) other) := by
  cases route with
  | memory pointer =>
    let selection := selectMemoryDestination (grow := grow) (sig := sig) site.destination [.int .i32 site.handle, pointer]
    let next : Except Issue (Stored.OwnedMemory.Tree sig × Nat) → Session grow sig (List FlatValue)
      | .error issue => pure (completion 0 (.error issue)).2
      | .ok (tree, ptr) => memoryBody site.inst site.destination tree ptr
    have resolved := linked.linked
    have word := linked.admitted
    change Stored.flatType pointer = ABI.pointerType site.destination.width at word
    refine entryWith site linked other selection (site.tree, flatNat pointer) next ?_ ?_ ?_
    · simp only [LiveDispatch.host, selectBinding, resolved, GiveEffectRoute.action, GiveEffectRoute.args, memoryWords]
      rfl
    · simp only [selection, selectMemoryDestination, Execution.Runtime.Value.int, Prog.bind_eq, word,
        bne_self_eq_false, Bool.false_eq_true, ite_false, readStore, linked.destination, readSelection, selected]
      rfl
    · simp only [next, memoryBody, Site.tree, Site.referenceProgram,
        GiveEffectRoute.output, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
      rfl
  | flat schema =>
    let selection := selectFlatDestination (grow := grow) (sig := sig) site.destination schema [.int .i32 site.handle]
    let next : Except Issue (Stored.OwnedMemory.Tree sig) → Session grow sig (List FlatValue)
      | .error issue => pure (flatCompletion 0 (ABI.flatten site.destination.width schema) (.error issue)).2
      | .ok tree => flatBody site.inst site.destination schema tree
    have resolved := linked.linked
    have schemaMatches := linked.admitted
    change rootHasSchema site.tree schema = true at schemaMatches
    refine entryWith site linked other selection site.tree next ?_ ?_ ?_
    · simp only [LiveDispatch.host, selectBinding, resolved, GiveEffectRoute.action, GiveEffectRoute.args, flatWords]
      rfl
    · simp only [selection, selectFlatDestination, Execution.Runtime.Value.int, Prog.bind_eq,
        readStore, linked.destination, readSelection, selected, schemaMatches, Bool.not_true, Bool.false_eq_true, ite_false]
      rfl
    · simp only [next, flatBody, Site.tree, Site.referenceProgram, GiveEffectRoute.output,
        Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
      congr 1
      funext words
      change (Prog.pure (Ret.flat (E := core3 grow) (flatCompletion 0 _ (.ok words)).2) :
        Session grow sig (Ret (core3 grow))) =
        Prog.pure (Ret.flat (flatCompletion site.start.host.nextTicket _ (.ok words)).2)
      simp only [flatCompletion]
      split <;> rfl

theorem pairedEntry (site : Site grow sig route) (linked : site.Linked bindings)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : State grow sig}
    (paired : HostFrame.Related.Paired older site.start other)
    (selected : Stored.Endpoints.Core.childFromHistory other.host.writer.accepted site.handle = some site.tree) :
    ∃ labels entered,
      labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) other labels entered ∧
      HostFrame.Related.Paired older (site.reference site.referenceReply) entered := by
  have related : ReturnFrame.Related.Paired older (HostFrame.replace site.start other.host) other := paired
  obtain ⟨frames, rest, focused, residual⟩ := related.push_shared linked.parked
    (.prog (site.referenceProgram >>= site.referenceReply)) (.core site.core site.resume)
  let shadow : Site grow sig route := { site with start := HostFrame.replace other site.start.host, frames, rest }
  have shared := paired.data.1
  have shadowLinked : shadow.Linked bindings :=
    { parked := focused
      calling := shared ▸ linked.calling
      linked := linked.linked
      caller := shared ▸ linked.caller
      mayLeave := shared ▸ linked.mayLeave
      destination := shared ▸ linked.destination
      selected := linked.selected
      admitted := linked.admitted
      compiled := linked.compiled }
  obtain ⟨labels, silent, path⟩ := entry (profile := profile) (ready := ready) (base := base) shadow shadowLinked other.host selected
  exact ⟨labels, _, silent, path, residual⟩

theorem dispatchUnchanged {call : Call (core3 grow)} (unmodified : Unchanged bindings call) :
    specDispatch ready base call = specDispatch ready (LiveDispatch.host bindings base) call := by
  cases call with
  | hostCallout callee args =>
    cases callee with
    | embedder name kind =>
      change selectBinding bindings name kind = none at unmodified
      simp only [specDispatch, dispatch, hostCalloutProg, calloutBody, LiveDispatch.host, unmodified]
    | lowered | builtin => rfl
  | threadBody body => cases body <;> rfl
  | onCancel cancel => cases cancel <;> rfl
  | _ => rfl

variable {start finish : Config (core3 grow) (HostState sig)}

theorem replayStep {label} (step : Step profile ready (specDispatch ready base) start label finish)
    (unmodified : UnchangedAt bindings start) :
    Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) start label finish := by
  cases step with
  | call focused => rw [dispatchUnchanged (unmodified.direct focused)]; exact .call focused
  | coreCallout focused calling => rw [dispatchUnchanged (unmodified.core focused calling)]; exact .coreCallout focused calling
  | newThread focused allocated =>
    unfold StepDefs.threadAct
    rw [dispatchUnchanged (bindings := bindings) (call := .threadBody _) trivial]
    exact .newThread focused allocated
  | popProg focused => exact .popProg focused
  | popCore focused => exact .popCore focused
  | threadExit focused => exact .threadExit focused
  | hostDone focused => exact .hostDone focused
  | callCore focused => exact .callCore focused
  | coreInternal focused status inner => exact .coreInternal focused status inner
  | coreReturned focused status => exact .coreReturned focused status
  | coreTrap focused status => exact .coreTrap focused status
  | get focused => exact .get focused
  | modify focused => exact .modify focused
  | trap focused => exact .trap focused
  | choose answer focused allowed => exact .choose answer focused allowed
  | currentThread focused => exact .currentThread focused
  | block focused => exact .block focused
  | blockSwitch focused saved => exact .blockSwitch focused saved
  | resumeThread focused saved => exact .resumeThread focused saved
  | hostGet focused => exact .hostGet focused
  | hostSet focused => exact .hostSet focused
  | emit focused => exact .emit focused
  | fault failed => exact .fault failed
  | hostInvoke enabled fresh => exact .hostInvoke enabled fresh
  | hostTick enabled => exact .hostTick enabled
  | hostCancel enabled pending unresolved => exact .hostCancel enabled pending unresolved
  | hostRun enabled => exact .hostRun enabled

theorem replay {labels} (run : Steps profile ready (specDispatch ready base) start labels finish)
    (closed : UnchangedThrough bindings profile ready base start labels finish) :
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start labels finish := by
  induction run with
  | refl => exact .refl _
  | @cons before middle after label labels step tail ih =>
    refine .cons (replayStep step (closed (leading := []) rfl (.refl _) (.cons step tail))) (ih ?_)
    intro leading cut next trailing split front back
    exact closed (leading := label :: leading) (congrArg (List.cons label) split) (.cons step front) back

theorem replayGrowing {labels} (run : CoreGrowthSteps profile ready (specDispatch ready base) start labels finish)
    (closed : UnchangedThrough bindings profile ready base start labels finish) :
    CoreGrowthSteps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start labels finish := by
  induction run with
  | refl => exact .refl _
  | @cons before middle after label labels grows step tail ih =>
    refine .cons grows (replayStep step (closed (leading := []) rfl (.refl _) (.cons step tail.steps))) (ih ?_)
    intro leading cut next trailing split front back
    exact closed (leading := label :: leading) (congrArg (List.cons label) split) (.cons step front) back

theorem nestedReturn (site : Site grow sig route) (linked : site.Linked bindings)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other checked baseline : State grow sig}
    (paired : HostFrame.Related.Paired older site.start other)
    (selected : Stored.Endpoints.Core.childFromHistory other.host.writer.accepted site.handle = some site.tree)
    {value : route.output.Result} {reached reference : State grow sig} {labels}
    (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline)
    (body : CoreGrowthSteps profile ready (specDispatch ready base) (site.reference site.referenceReply) labels baseline)
    (closed : UnchangedThrough bindings profile ready base (site.reference site.referenceReply) labels baseline) :
    let dispatch := specDispatch ready (LiveDispatch.host bindings base)
    ∃ installed entered, installed.all (· matches .tau) = true ∧ Steps profile ready dispatch other installed entered ∧
      NestedReplay profile ready dispatch older (site.reference site.referenceReply) entered labels checked := by
  dsimp only
  obtain ⟨installed, entered, silent, install, inside⟩ := pairedEntry site linked paired selected
  refine ⟨installed, entered, silent, install, ?_⟩
  rcases HostFrame.Related.paired_growing_steps inside (replayGrowing (bindings := bindings) body closed) with completed | cut
  · obtain ⟨last, path, related⟩ := completed
    have aligned := replies.scheduler_rejoin
    have same := congrArg (fun state => HostFrame.replace state last.host) aligned
    change HostFrame.replace baseline last.host = HostFrame.replace checked last.host at same
    have basePair : ReturnFrame.Related.Paired older (HostFrame.replace baseline last.host) last := related
    have callerPair : ReturnFrame.Related.Paired older (HostFrame.replace checked last.host) last := same ▸ basePair
    exact .rejoined path.steps callerPair
  · obtain ⟨_, _, _, _, _, _, _, split, left, right, related, boundary, lstep, rstep, _⟩ := cut
    exact .boundary split left.steps right.steps related boundary lstep rstep

theorem append {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {middle : Config (core3 grow) (HostState sig)} {leading trailing}
    (first : Steps profile ready dispatch start leading middle) (tail : Steps profile ready dispatch middle trailing finish) :
    Steps profile ready dispatch start (leading ++ trailing) finish := by
  induction first with
  | refl => exact tail
  | cons step _ ih => exact .cons step (ih tail)

private theorem neutralRetarget {action labels} {impl : HostImpl (core3 grow) (HostState sig)}
    (edge : Transition profile ready base start action labels finish) (closed : JournalNeutralAction action) :
    Transition profile ready impl start action labels finish := by
  cases edge <;> try contradiction
  case invoke available fresh => exact .invoke available fresh
  case invokePrologue focused => exact .invokePrologue focused
  case liftedLookup focused lookup => exact .liftedLookup focused lookup
  case liftLaunch site => exact .liftLaunch site
  case liftAdmit site admission => exact .liftAdmit site admission
  case liftArguments site live => exact .liftArguments site live
  case invokeReturn focused => exact .invokeReturn focused
  case stackfulComplete exit => exact .stackfulComplete exit
  case stackfulUnresolved => exact .stackfulUnresolved (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  case stackfulExit exit empty => exact .stackfulExit exit empty
  case coreInternal focused running steps => exact .coreInternal focused running steps
  case coreReturned focused returned => exact .coreReturned focused returned
  case coreTrap focused trapped => exact .coreTrap focused trapped
  case coreReply focused => exact .coreReply focused
  case poll poll pending branch => exact .poll poll pending branch
  case waitBlock wait empty => exact .waitBlock wait empty
  case waitReady early allowed wait available => exact .waitReady wait available early allowed
  case waitResume resume saved => exact .waitResume resume saved
  case waitTake delivery focused pending branch => exact .waitTake delivery focused pending branch
  case cancelReturned cancel pending available => exact .cancelReturned cancel pending available
  case cancelReply cancel record cancelled pending focused live => exact .cancelReply cancel record focused live cancelled pending
  case cancelPark wait => exact .cancelPark wait
  case cancelResume resume saved => exact .cancelResume resume saved
  case cancelTake resume pending => exact .cancelTake resume pending

theorem interleavingRetarget {actions labels incoming outgoing} {impl : HostImpl (core3 grow) (HostState sig)}
    (run : JournalInterleaving profile ready base start incoming actions labels finish outgoing) :
    JournalInterleaving profile ready impl start incoming actions labels finish outgoing := by
  induction run with
  | stop state other => exact .stop state other
  | neutral edge closed _ ih => exact .neutral (neutralRetarget edge closed) closed ih
  | commit resolve registered sameHandle _ ih => exact .commit resolve registered sameHandle ih
  | tick tick agrees _ ih => exact .tick tick agrees ih

private theorem neutralHost {action labels} (edge : Transition profile ready base start action labels finish)
    (closed : JournalNeutralAction action) : finish.host = start.host := by
  cases edge <;> try contradiction
  case invokeReturn =>
    cases call : start.pending.getLast?.map (·.1) <;> simp [StepDefs.hostFinish, StepDefs.lastCall?, call, Config.setCancel]
  case poll poll pending branch => cases branch <;> rfl
  case waitReady early allowed wait available => cases early <;> rfl
  case waitTake delivery focused pending branch => cases branch <;> rfl
  all_goals rfl

theorem interleavingRoots {actions labels incoming outgoing}
    (run : JournalInterleaving profile ready base start incoming actions labels finish outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted) : outgoing.writer.accepted = finish.host.writer.accepted := by
  induction run with
  | stop => exact roots
  | neutral edge closed _ ih => exact ih (roots.trans (congrArg (·.writer.accepted) (neutralHost edge closed)).symm)
  | commit resolve registered _ _ ih =>
    apply ih
    change _ = resolve.writer.accepted
    exact (Stored.OwnedMemory.Claims.register_claims registered).1.trans
      ((congrArg (resolve.tree :: ·) roots).trans (Stored.OwnedMemory.Claims.register_claims resolve.registered).1.symm)
  | tick tick _ _ ih => exact ih roots

theorem interleavingSteps {actions labels incoming outgoing}
    (between : JournalInterleaving profile ready base start incoming actions labels finish outgoing) :
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base))
      (HostFrame.replace start incoming) labels (HostFrame.replace finish outgoing) :=
  (interleavingRetarget (impl := LiveDispatch.host bindings base) between).runs.2.steps

theorem afterInterleaving (site : Site grow sig route) (linked : site.Linked bindings) {incoming outgoing : HostState sig}
    (selected : Stored.Endpoints.Core.childFromHistory outgoing.writer.accepted site.handle = some site.tree)
    {leading middleLabels actions}
    (prior : Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start leading
      (HostFrame.replace finish incoming))
    (between : JournalInterleaving profile ready base finish incoming actions middleLabels site.start outgoing) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start
        (leading ++ middleLabels ++ labels) (HostFrame.replace (site.reference site.referenceReply) outgoing) := by
  obtain ⟨labels, silent, entered⟩ := entry (profile := profile) (ready := ready) (base := base) site linked outgoing selected
  exact ⟨labels, silent, append (append prior (interleavingSteps between)) entered⟩

theorem afterSameRoots (site : Site grow sig route) (linked : site.Linked bindings) {incoming outgoing : HostState sig}
    (roots : incoming.writer.accepted = finish.host.writer.accepted) {leading middleLabels actions}
    (prior : Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start leading
      (HostFrame.replace finish incoming))
    (between : JournalInterleaving profile ready base finish incoming actions middleLabels site.start outgoing) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start
        (leading ++ middleLabels ++ labels) (HostFrame.replace (site.reference site.referenceReply) outgoing) := by
  have selected : Stored.Endpoints.Core.childFromHistory outgoing.writer.accepted site.handle = some site.tree := by
    rw [interleavingRoots between roots]
    exact linked.selected
  exact afterInterleaving site linked selected prior between

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch
