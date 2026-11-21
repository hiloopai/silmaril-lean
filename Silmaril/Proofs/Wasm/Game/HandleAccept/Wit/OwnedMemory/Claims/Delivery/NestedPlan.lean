module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.StringPlan.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.StringPlan.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Public.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open LiveDispatch ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind} {ready : HostReady (HostState sig)}
  {bindings : List (Binding sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {start finish incoming : Config (core3 grow) (HostState sig)} {labels : Trace grow sig}
  {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}

private theorem append {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {before middle after : Config (core3 grow) (HostState sig)} {leading trailing}
    (front : Steps profile ready dispatch before leading middle) (back : Steps profile ready dispatch middle trailing after) :
    Steps profile ready dispatch before (leading ++ trailing) after := by
  induction front with
  | refl => exact back
  | cons step _ ih => exact .cons step (ih back)

private theorem silentVisible {trace : Trace grow sig} (silent : trace.all (· matches .tau) = true) :
    PayloadPrefix.visible trace = [] := by
  induction trace with
  | nil => rfl
  | cons label trace ih =>
    have main := List.all_eq_true.mp silent label List.mem_cons_self
    cases label <;> try contradiction
    apply ih
    exact List.all_eq_true.mpr fun next member => List.all_eq_true.mp silent next (List.mem_cons_of_mem _ member)

private theorem entryVisible {route : GiveEffectRoute}
    (entry : Transition profile ready base start (.give route .entered) labels finish) : PayloadPrefix.visible labels = [] := by
  cases entry with
  | giveEntry _ _ silent _ _ _ => exact silent
  | giveStopped _ _ _ _ _ _ stopped => cases stopped

private theorem visibleAppend (left right : Trace grow sig) :
    PayloadPrefix.visible (left ++ right) = PayloadPrefix.visible left ++ PayloadPrefix.visible right :=
  List.filter_append left right

private theorem visiblePrefix {left right : Trace grow sig} (initial : left <+: right) :
    PayloadPrefix.visible left <+: PayloadPrefix.visible right := by
  obtain ⟨tail, rfl⟩ := initial
  rw [visibleAppend]
  exact List.prefix_append _ _

private theorem prefixBefore {left right : Trace grow sig} (front : Trace grow sig) (initial : left <+: right) :
    front ++ left <+: front ++ right := by
  obtain ⟨tail, rfl⟩ := initial
  exact ⟨tail, List.append_assoc _ _ _⟩

theorem source (plan : NestedPlan bindings profile ready base start labels finish) :
    Steps profile ready (specDispatch ready base) start labels finish := by
  induction plan with
  | segment path => exact path
  | localSegment path => exact path.steps
  | commit resolve => exact (Transition.commit (impl := base) resolve).steps
  | poll poll pending branch => exact (Transition.poll (impl := base) poll pending branch).steps
  | waitBlock wait empty => exact (Transition.waitBlock (impl := base) wait empty).steps
  | waitReady wait available early allowed => exact (Transition.waitReady (impl := base) wait available early allowed).steps
  | waitResume resume saved => exact (Transition.waitResume (impl := base) resume saved).steps
  | waitTake delivery focused pending branch => exact (Transition.waitTake (impl := base) delivery focused pending branch).steps
  | cancelReturned cancel pending available => exact (Transition.cancelReturned (impl := base) cancel pending available).steps
  | cancelRequest cancel record live unresolved notDelivered notRequested notJoined =>
    exact (Transition.cancelRequest (impl := base) cancel record live unresolved notDelivered notRequested notJoined).steps
  | cancelReentry request mode saved => exact (Transition.cancelReentry (impl := base) request mode saved).steps
  | cancelCallbackDone request => exact (Transition.cancelCallbackDone (impl := base) request).steps
  | cancelPark wait => exact (Transition.cancelPark (impl := base) wait).steps
  | cancelResume resume saved => exact (Transition.cancelResume (impl := base) resume saved).steps
  | cancelFinish cancel record focused live resolved pending => exact cancel.finish_delivers record focused live resolved pending
  | sequence _ _ front back => exact append front back
  | give _ _ entry checkedBody _ _ replies _ _ => exact append (append entry.steps checkedBody) (replies.1 _)
  | stop _ _ entry checkedBody _ _ _ _ _ => exact append entry.steps checkedBody

theorem replayLocal (run : PayloadPrefix.LocalSteps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ reached, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming labels reached ∧
      HostFrame.Related.Paired older finish reached := by
  induction run generalizing incoming with
  | refl => exact ⟨_, .refl _, paired⟩
  | @cons before next finish label labels localFocus step tail ih =>
    have unchanged : UnchangedAt bindings before := by
      constructor
      · intro thread call cont frames rest focused
        simp [PayloadPrefix.LocalFocus, focused] at localFocus
      · intro thread core cont frames rest callee args focused calling
        simp [PayloadPrefix.LocalFocus, focused] at localFocus
    rcases LiveDispatch.classify_step (bindings := bindings) step with canonical | install
    · obtain ⟨_, reached, aligned | boundary⟩ := HostFrame.Related.paired_step paired canonical
      · obtain ⟨_, replay, last⟩ := ih aligned
        exact ⟨_, .cons reached replay, last⟩
      · cases boundary with
        | read cut _ =>
          cases cut with
          | mk focused _ => simp [PayloadPrefix.LocalFocus, focused] at localFocus
        | returned cut =>
          obtain ⟨_, _, _, _, _, _, _, focused⟩ := cut.left_input
          simp only [HostFrame.replace] at focused
          simp [PayloadPrefix.LocalFocus, focused] at localFocus
    · cases install with
      | direct focused give => exact (give (unchanged.direct focused)).elim
      | core focused calling give => exact (give (unchanged.core focused calling)).elim

theorem planOfSteps (run : Steps profile ready (specDispatch ready base) start labels finish) :
    NestedPlan bindings profile ready base start labels finish := by
  classical
  induction run with
  | refl _ => exact .localSegment (.refl _)
  | @cons before next finish label labels step _ tail =>
    have front : NestedPlan bindings profile ready base before [label] next := by
      by_cases localFocus : PayloadPrefix.LocalFocus before
      · exact .localSegment (.cons localFocus step (.refl _))
      · exact .segment (.cons step (.refl _))
    exact .sequence front tail

theorem comparedGive {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {entryLabels checkLabels canonLabels reached reference checked baseline} (value : route.output.Result)
    (entry : Transition profile ready base site.start (.give route .entered) entryLabels site.checked)
    (left : Steps profile ready (specDispatch ready base) site.checked checkLabels reached)
    (right : Steps profile ready (specDispatch ready base) (site.reference site.referenceReply) canonLabels reference)
    (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
    (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline) :
    NestedPlan bindings profile ready base site.start (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked :=
  .give site linked entry left (planOfSteps (append right (replies.2.1 _))) value replies seen

theorem rejoinedGive {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {entryLabels reached reference} (value : route.output.Result)
    (entry : Transition profile ready (Scheduled.host bindings) site.start (.give route .entered) entryLabels site.checked)
    (compared : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference) :
    ∃ checkLabels checked baseline,
      NestedPlan bindings profile ready (Scheduled.host bindings) site.start (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked ∧
      LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline := by
  obtain ⟨⟨checkLabels, canonLabels, seen, left, right⟩, checked, baseline, replies⟩ := compared
  exact ⟨checkLabels, checked, baseline, comparedGive site linked value entry
    (ReturnFrame.Occurrence.prefix_survives (left 0)).1 (ReturnFrame.Occurrence.prefix_survives (right 0)).1 seen replies, replies⟩

theorem linkedRejoinedGive {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {callees : List (ComponentCall.Callee sig)} {entryLabels reached reference} (value : route.output.Result)
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees)
      site.start (.give route .entered) entryLabels site.checked)
    (compared : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference) :
    ∃ checkLabels canonLabels checked baseline,
      LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline ∧
      (NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) site.start
          (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked ∨
        Dispatch.LookupCut profile ready bindings callees site.checked checkLabels reached ∨
        Dispatch.LookupCut profile ready bindings callees (site.reference site.referenceReply) canonLabels reference) := by
  obtain ⟨⟨checkLabels, canonLabels, seen, left, right⟩, checked, baseline, replies⟩ := compared
  refine ⟨checkLabels, canonLabels, checked, baseline, replies, ?_⟩
  rcases Dispatch.compatible_or_lookup (callees := callees) (ReturnFrame.Occurrence.prefix_survives (left 0)).1 with accepted | lookup
  · rcases Dispatch.compatible_or_lookup (callees := callees) (ReturnFrame.Occurrence.prefix_survives (right 0)).1 with canonical | lookup
    · exact .inl (comparedGive site linked value entry accepted.steps canonical.steps seen replies)
    · exact .inr (.inr lookup)
  · exact .inr (.inl lookup)

theorem linkedGiveStop {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {callees : List (ComponentCall.Callee sig)} {entryLabels checkLabels canonLabels reached reference check phase}
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees)
      site.start (.give route .entered) entryLabels site.checked)
    (left : Steps profile ready (Dispatch.coreOnly ready bindings) site.checked checkLabels reached)
    (right : Steps profile ready (Dispatch.coreOnly ready bindings) (site.reference site.referenceReply) canonLabels reference)
    (stop : GiveStop site check phase canonLabels reached reference) (store : reached.store = reference.store)
    (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels) :
    NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) site.start
        (entryLabels ++ checkLabels) reached ∨
      Dispatch.LookupCut profile ready bindings callees site.checked checkLabels reached ∨
      Dispatch.LookupCut profile ready bindings callees (site.reference site.referenceReply) canonLabels reference := by
  rcases Dispatch.compatible_or_lookup (callees := callees) left with accepted | lookup
  · rcases Dispatch.compatible_or_lookup (callees := callees) right with canonical | lookup
    · exact .inl (.stop site linked entry accepted.steps (planOfSteps canonical.steps) stop store seen)
    · exact .inr (.inr lookup)
  · exact .inr (.inl lookup)

theorem linkedAllocatorCut {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route}
    {callees : List (ComponentCall.Callee sig)} {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {beforeCheck beforeCanon left right reached reference : State grow sig}
    {checkEntryLabels canonEntryLabels checkLabels canonLabels mark}
    (cut : AllocatorCut profile ready bindings older changes left right reached reference checkLabels canonLabels (some mark))
    (checkEntry : Dispatch.Compatible profile ready bindings callees site.checked checkEntryLabels beforeCheck)
    (canonEntry : Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonEntryLabels beforeCanon)
    (seenEntry : PayloadPrefix.visible checkEntryLabels = PayloadPrefix.visible canonEntryLabels)
    (checkInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCheck [.tau, .tau, .tau] left)
    (canonInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCanon [.tau, .tau] right) :
    let checkTrace := checkEntryLabels ++ [.tau, .tau, .tau] ++ checkLabels
    let canonTrace := canonEntryLabels ++ [.tau, .tau] ++ canonLabels
    (Transition profile ready (ComponentCall.hostWithComponent bindings callees) site.checked
        (.give route (.allocatorPrefix (some mark))) checkTrace reached ∧
      Steps profile ready (Dispatch.linked ready bindings callees) (site.reference site.referenceReply) canonTrace reference ∧
      PayloadPrefix.visible checkTrace = PayloadPrefix.visible canonTrace) ∨
      Dispatch.LookupCut profile ready bindings callees left checkLabels reached ∨
      Dispatch.LookupCut profile ready bindings callees right canonLabels reference := by
  obtain ⟨_, _, path⟩ := cut.checked.survives
  obtain ⟨_, _, peer⟩ := cut.canonical.survives
  rcases Dispatch.compatible_or_lookup (callees := callees) (ReturnFrame.Occurrence.prefix_survives path).1 with good | lookup
  · rcases Dispatch.compatible_or_lookup (callees := callees) (ReturnFrame.Occurrence.prefix_survives peer).1 with matched | lookup
    · exact .inl (cut.session checkEntry canonEntry seenEntry checkInstall canonInstall good matched)
    · exact .inr (.inr lookup)
  · exact .inr (.inl lookup)

theorem runs (plan : NestedPlan bindings profile ready base start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ trace reached, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming trace reached ∧
      PayloadPrefix.visible trace <+: PayloadPrefix.visible labels ∧
      ((PayloadPrefix.visible labels = PayloadPrefix.visible trace ∧ HostFrame.Related.Paired older finish reached) ∨
        NestedCut bindings profile ready base older reached) := by
  classical
  induction plan generalizing incoming with
  | segment path =>
    cases LiveDispatch.paired_replay (bindings := bindings) paired path with
    | complete replay aligned => exact ⟨_, _, replay, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
    | request split _ replay aligned install _ =>
      exact ⟨_, _, replay, visiblePrefix ⟨_, split.symm⟩, .inr (.request aligned install)⟩
    | @boundary _ _ trailing _ _ _ _ split _ replay aligned cut lhs rhs _ =>
      refine ⟨_, _, append replay (.cons rhs (.refl _)), visiblePrefix ⟨trailing, ?_⟩, .inr (.boundary aligned cut lhs rhs)⟩
      simpa only [List.append_assoc, List.singleton_append] using split.symm
  | localSegment path =>
    obtain ⟨_, replay, aligned⟩ := replayLocal (bindings := bindings) path paired
    exact ⟨_, _, replay, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | commit resolve =>
    by_cases compatible : ∃ writer, incoming.host.writer.register resolve.tree = .ok writer ∧
        writer.accepted.length = resolve.writer.accepted.length
    · obtain ⟨_, registered, handle⟩ := compatible
      obtain ⟨_, replay, aligned, _, _⟩ :=
        Transition.commit_paired (profile := profile) (ready := ready) (impl := LiveDispatch.host bindings base)
          resolve paired registered handle
      exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
    · exact ⟨[], _, .refl _, ⟨_, rfl⟩, .inr (.publication resolve paired compatible)⟩
  | poll poll pending branch =>
    obtain ⟨_, replay, aligned, _⟩ :=
      Transition.poll_paired (ready := ready) (impl := LiveDispatch.host bindings base) poll pending branch paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | waitBlock wait empty =>
    obtain ⟨_, replay, aligned⟩ :=
      Transition.wait_block_paired (profile := profile) (ready := ready) (impl := LiveDispatch.host bindings base) wait empty paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | waitReady wait available early allowed =>
    obtain ⟨_, replay, aligned⟩ :=
      Transition.wait_ready_paired (ready := ready) (impl := LiveDispatch.host bindings base) wait available early allowed paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | waitResume resume saved =>
    obtain ⟨_, replay, aligned⟩ :=
      Transition.wait_resume_paired (profile := profile) (ready := ready) (impl := LiveDispatch.host bindings base) resume saved paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | waitTake delivery focused pending branch =>
    obtain ⟨_, replay, aligned, _⟩ :=
      Transition.wait_take_paired (ready := ready) (impl := LiveDispatch.host bindings base) delivery focused pending branch paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | cancelReturned cancel pending available =>
    obtain ⟨_, replay, aligned, _⟩ :=
      Transition.cancel_returned_paired (profile := profile) (ready := ready) (impl := LiveDispatch.host bindings base)
        cancel pending available paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | cancelRequest cancel record live unresolved notDelivered notRequested notJoined =>
    have installed := LiveDispatch.cancel_dispatch (bindings := bindings) (ready := ready) (base := base) record.onCancel
    obtain ⟨_, replay, aligned⟩ := Transition.cancel_request_paired (profile := profile) cancel record live unresolved
      notDelivered notRequested notJoined paired installed
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | cancelReentry request mode saved =>
    by_cases available : request.callee.state = .started →
        request.markedStore.threadReady (ready incoming.host) request.implicitThread = true
    · obtain ⟨_, replay, aligned⟩ := Transition.cancel_reentry_paired (profile := profile)
        (impl := LiveDispatch.host bindings base) request mode saved paired available
      exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
    · exact ⟨[], _, .refl _, ⟨_, rfl⟩, .inr (.cancelReadiness request mode paired available)⟩
  | cancelCallbackDone request =>
    obtain ⟨_, replay, aligned⟩ := Transition.cancel_callback_done_paired (profile := profile) (ready := ready)
      (impl := LiveDispatch.host bindings base) request paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | cancelPark wait =>
    obtain ⟨_, replay, aligned⟩ := Transition.cancel_park_paired (profile := profile) (ready := ready)
      (impl := LiveDispatch.host bindings base) wait paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | cancelResume resume saved =>
    obtain ⟨_, replay, aligned⟩ := Transition.cancel_resume_paired (profile := profile) (ready := ready)
      (impl := LiveDispatch.host bindings base) resume saved paired
    exact ⟨_, _, replay.steps, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | cancelFinish cancel record focused live resolved pending =>
    obtain ⟨_, replay, aligned⟩ := cancel_finish_paired (profile := profile) (ready := ready)
      (impl := LiveDispatch.host bindings base) cancel record focused live resolved pending paired
    exact ⟨_, _, replay, List.prefix_refl _, .inl ⟨rfl, aligned⟩⟩
  | sequence _ _ replayFront replayBack =>
    obtain ⟨_, _, front, frontPrefix, ⟨seenFront, aligned⟩ | cut⟩ := replayFront paired
    · obtain ⟨_, _, back, backPrefix, result⟩ := replayBack aligned
      refine ⟨_, _, append front back, ?_, ?_⟩
      · rw [visibleAppend, visibleAppend, seenFront]
        exact prefixBefore _ backPrefix
      · rcases result with ⟨seenBack, final⟩ | cut
        · exact .inl ⟨by rw [visibleAppend, visibleAppend, seenFront, seenBack], final⟩
        · exact .inr cut
    · refine ⟨_, _, front, ?_, .inr cut⟩
      rw [visibleAppend]
      exact frontPrefix.trans (List.prefix_append _ _)
  | @give _ site linked entryLabels checkLabels referenceLabels _ _ checked baseline entry _ _ _ replies seen replayBody =>
    by_cases selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree
    · obtain ⟨installed, _, silent, install, aligned⟩ := LiveDispatch.entry_paired (base := base) site linked paired selected
      obtain ⟨trace, reached, body, bodyPrefix, result⟩ := replayBody aligned
      have checkedSeen : PayloadPrefix.visible (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) =
          PayloadPrefix.visible (referenceLabels ++ [.tau]) := by
        rw [visibleAppend, visibleAppend, entryVisible entry, List.nil_append, seen, visibleAppend]
        rfl
      have liveSeen : PayloadPrefix.visible (installed ++ trace) = PayloadPrefix.visible trace := by
        rw [visibleAppend, silentVisible silent, List.nil_append]
      refine ⟨_, _, append install body, by rw [checkedSeen, liveSeen]; exact bodyPrefix, ?_⟩
      rcases result with ⟨bodySeen, rejoined⟩ | cut
      · have same := congrArg (fun state => HostFrame.replace state reached.host) replies.scheduler_rejoin
        change HostFrame.replace baseline reached.host = HostFrame.replace checked reached.host at same
        have baselinePair : ReturnFrame.Related.Paired older (HostFrame.replace baseline reached.host) reached := rejoined
        have caller : HostFrame.Related.Paired older checked reached :=
          show ReturnFrame.Related.Paired older (HostFrame.replace checked reached.host) reached from same ▸ baselinePair
        exact .inl ⟨checkedSeen.trans (bodySeen.trans liveSeen.symm), caller⟩
      · exact .inr cut
    · exact ⟨[], _, .refl _, ⟨_, rfl⟩, .inr (.unselected site linked paired selected)⟩
  | stop site linked entry checkedBody _ stopped store seen replayBody =>
    by_cases selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree
    · obtain ⟨_, _, silent, install, aligned⟩ := LiveDispatch.entry_paired (base := base) site linked paired selected
      obtain ⟨_, _, body, bodyPrefix, result⟩ := replayBody aligned
      refine ⟨_, _, append install body, ?_, .inr ?_⟩
      · rw [visibleAppend, visibleAppend, entryVisible entry, silentVisible silent, List.nil_append, List.nil_append, seen]
        exact bodyPrefix
      · rcases result with ⟨bodySeen, reached⟩ | cut
        · exact .stopped site stopped checkedBody body reached (store.trans reached.data.1) (seen.trans bodySeen)
        · exact cut
    · exact ⟨[], _, .refl _, ⟨_, rfl⟩, .inr (.unselected site linked paired selected)⟩

theorem stackfulEnd {task : TaskId} (edge : StackfulBodyEnd task start labels finish)
    (outer : ∀ (site : StackfulReturn start), site.segments = []) :
    NestedPlan bindings profile ready base start labels finish := by
  cases edge with
  | «prefix» => exact .segment (.refl _)
  | @exited site _ exit =>
    exact .sequence (.segment (Transition.stackfulComplete (impl := base) exit).steps)
      (.segment (Transition.stackfulExit (impl := base) exit (outer site)).steps)
  | unresolved site _ records last unresolved =>
    exact .segment (Transition.stackfulUnresolved (impl := base) site records.live records.implicitThread last unresolved).steps

theorem stackfulWorker {start reached first : State grow sig} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} {callees : List (ComponentCall.Callee sig)}
    (args : CalleeArguments returned) {Result : Type} (words : Result → List FlatValue)
    (lowered : StringPlanPair profile ready bindings callees first (fun result => args.enter (words result)))
    (asyncMode : args.record.opts.async_ = true) (callback : args.record.opts.callback = none)
    (body : ∀ (entry : State grow sig) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
      entry.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest →
      ∃ bodyLabels afterBody exitLabels afterExit deliveryLabels last,
        NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) entry bodyLabels afterBody ∧
        StackfulBodyEnd args.task afterBody exitLabels afterExit ∧
        (∀ (site : StackfulReturn afterBody), site.segments = []) ∧
        NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) afterExit deliveryLabels last) :
    ∃ leading entry trailing last,
      Steps profile ready (Dispatch.linked ready bindings callees) first leading entry ∧
      NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) first (leading ++ trailing) last ∧
      ((∃ (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
          entry.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest ∧
          NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) entry trailing last) ∨
        (StringPlanStopped profile ready bindings first leading entry ∧ trailing = [] ∧ last = entry)) := by
  obtain ⟨leading, entry, _, linked, entered | stopped⟩ := args.enter_stackful_after_strings words lowered asyncMode callback
  · obtain ⟨cursor, flat, control⟩ := entered
    obtain ⟨_, _, _, _, _, _, coreRun, ending, outer, delivery⟩ := body entry cursor flat control
    have tail := NestedPlan.sequence coreRun (.sequence (stackfulEnd ending outer) delivery)
    exact ⟨_, _, _, _, linked, .sequence (.segment linked) tail, .inl ⟨cursor, flat, control, tail⟩⟩
  · exact ⟨leading, entry, [], entry, linked, by simpa only [List.append_nil] using NestedPlan.segment (bindings := bindings) linked,
      .inr ⟨stopped, rfl, rfl⟩⟩

theorem localDataGive {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    (data : PayloadPrefix.LocalDataType (sig.payload site.tag)) (payload : Stored.Payload (sig.payload site.tag))
    (field : site.field = .data (sig.payload site.tag) payload) {entryLabels}
    (entryPath : Steps profile ready (specDispatch ready base) site.start entryLabels site.checked)
    (silent : PayloadPrefix.visible entryLabels = [])
    (placed : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok ())
    (prepared : Stored.OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ()) :
    ∃ bodyLabels finish, NestedPlan bindings profile ready base site.start (entryLabels ++ bodyLabels) finish ∧
      ((∃ value checkedLabels reached,
        Steps profile ready (specDispatch ready base) site.checked checkedLabels reached ∧
        reached.ctl = site.cursor.control (site.reply (.ok value)) ∧ bodyLabels = checkedLabels ++ [.tau, .tau, .tau] ∧
        finish.host = reached.host.record (route.reply site.destination site.start.host.nextTicket (.ok value)).1) ∨
      (finish.ctl = [] ∧ ∃ leading reason, PayloadPrefix.visible bodyLabels = leading ++ [.trap reason])) := by
  have entry := Transition.giveEntry site linked silent placed prepared entryPath
  have width : ptrTypeIn site.checked.store (site.destination.context site.inst) = site.destination.width := by
    have memory := site.destination.check_width site.start.store linked.destination
    simp only [PayloadRoot.Site.checked, PayloadRoot.Site.withBody, ptrTypeIn, RecordDestination.context,
      CanonOpts.ptrType, memory, Option.getD_some]
  let reference := site.reference site.referenceReply
  have canonAt := site.reference_at linked site.referenceReply
  rw [field] at canonAt
  have checkAt : site.checked.ctl = site.cursor.control
      (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
        (site.destination.context site.inst) site.destination.width (.data (sig.payload site.tag) payload) 0 route.output >>= site.reply) := by
    simp only [PayloadRoot.Site.checked, PayloadRoot.Site.withBody, field]
  obtain ⟨store, result, checkedLabels, canonLabels, checked, canon, seen, outcome⟩ :=
    PayloadPrefix.local_data_leaf_frame (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      site.destination site.inst (sig.payload site.tag) data payload 0 route.output site.start.store site.checked reference
      (Core3.Grows.refl _) width placed rfl site.cursor site.cursor rfl site.reply site.referenceReply checkAt canonAt
  cases result with
  | error reason =>
    obtain ⟨leading, trapped⟩ := outcome
    exact ⟨_, _, .stop site linked entry checked (.localSegment canon)
      (.trapped (check := site.cursor) rfl rfl ⟨leading, trapped⟩) rfl seen,
      .inr ⟨rfl, leading, reason, seen.trans trapped⟩⟩
  | ok value =>
    let reached := localLeafEnd site.checked site.checked.host store site.cursor.thread site.cursor.frames site.cursor.rest
      (fun result => site.reply (.ok result)) (.ok value)
    let canonical := localLeafEnd reference reference.host store site.cursor.thread site.cursor.frames site.cursor.rest
      site.referenceReply (.ok value)
    let older : ReturnFrame.Substitutions (core3 grow) (HostState sig) := fun _ _ => False
    have segments : ∀ frames, List.Forall₂ (ReturnFrame.Related.Segment older) frames frames :=
      fun _ => List.forall₂_same.mpr fun frame _ => .same frame
    have active : ∀ act, ReturnFrame.Related.Active older act act := fun ⟨_, _, frames⟩ => .mk (segments frames)
    have saved : ∀ act, ReturnFrame.Related.Saved older act act
      | none => .none
      | some act => .some (active act)
    have frame : LinkedCallback.ChildFrameOver older reached canonical site.cursor site.cursor :=
      ⟨rfl, rfl, rfl, rfl, List.forall₂_same.mpr fun act _ => saved act, rfl,
        segments site.cursor.frames, List.forall₂_same.mpr fun act _ => active act⟩
    obtain ⟨left, right, checkReply, canonReply, storeEq, checkHost, canonHost, paired⟩ :=
      LinkedCallback.MemorySequence.resume_returned_give site value frame (outcome.2.1 0) rfl rfl
    refine ⟨_, _, ?_, .inl ⟨value, checkedLabels, reached, checked, rfl, rfl, checkHost⟩⟩
    rw [← List.append_assoc]
    have popFocus : PayloadPrefix.LocalFocus canonical := by
      simp only [canonical, localLeafEnd, PayloadRoot.Site.cursor, PayloadRoot.Site.referenceReply, PayloadPrefix.LocalFocus]
      exact True.intro
    have pop : PayloadPrefix.LocalSteps profile ready (specDispatch ready base) canonical [.tau] right := by
      generalize traceEq : ([.tau] : Trace grow sig) = trace
      have run := canonReply (specDispatch ready base)
      rw [traceEq] at run
      cases run with
      | refl => contradiction
      | cons step tail =>
        cases traceEq
        cases tail
        exact .cons popFocus step (.refl _)
    exact .give site linked entry checked (.localSegment (canon.append pop)) value
      ⟨checkReply, canonReply, storeEq, checkHost, canonHost, paired⟩ seen

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan
