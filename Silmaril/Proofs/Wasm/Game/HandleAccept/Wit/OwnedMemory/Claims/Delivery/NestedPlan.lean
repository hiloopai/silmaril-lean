module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
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
  | segment path => exact path.steps
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

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan
