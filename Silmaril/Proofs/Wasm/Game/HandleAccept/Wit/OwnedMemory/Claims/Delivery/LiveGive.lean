module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveGive.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveGive

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {route : GiveEffectRoute}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {start : State grow sig}
  {bindings : List (Binding sig)} {callees : List (Callee sig)}

private theorem appendSteps {Host : Type} {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    {hr : HostReady Host} {before middle finish : Config (core3 grow) Host} {leading trailing}
    (first : Steps profile hr dispatch before leading middle) (tail : Steps profile hr dispatch middle trailing finish) :
    Steps profile hr dispatch before (leading ++ trailing) finish := by
  induction first with
  | refl => exact tail
  | cons step _ ih => exact .cons step (ih tail)

private theorem silentVisible {labels : Trace grow sig} (silent : labels.all (· matches .tau) = true) :
    PayloadPrefix.visible labels = [] := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
    have main := List.all_eq_true.mp silent label (List.mem_cons_self)
    cases label <;> try contradiction
    apply ih
    exact List.all_eq_true.mpr fun next member => List.all_eq_true.mp silent next (List.mem_cons_of_mem _ member)

private theorem entryVisible {before after : State grow sig} {labels}
    (entry : Transition profile ready (hostWithComponent bindings callees) before (.give route .entered) labels after) :
    PayloadPrefix.visible labels = [] := by
  cases entry with
  | giveEntry _ _ silent _ _ _ => exact silent
  | giveStopped _ _ _ _ _ _ stopped => cases stopped

private theorem episodeWithReplay (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {actions leading entryLabels checked incoming outgoing phase checkLabels canonLabels reference}
    (between : JournalInterleaving profile ready (hostWithComponent bindings callees)
      start incoming actions leading site.start outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted)
    (entry : Transition profile ready (hostWithComponent bindings callees) site.start (.give route .entered) entryLabels site.checked)
    (body : Transition profile ready (hostWithComponent bindings callees) site.checked (.give route phase) checkLabels checked)
    (canonical : Steps profile ready (Dispatch.linked ready bindings callees) (site.reference site.referenceReply)
      canonLabels reference)
    (visible : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
    (observes : GivePrefixObservations profile ready bindings callees (site.reference site.referenceReply)
      outgoing canonLabels reference) :
    ∃ installed after,
      Run profile ready (hostWithComponent bindings callees) start
        (actions ++ [.give route .entered, .give route phase]) (leading ++ entryLabels ++ checkLabels) checked ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (hostWithComponent bindings callees)))
        (HostFrame.replace start incoming) (leading ++ installed ++ canonLabels) (HostFrame.replace reference after) ∧
      PayloadPrefix.visible (leading ++ entryLabels ++ checkLabels) = PayloadPrefix.visible (leading ++ installed ++ canonLabels) ∧
      Steps profile ready (Dispatch.linked ready bindings callees) (HostFrame.replace (site.reference site.referenceReply) outgoing)
        canonLabels (HostFrame.replace reference after) := by
  obtain ⟨installed, silent, reachedEntry⟩ := LiveDispatch.entry_after_equal_roots site linked roots (.refl _) between
  obtain ⟨after, reachedBody⟩ := (JournalReplay.of_steps canonical outgoing).complete_of_reads_agree observes.reads
  refine ⟨installed, after, ?_, appendSteps reachedEntry (LiveDispatch.replay reachedBody (observes.installs reachedBody)),
    ?_, reachedBody⟩
  · simpa only [List.append_nil, List.append_assoc] using between.runs.1.append (.next entry (.next body (.stop _)))
  · have silentEntry := entryVisible entry
    have silentInstall := silentVisible silent
    simp only [PayloadPrefix.visible, List.filter_append] at silentEntry silentInstall visible ⊢
    rw [silentEntry, silentInstall, visible]

theorem episode (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {actions leading entryLabels checked incoming outgoing phase checkLabels canonLabels reference}
    (between : JournalInterleaving profile ready (hostWithComponent bindings callees)
      start incoming actions leading site.start outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted)
    (entry : Transition profile ready (hostWithComponent bindings callees) site.start (.give route .entered) entryLabels site.checked)
    (body : Transition profile ready (hostWithComponent bindings callees) site.checked (.give route phase) checkLabels checked)
    (canonical : Steps profile ready (Dispatch.linked ready bindings callees) (site.reference site.referenceReply)
      canonLabels reference)
    (visible : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
    (observes : GivePrefixObservations profile ready bindings callees (site.reference site.referenceReply)
      outgoing canonLabels reference) :
    ∃ installed after,
      Run profile ready (hostWithComponent bindings callees) start
        (actions ++ [.give route .entered, .give route phase]) (leading ++ entryLabels ++ checkLabels) checked ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (hostWithComponent bindings callees)))
        (HostFrame.replace start incoming) (leading ++ installed ++ canonLabels) (HostFrame.replace reference after) ∧
      PayloadPrefix.visible (leading ++ entryLabels ++ checkLabels) = PayloadPrefix.visible (leading ++ installed ++ canonLabels) := by
  obtain ⟨installed, after, checkRun, canonRun, seen, _⟩ := episodeWithReplay site linked between roots entry body canonical visible observes
  exact ⟨installed, after, checkRun, canonRun, seen⟩

theorem stopped (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {actions leading entryLabels incoming outgoing phase checkLabels canonLabels reached reference}
    (between : JournalInterleaving profile ready (hostWithComponent bindings callees)
      start incoming actions leading site.start outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted)
    (entry : Transition profile ready (hostWithComponent bindings callees) site.start (.give route .entered) entryLabels site.checked)
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (stop : GiveStop site check phase canonLabels reached reference) (sameStore : reached.store = reference.store)
    (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
    (checked : Steps profile ready (Dispatch.coreOnly ready bindings) site.checked checkLabels reached)
    (canonical : Steps profile ready (Dispatch.coreOnly ready bindings) (site.reference site.referenceReply) canonLabels reference)
    (agreement : GiveCutDispatch profile ready bindings callees site)
    (observes : GivePrefixObservations profile ready bindings callees (site.reference site.referenceReply)
      outgoing canonLabels reference) :
    ∃ installed after,
      Run profile ready (hostWithComponent bindings callees) start
        (actions ++ [.give route .entered, .give route phase]) (leading ++ entryLabels ++ checkLabels) reached ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (hostWithComponent bindings callees)))
        (HostFrame.replace start incoming) (leading ++ installed ++ canonLabels) (HostFrame.replace reference after) ∧
      PayloadPrefix.visible (leading ++ entryLabels ++ checkLabels) = PayloadPrefix.visible (leading ++ installed ++ canonLabels) ∧
      reached.store = (HostFrame.replace reference after).store := by
  obtain ⟨checkPath, canonPath⟩ := agreement stop sameStore seen checked canonical
  obtain ⟨installed, after, checkRun, canonRun, visible⟩ := episode site linked between roots entry
    (.giveStopped site rfl checkPath canonPath seen sameStore stop) canonPath.steps seen observes
  exact ⟨installed, after, checkRun, canonRun, visible, sameStore⟩

theorem sessionRuns {incoming actions finish} (session : LiveSession profile ready bindings callees start incoming actions finish) :
    ∃ checkLabels canonLabels reference,
      Run profile ready (hostWithComponent bindings callees) start actions checkLabels finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (hostWithComponent bindings callees)))
        (HostFrame.replace start incoming) canonLabels reference ∧
      PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧ finish.store = reference.store := by
  induction session with
  | interleaving path =>
    exact ⟨_, _, _, path.runs.1, LiveDispatch.interleaving_steps path, rfl, rfl⟩
  | @returned route site linked before journal actions leading outgoing entryLabels checkLabels canonLabels left right reached
      reference finish tailActions between roots entry value checked canonical replies visible observes tail ih =>
    have body := Transition.giveReturned site value rfl checked canonical visible replies
    have canonBody := appendSteps canonical.steps (replies.2.1 _)
    have bodySeen : PayloadPrefix.visible (checkLabels ++ [.tau, .tau, .tau]) = PayloadPrefix.visible (canonLabels ++ [.tau]) := by
      simpa [PayloadPrefix.visible, List.filter_append] using visible
    obtain ⟨_, after, checkRun, canonRun, seen, replay⟩ := episodeWithReplay site linked between roots entry body canonBody
      bodySeen observes
    obtain ⟨_, _, _, checkTail, canonTail, tailSeen, sameStore⟩ := ih replay
    have aligned := replies.scheduler_rejoin
    have rejoined : HostFrame.replace _ after = HostFrame.replace _ after :=
      congrArg (fun state => HostFrame.replace state after) aligned
    refine ⟨_, _, _, checkRun.append checkTail, appendSteps (rejoined ▸ canonRun) canonTail, ?_, sameStore⟩
    simp only [PayloadPrefix.visible, List.filter_append] at seen tailSeen ⊢
    rw [seen, tailSeen]
  | cut site linked between roots entry body canonical store visible observes =>
    obtain ⟨_, _, checkRun, canonRun, seen⟩ := episode site linked between roots entry body canonical visible observes
    exact ⟨_, _, _, checkRun, canonRun, seen, store⟩

theorem ofRejoined (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {incoming outgoing actions leading entryLabels tailActions finish reached reference}
    (between : JournalInterleaving profile ready (hostWithComponent bindings callees)
      start incoming actions leading site.start outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted)
    (entry : Transition profile ready (hostWithComponent bindings callees) site.start (.give route .entered) entryLabels site.checked)
    (value : route.output.Result)
    (comparison : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference)
    (agreement : GiveBodyAgreement profile ready bindings callees site reached reference)
    (observes : ∀ {canonLabels left right},
      Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonLabels reference →
      LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference left right →
        GivePrefixObservations profile ready bindings callees (site.reference site.referenceReply) outgoing (canonLabels ++ [.tau]) right)
    (tail : ∀ {canonLabels left right after},
      LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference left right →
      Steps profile ready (Dispatch.linked ready bindings callees)
        (HostFrame.replace (site.reference site.referenceReply) outgoing) (canonLabels ++ [.tau]) (HostFrame.replace right after) →
      LiveSession profile ready bindings callees left after tailActions finish) :
    LiveSession profile ready bindings callees start incoming
      ((actions ++ [.give route .entered, .give route .returned]) ++ tailActions) finish := by
  obtain ⟨⟨checkLabels, canonLabels, seen, checked, canonical⟩, left, right, replies⟩ := comparison
  obtain ⟨checkRun, canonRun⟩ := agreement checkLabels canonLabels checked canonical
  exact .returned site linked between roots entry value checkRun canonRun replies seen (observes canonRun replies) (tail replies)

private theorem pairedStore {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : State grow sig} (paired : ReturnFrame.Related.Paired changes left right) : left.store = right.store := by
  cases paired
  rfl

theorem ofAllocator (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {incoming outgoing actions leading entryLabels}
    (between : JournalInterleaving profile ready (hostWithComponent bindings callees)
      start incoming actions leading site.start outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted)
    (entry : Transition profile ready (hostWithComponent bindings callees) site.start (.give route .entered) entryLabels site.checked)
    {older changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {beforeCheck beforeCanon left right reached reference : State grow sig}
    {checkEntryLabels canonEntryLabels checkLabels canonLabels mark}
    (cut : AllocatorCut profile ready bindings older changes left right reached reference checkLabels canonLabels mark)
    (checkEntry : Dispatch.Compatible profile ready bindings callees site.checked checkEntryLabels beforeCheck)
    (canonEntry : Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonEntryLabels beforeCanon)
    (seenEntry : PayloadPrefix.visible checkEntryLabels = PayloadPrefix.visible canonEntryLabels)
    (checkInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCheck [.tau, .tau, .tau] left)
    (canonInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCanon [.tau, .tau] right)
    (checked : Dispatch.Compatible profile ready bindings callees left checkLabels reached)
    (canonical : Dispatch.Compatible profile ready bindings callees right canonLabels reference)
    (observes : GivePrefixObservations profile ready bindings callees (site.reference site.referenceReply)
      outgoing (canonEntryLabels ++ [.tau, .tau] ++ canonLabels) reference) :
    LiveSession profile ready bindings callees start incoming (actions ++ [.give route .entered, .give route (.allocatorPrefix mark)])
      reached := by
  obtain ⟨body, path, seen⟩ := cut.session checkEntry canonEntry seenEntry checkInstall canonInstall checked canonical
  have paired : ReturnFrame.Related.Paired changes (HostFrame.replace reached reference.host) reference := cut.paired
  have sameStore := pairedStore paired
  exact .cut site linked between roots entry body path sameStore seen observes

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveGive
