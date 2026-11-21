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
  obtain ⟨installed, silent, reachedEntry⟩ := LiveDispatch.entry_after_equal_roots site linked roots (.refl _) between
  obtain ⟨after, reachedBody⟩ := (JournalReplay.of_steps canonical outgoing).complete_of_reads_agree observes.reads
  refine ⟨installed, after, ?_, appendSteps reachedEntry (LiveDispatch.replay reachedBody (observes.installs reachedBody)), ?_⟩
  · simpa only [List.append_nil, List.append_assoc] using between.runs.1.append (.next entry (.next body (.stop _)))
  · have silentEntry := entryVisible entry
    have silentInstall := silentVisible silent
    simp only [PayloadPrefix.visible, List.filter_append] at silentEntry silentInstall visible ⊢
    rw [silentEntry, silentInstall, visible]

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

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveGive
