module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveGive.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveGive

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {route : GiveEffectRoute}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {start : State grow sig}
  {bindings : List (Binding sig)} {callees : List (Callee sig)}

/-- Compose the reached delivery interleaving, live public give entry and a
compared body prefix into actual checked and canonical runs. The phase and
canonical residual stay distinct: a typed guard stop does not emit a reference
reply, and a finite parked allocator is not required to resume. -/
theorem JournalInterleaving.live_give (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
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
      PayloadPrefix.visible (leading ++ entryLabels ++ checkLabels) = PayloadPrefix.visible (leading ++ installed ++ canonLabels) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveGive.episode
    site linked between roots entry body canonical visible observes

/-- A selected stop keeps the actual reached store on both paths. A trap
keeps its canonical trap label; a guard stop leaves the canonical program at
the corresponding prefix and does not synthesize a reference refusal. -/
theorem JournalInterleaving.live_stopped_give (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
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
      reached.store = (HostFrame.replace reference after).store :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveGive.stopped
    site linked between roots entry stop sameStore seen checked canonical agreement observes

/-- Continue a session from an actual recursive body comparison and caller
rejoin. The continuation receives the reached canonical replay, rather than
starting with the journal from the original site. -/
theorem LiveSession.of_rejoined (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
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
      ((actions ++ [.give route .entered, .give route .returned]) ++ tailActions) finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveGive.ofRejoined
    site linked between roots entry value comparison agreement observes tail

/-- A finite allocator cut ends at the paired reached store, even if the
allocator frame remains parked. In particular it is not a give return. -/
theorem LiveSession.of_allocator (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
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
      reached :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveGive.ofAllocator
    site linked between roots entry cut checkEntry canonEntry seenEntry checkInstall canonInstall checked canonical observes

/-- Execute each classified episode under a single live reference dispatcher.
Only actual returns rejoin the caller and continue; a terminal cut retains
the reached store and visible labels without forcing a canonical reply. -/
theorem LiveSession.runs {incoming actions finish}
    (session : LiveSession profile ready bindings callees start incoming actions finish) :
    ∃ checkLabels canonLabels reference,
      Run profile ready (hostWithComponent bindings callees) start actions checkLabels finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (hostWithComponent bindings callees)))
        (HostFrame.replace start incoming) canonLabels reference ∧
      PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧ finish.store = reference.store :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveGive.sessionRuns session

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
