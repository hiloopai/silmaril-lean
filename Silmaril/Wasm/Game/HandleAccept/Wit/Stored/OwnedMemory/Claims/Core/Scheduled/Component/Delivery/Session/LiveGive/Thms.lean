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

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
