module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

/-- The open observations at a selected canonical body prefix. This compares
only reached host reads and dispatcher installs, not bytes, live claims, events,
or whether the body eventually returns. A nested public request delimits this
segment; it must be entered with the live dispatcher rather than replayed. -/
structure GivePrefixObservations (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (Callee sig))
    (body : State grow sig) (incoming : HostState sig) (labels : Trace grow sig) (finish : State grow sig) : Prop where
  reads : ReachedReadsAgree (profile := profile) (ready := ready) (Dispatch.linked ready bindings callees)
    body incoming labels finish
  installs : ∀ {outgoing}, Steps profile ready (Dispatch.linked ready bindings callees)
    (HostFrame.replace body incoming) labels (HostFrame.replace finish outgoing) →
      LiveDispatch.UnchangedThrough bindings profile ready (hostWithComponent bindings callees)
        (HostFrame.replace body incoming) labels (HostFrame.replace finish outgoing)

/-- A finite classified session of live public gives. A returning give
continues from the rejoined caller and the journal reached by replay. A
terminal cut need not return, for example at an allocator or a guard stop. -/
inductive LiveSession (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (Callee sig)) :
    State grow sig → HostState sig → List Action → State grow sig → Prop where
  | interleaving {start incoming actions labels finish outgoing}
      (path : JournalInterleaving profile ready (hostWithComponent bindings callees)
        start incoming actions labels finish outgoing) :
      LiveSession profile ready bindings callees start incoming actions finish
  | returned {route} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      {start incoming actions leading outgoing entryLabels checkLabels canonLabels left right reached reference finish tailActions}
      (between : JournalInterleaving profile ready (hostWithComponent bindings callees)
        start incoming actions leading site.start outgoing)
      (roots : incoming.writer.accepted = start.host.writer.accepted)
      (entry : Transition profile ready (hostWithComponent bindings callees) site.start (.give route .entered)
        entryLabels site.checked)
      (value : route.output.Result)
      (checked : Dispatch.Compatible profile ready bindings callees site.checked checkLabels reached)
      (canonical : Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonLabels reference)
      (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference left right)
      (visible : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
      (observes : GivePrefixObservations profile ready bindings callees (site.reference site.referenceReply)
        outgoing (canonLabels ++ [.tau]) right)
      (tail : ∀ {after}, Steps profile ready (Dispatch.linked ready bindings callees)
        (HostFrame.replace (site.reference site.referenceReply) outgoing) (canonLabels ++ [.tau]) (HostFrame.replace right after) →
        LiveSession profile ready bindings callees left after tailActions finish) :
      LiveSession profile ready bindings callees start incoming
        ((actions ++ [.give route .entered, .give route .returned]) ++ tailActions) finish
  | cut {route} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      {start incoming actions leading outgoing entryLabels checkLabels canonLabels phase reached reference}
      (between : JournalInterleaving profile ready (hostWithComponent bindings callees)
        start incoming actions leading site.start outgoing)
      (roots : incoming.writer.accepted = start.host.writer.accepted)
      (entry : Transition profile ready (hostWithComponent bindings callees) site.start (.give route .entered)
        entryLabels site.checked)
      (body : Transition profile ready (hostWithComponent bindings callees) site.checked (.give route phase)
        checkLabels reached)
      (canonical : Steps profile ready (Dispatch.linked ready bindings callees) (site.reference site.referenceReply)
        canonLabels reference)
      (store : reached.store = reference.store)
      (visible : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
      (observes : GivePrefixObservations profile ready bindings callees (site.reference site.referenceReply)
        outgoing canonLabels reference) :
      LiveSession profile ready bindings callees start incoming (actions ++ [.give route .entered, .give route phase]) reached

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
