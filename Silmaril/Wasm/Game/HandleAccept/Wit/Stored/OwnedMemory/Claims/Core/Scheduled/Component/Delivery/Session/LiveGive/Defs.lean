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

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
