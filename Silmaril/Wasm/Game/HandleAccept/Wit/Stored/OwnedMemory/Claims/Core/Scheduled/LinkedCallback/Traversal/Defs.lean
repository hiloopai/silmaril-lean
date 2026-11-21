module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.CollectionVisit.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine ReturnFrame.Occurrence PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

/-- Two reached paths with the same visible labels. Each carries every
enclosing active slot, even through temporary pushes or suspension, and
the exact classified callback segments traversed on the way. -/
def TrackedAdvance (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (left right reached reference : State grow sig) : Prop :=
  let dispatch := specDispatch ready (host bindings)
  ∃ checkLabels canonLabels, visible checkLabels = visible canonLabels ∧
    RetainsActiveSlots profile ready dispatch left checkLabels reached ∧
    RetainsActiveSlots profile ready dispatch right canonLabels reference ∧
    ReplayTrace profile ready bindings left checkLabels reached right canonLabels reference

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
