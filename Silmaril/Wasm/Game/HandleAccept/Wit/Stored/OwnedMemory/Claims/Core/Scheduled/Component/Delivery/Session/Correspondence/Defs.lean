module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession

/-- These classified edges use only the reached machine state, not the
acceptor journal. `ClosedDeliveryAction` instead compares dispatcher
overlays at an identical state. -/
def JournalNeutralAction : Action → Prop
  | .coreStep | .coreReturn | .coreTrap | .poll .. | .wait .. | .waitEnter .. | .waitResume ..
  | .cancel .. | .cancelPark .. | .cancelResume .. => True
  | _ => False

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
