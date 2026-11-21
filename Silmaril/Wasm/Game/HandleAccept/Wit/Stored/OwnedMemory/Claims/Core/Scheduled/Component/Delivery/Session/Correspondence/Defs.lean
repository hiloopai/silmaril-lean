module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine

/-- These classified edges use only the reached machine state, not the
acceptor journal. `ClosedDeliveryAction` instead compares dispatcher
overlays at an identical state. -/
def JournalNeutralAction : Action → Prop
  | .coreStep | .coreReturn | .coreTrap | .coreReply .. | .poll .. | .wait .. | .waitEnter .. | .waitResume ..
  | .cancel .. | .cancelPark .. | .cancelResume .. => True
  | _ => False

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}
  {profile : ProfileKind} {ready : HostReady (HostState sig)}

/-- Replay from the journal reached by the canonical side. A differing
host read is an executed boundary, not a trap or an erased callback. -/
inductive JournalReplay (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (start : State grow sig) (incoming : HostState sig) (labels : Trace grow sig) (finish : State grow sig) : Prop where
  | complete {outgoing : HostState sig}
      (run : Steps profile ready dispatch (HostFrame.replace start incoming) labels (HostFrame.replace finish outgoing))
  | read {leading label trailing reached reachedHost next alternate}
      (split : labels = leading ++ label :: trailing)
      (baseline : Steps profile ready dispatch start leading reached)
      (replayed : Steps profile ready dispatch (HostFrame.replace start incoming) leading (HostFrame.replace reached reachedHost))
      (read : HostFrame.ReadCut reached reachedHost label next alternate)
      (baselineRead : Step profile ready dispatch reached label next)
      (replayedRead : Step profile ready dispatch (HostFrame.replace reached reachedHost) label alternate)
      (tail : Steps profile ready dispatch next trailing finish)

/-- Only the residual program of a reached read must agree, after whatever
host writes the preceding steps performed on either side. -/
def ReachedReadsAgree (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (start : State grow sig) (incoming : HostState sig) (labels : Trace grow sig) (finish : State grow sig) : Prop :=
  ∀ {leading label trailing reached reachedHost next}, labels = leading ++ label :: trailing →
    Steps profile ready dispatch start leading reached →
    Steps profile ready dispatch (HostFrame.replace start incoming) leading (HostFrame.replace reached reachedHost) →
    Step profile ready dispatch reached label next → Steps profile ready dispatch next trailing finish →
    ∀ {thread read frames rest}, reached.ctl = ⟨thread, .prog (.op .hostGet read), frames⟩ :: rest →
      read reached.host = read reachedHost

/-- A closed canonical prefix in the journal sense has no reached host
read. Host writes, realloc and ordinary store effects are not excluded. -/
def ReadFreeThrough (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (start : State grow sig) (labels : Trace grow sig) (finish : State grow sig) : Prop :=
  ∀ {leading label trailing reached}, labels = leading ++ label :: trailing →
    Steps profile ready dispatch start leading reached → Steps profile ready dispatch reached (label :: trailing) finish →
    ∀ {thread read frames rest}, reached.ctl ≠ ⟨thread, .prog (.op .hostGet read), frames⟩ :: rest

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
