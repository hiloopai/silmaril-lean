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

/-- Only reached waiting threads whose ready condition queries the host
can distinguish the two journals at a scheduler tick. -/
def TickReadsAgree (ready : HostReady (HostState sig)) (start : State grow sig) (other : HostState sig) : Prop :=
  let entered := StepDefs.enterHostSt start.store
  ∀ thread ∈ entered.waiting, ∀ entry, entered.thread? thread = some entry → entry.blocked = true →
    ∀ query, entry.readyCond = some (.host query) → ready start.host query = ready other query

open ComponentCall.Delivery (LinkedResolution)

/-- These actions execute in both sessions with reached stores and separate
journals. A commit installs its current event; a delivery can consume it
or a different live event. A tick uses the actual sampled readiness queries. -/
inductive JournalInterleaving (profile : ProfileKind) (ready : HostReady (HostState sig))
    (impl : HostImpl (core3 grow) (HostState sig)) :
    State grow sig → HostState sig → List Action → Trace grow sig → State grow sig → HostState sig → Prop where
  | stop (state : State grow sig) (other : HostState sig) : JournalInterleaving profile ready impl state other [] [] state other
  | neutral {start other action leading middle actions trailing finish outgoing}
      (edge : Transition profile ready impl start action leading middle) (closed : JournalNeutralAction action)
      (tail : JournalInterleaving profile ready impl middle other actions trailing finish outgoing) :
      JournalInterleaving profile ready impl start other (action :: actions) (leading ++ trailing) finish outgoing
  | commit {start other target index actions trailing finish outgoing}
      (resolve : LinkedResolution start target index) {writer : OwnedMemory.Claims.State sig}
      (registered : other.writer.register resolve.tree = .ok writer)
      (sameHandle : writer.accepted.length = resolve.writer.accepted.length)
      (tail : JournalInterleaving profile ready impl resolve.committed
        ((({ other with writer } : HostState sig).record (.published resolve.ticket writer.accepted.length)).record
          (.returned resolve.ticket writer.accepted.length)) actions trailing finish outgoing) :
      JournalInterleaving profile ready impl start other (.commit target index :: actions)
        (List.replicate 17 .tau ++ trailing) finish outgoing
  | tick {start other thread actions trailing finish outgoing}
      (tick : ComponentCall.Delivery.SelectedTick thread start ready profile) (agrees : TickReadsAgree ready start other)
      (tail : JournalInterleaving profile ready impl tick.atResume other actions trailing finish outgoing) :
      JournalInterleaving profile ready impl start other (.tick thread :: actions) (tick.selectionLabels ++ trailing) finish outgoing

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
