module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {initial committed parked : Config (core3 grow) (HostState sig)} {subtask : SubtaskId} {index : Nat}

theorem Retaining.reaches {labels}
    (path : Retaining profile ready (specDispatch ready impl) subtask index committed labels parked)
    (pending : PendingAt committed.store subtask index) :
    Steps profile ready (specDispatch ready impl) committed labels parked ∧ PendingAt parked.store subtask index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.retainingPath path pending

theorem Retaining.of_subtasks {E : CoreEngine} {Host : Type} {hr : HostReady Host} {dispatch : Call E → P E Host (Ret E)}
    {state reached : Config E Host} {label} (run : Step profile hr dispatch state label reached)
    (same : reached.store.subtasks = state.store.subtasks) : Retaining profile hr dispatch subtask index state [label] reached :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.stepOfSubtasks run same

theorem Retaining.join {E : CoreEngine} {Host : Type} {hr : HostReady Host} {dispatch : Call E → P E Host (Ret E)}
    {state : Config E Host} {thread segments rest}
    (waitable : Waitable) (set : Option WsetId) (next : P E Host (Ret E))
    (focused : state.ctl = ⟨thread, .prog (Waitable.join waitable set >>= fun () => next), segments⟩ :: rest) :
    Retaining profile hr dispatch subtask index state [.tau]
      { state with store := state.store.joinSt waitable set, ctl := ⟨thread, .prog next, segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.joinStep waitable set next focused

theorem LinkedResolution.indexed_steps (resolve : LinkedResolution initial subtask index) :
    Steps profile ready (specDispatch ready impl) initial (List.replicate 17 .tau) resolve.committed ∧
      PendingAt resolve.committed.store subtask index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resolutionIndexed resolve

/-- Between result commit and a selected parked poll, the reached prefix
must retain the pending event. Poll buffer traps still occur after removal
and lend release, not before commit or as a rollback. -/
theorem LinkedResolution.then_poll (resolve : LinkedResolution initial subtask index) {between}
    (path : Retaining profile ready (specDispatch ready impl) subtask index resolve.committed between parked)
    (poll : ParkedPoll parked subtask profile) :
    poll.steps index ready impl initial (List.replicate 17 .tau ++ between) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resolutionPoll resolve path poll

theorem ParkedPoll.delivered_clears (poll : ParkedPoll parked subtask profile) (pending : PendingAt parked.store subtask index) :
    ∃ record, poll.delivered.subtask? subtask = some record ∧ record.common.pending = none ∧
      record.lenders = none ∧ record.state = .returned ∧ record.index = some index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.deliveredClears poll pending

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery
