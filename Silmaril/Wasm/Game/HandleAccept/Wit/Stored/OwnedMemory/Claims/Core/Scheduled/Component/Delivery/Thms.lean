module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

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

/-- With no event available, the wait registers the actual ready condition and parks the
Core continuation. It neither returns to Core nor consumes an event. -/
theorem ParkedWait.blocks (wait : ParkedWait initial) (empty : initial.store.wsetHasEvent wait.ws = false) :
    Steps profile ready (specDispatch ready impl) initial (List.replicate 13 .tau) wait.blocked :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.parkedWaitBlocks wait empty

/-- On the selected tick, resume the saved wait and reach selection in the current store.
This does not assume that the scheduler will ever select that waiter. -/
theorem WaitTick.resumes {atHost : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
    (tick : WaitTick wait atHost ready profile) (saved : atHost.cont? wait.thread = some wait.saved) :
    Steps profile ready (specDispatch ready impl) atHost tick.labels tick.reached :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resumeWaitTick tick saved

/-- A resolution can feed a previously blocked Core wait on the selected tick.
The actual buffer check follows consumption; a trap retains the earlier effects. -/
theorem LinkedResolution.then_wait {atHost : Config (core3 grow) (HostState sig)} {wait : ParkedWait parked}
    {tick : WaitTick wait atHost ready profile} (delivery : WaitDelivery tick subtask)
    (resolve : LinkedResolution initial subtask index) {between}
    (path : Retaining profile ready (specDispatch ready impl) subtask index resolve.committed between atHost)
    (saved : atHost.cont? wait.thread = some wait.saved) :
    delivery.outcomes index impl initial ((List.replicate 17 .tau ++ between) ++ tick.labels) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resolutionWait delivery resolve path saved

/-- Compose the actual block, reached resolution and selected wakeup. The
same saved activation is derived from the actual edits, not a final lookup. -/
theorem ParkedWait.then_resolution {atHost resolving : Config (core3 grow) (HostState sig)} {wait : ParkedWait initial}
    {tick : WaitTick wait atHost ready profile} (delivery : WaitDelivery tick subtask)
    (empty : initial.store.wsetHasEvent wait.ws = false) {whileBlocked between}
    (runs : ParkedPrefix profile ready (specDispatch ready impl) wait.thread wait.blocked whileBlocked resolving)
    (resolve : LinkedResolution resolving subtask index)
    (path : ParkedRetaining profile ready (specDispatch ready impl) wait.thread subtask index resolve.committed between atHost) :
    delivery.outcomes index impl initial
      ((((List.replicate 13 .tau ++ whileBlocked) ++ List.replicate 17 .tau) ++ between) ++ tick.labels) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.blockedResolutionWait delivery empty runs resolve path

/-- On an already resolved subtask, cancel consumes the returned event and
reports its existing state. It does not run the cancellation callback. -/
theorem ParkedCancel.delivers_returned (cancel : ParkedCancel parked subtask) (pending : PendingAt parked.store subtask index)
    (available : CancelAvailable parked.store subtask) :
    Steps profile ready (specDispatch ready impl) parked (List.replicate 15 .tau) cancel.resumed :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.cancelReturned cancel pending available

theorem ParkedCancel.delivered_clears (cancel : ParkedCancel parked subtask) (pending : PendingAt parked.store subtask index) :
    ∃ record, cancel.resumed.store.subtask? subtask = some record ∧ record.common.pending = none ∧
      record.lenders = none ∧ record.state = .returned ∧ record.index = some index :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.cancelClears cancel pending

/-- After committing a result, a cancel callout on the same live subtask can
deliver the result without a poll or event buffer. The publication is retained. -/
theorem LinkedResolution.then_cancel (resolve : LinkedResolution initial subtask index) {between}
    (path : Retaining profile ready (specDispatch ready impl) subtask index resolve.committed between parked)
    (cancel : ParkedCancel parked subtask) (available : CancelAvailable parked.store subtask) :
    Steps profile ready (specDispatch ready impl) initial ((List.replicate 17 .tau ++ between) ++ List.replicate 15 .tau)
      cancel.resumed :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.resolutionCancel resolve path cancel available

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery
