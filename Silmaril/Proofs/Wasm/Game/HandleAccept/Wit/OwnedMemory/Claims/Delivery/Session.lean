module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Callback.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall.Delivery ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start middle finish : State grow sig}

theorem transitionSteps {action leading} (edge : Transition profile ready impl start action leading finish) :
    Steps profile ready (specDispatch ready impl) start leading finish := by
  cases edge with
  | invoke hostReady fresh => exact .cons (.hostInvoke hostReady fresh) (.refl _)
  | tick tick => exact tick.selects_thread
  | coreInternal focused running step => exact .cons (.coreInternal focused running step) (.refl _)
  | coreReturned focused returned => exact .cons (.coreReturned focused returned) (.refl _)
  | coreTrap focused trapped => exact .cons (.coreTrap focused trapped) (.refl _)
  | commit resolve => exact (resolve.indexed_steps (profile := profile) (ready := ready) (impl := impl)).1
  | poll poll pending branch =>
    have outcomes := poll.delivers_returned (ready := ready) (impl := impl) pending
    cases branch with
    | unaligned bad => exact outcomes.1 bad
    | outside aligned sized bad => exact (outcomes.2 _ aligned sized).2 bad
    | inside aligned sized fits => exact (outcomes.2 _ aligned sized).1 fits
  | waitBlock wait empty => exact wait.blocks empty
  | waitReady wait available early allowed => exact wait.ready_choice available early allowed
  | waitResume resume saved => exact resume.resumes saved
  | waitTake delivery focused pending branch =>
    have outcomes := delivery.at_selection (ready := ready) (impl := impl) focused pending
    cases branch with
    | unaligned bad => exact outcomes.1 bad
    | outside aligned sized bad => exact (outcomes.2 _ aligned sized).2 bad
    | inside aligned sized fits => exact (outcomes.2 _ aligned sized).1 fits
  | cancelReturned cancel pending available => exact cancel.delivers_returned pending available
  | cancelReply cancel record focused live cancelled pending =>
    exact cancel.finish_cancelled_callback _ record focused live cancelled pending
  | callbackPark wait availability => exact wait.parks availability
  | callbackResume resume saved => exact resume.resumes saved
  | callbackTake wait kind focused live noCancel setLive allowed selects tracked resolved pending chosen =>
    exact (wait.wait_takes_resolution (ready := ready) (impl := impl) kind focused live noCancel setLive allowed
      selects tracked resolved pending chosen).1
  | callbackResolveCancel entry empty resolution started indexed =>
    exact (entry.resolves_started (profile := profile) (ready := ready) (impl := impl) empty resolution started indexed).1
  | callbackBorrowTrap entry borrows =>
    exact (entry.enters_resolution (profile := profile) (ready := ready) (impl := impl)).2 borrows
  | callbackExit exit => exact (exit.unwinds (profile := profile) (ready := ready) (impl := impl)).1
  | closedCallback path => exact path.reaches.1

private theorem appendSteps {leading trailing}
    (left : Steps profile ready (specDispatch ready impl) start leading middle)
    (right : Steps profile ready (specDispatch ready impl) middle trailing finish) :
    Steps profile ready (specDispatch ready impl) start (leading ++ trailing) finish := by
  induction left with
  | refl => exact right
  | cons step _ ih => exact .cons step (ih right)

theorem runSteps {actions labels} (path : Run profile ready impl start actions labels finish) :
    Steps profile ready (specDispatch ready impl) start labels finish := by
  induction path with
  | stop => exact .refl _
  | next edge _ ih => exact appendSteps (transitionSteps edge) ih

theorem runAppend {first second leading trailing} (left : Run profile ready impl start first leading middle)
    (right : Run profile ready impl middle second trailing finish) :
    Run profile ready impl start (first ++ second) (leading ++ trailing) finish := by
  induction left with
  | stop => exact right
  | next edge _ ih => simpa only [List.cons_append, List.append_assoc] using Run.next edge (ih right)

theorem closedRecord {target labels} (edge : Transition profile ready impl start (.closedCallback target) labels finish) :
    finish.store.subtask? target = start.store.subtask? target := by
  cases edge with
  | closedCallback path => exact path.reaches.2

theorem takenRecord {target event labels}
    (edge : Transition profile ready impl start (.callbackTake target event) labels finish) :
    ∃ record, start.store.subtask? target = some record ∧
      finish.store.subtask? target = some { record with common := { record.common with pending := none }, lenders := none } := by
  cases edge with
  | callbackTake wait kind focused live noCancel setLive allowed selects tracked resolved pending chosen =>
    exact ⟨_, tracked, (wait.wait_takes_resolution (ready := ready) (impl := impl) kind focused live noCancel setLive allowed
      selects tracked resolved pending chosen).2⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession
