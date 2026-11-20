module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.AsyncRef
open OwnedMemory (Tree)
open OwnedMemory.Claims (State)
open Stored.Endpoints.RecordLower

/-- A return event belongs to the canonical subtask arena object, not to the
numeric handle or waitable set through which a guest might poll it. -/
def PendingAt {E : CoreEngine} (store : CStore E) (subtask : SubtaskId) (index : Nat) : Prop :=
  ∃ record, store.subtask? subtask = some record ∧ record.state = .returned ∧ record.index = some index ∧
    record.common.pending = some (.subtask subtask)

/-- Classify the actual intervening steps. If a cut loses the pending
observation, a final matching lookup cannot certify this prefix. -/
inductive Retaining {E : CoreEngine} {Host : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (subtask : SubtaskId) (index : Nat) :
    Config E Host → List (Label E Host) → Config E Host → Prop where
  | done (state : Config E Host) : Retaining profile ready dispatch subtask index state [] state
  | step {start next reached labels label} (run : Step profile ready dispatch start label next)
      (kept : PendingAt start.store subtask index → PendingAt next.store subtask index)
      (tail : Retaining profile ready dispatch subtask index next labels reached) :
      Retaining profile ready dispatch subtask index start (label :: labels) reached

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

structure LinkedResolution (cfg : Config (core3 grow) (HostState sig)) (subtask : SubtaskId) (index : Nat) where
  callee : Callee sig
  ticket : Nat
  caller : CallerId
  tree : Tree sig
  writer : State sig
  record : Subtask
  context : LiftLowerContext (core3 grow)
  args : List FlatValue
  position : Nat
  pointer : FlatValue
  bytes : Nat
  thread : Option ThreadId
  segments : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  callerRecord : ArenaField.callers.get? cfg.store caller = some
    (.lower subtask context args position callee.funcType (lowerLimits callee.async_).1 (lowerLimits callee.async_).2)
  live : cfg.store.subtask? subtask = some record
  indexed : record.index = some index
  options : context.opts = callee.options
  atCursor : args[position]? = some pointer
  aligned : flatNat pointer = ABI.alignTo (flatNat pointer) .four
  sized : (core3 grow).memSize? cfg.store.core callee.memory = some bytes
  inBounds : flatNat pointer + 8 ≤ bytes
  registered : cfg.host.writer.register tree = .ok writer
  room : writer.accepted.length < 2 ^ 32
  focused : cfg.ctl = ⟨thread, .prog (resolveTree ticket caller tree), segments⟩ :: rest

def LinkedResolution.committed {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId} {index : Nat}
    (resolve : LinkedResolution cfg subtask index) : Config (core3 grow) (HostState sig) :=
  let handle := resolve.writer.accepted.length
  let out := flatNat resolve.pointer
  let queued := cfg.store.setPendingSt (.subtask subtask) (.subtask subtask)
  let tagged := writeMemSt resolve.callee.memory out (intToLE 1 0) queued
  let written := writeMemSt resolve.callee.memory (out + 4) (intToLE 4 handle) tagged
  { cfg with
    store := written.subtaskResolveSt subtask .returned []
    host := (({ cfg.host with writer := resolve.writer } : HostState sig).record (.published resolve.ticket handle)).record
      (.returned resolve.ticket handle)
    ctl := ⟨resolve.thread, .prog (.pure (.cancel .none)), resolve.segments⟩ :: resolve.rest }

/-- Reached caller and selection facts, independent of a proof that the
selected subtask still has its original pending returned event. -/
structure ParkedPoll (cfg : Config (core3 grow) (HostState sig)) (subtask : SubtaskId)
    (profile : ProfileKind) where
  memory : Nat
  slot : FlatValue
  out : FlatValue
  ws : WsetId
  thread : ThreadId
  active : Thread
  task : Task (core3 grow)
  instance_ : InstState
  core : (core3 grow).Thread (CanonHost (core3 grow))
  next : List FlatValue → Session grow sig (Ret (core3 grow))
  segments : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  set : WaitableSet
  perm : List Nat
  focused : cfg.ctl = ⟨some thread, .core core next, segments⟩ :: rest
  callout : (core3 grow).status cfg.store.core core =
    .callout (.builtin (.waitableSetPoll memory) task.inst) [slot, out]
  liveThread : ArenaField.threads.get? cfg.store thread = some active
  liveTask : ArenaField.tasks.get? cfg.store active.task = some task
  liveInst : ArenaField.insts.get? cfg.store task.inst = some instance_
  mayLeave : instance_.mayLeave = true
  handle : instance_.handles.get? (flatNat slot) = some (.wset ws)
  setLive : cfg.store.wset? ws = some set
  member : .subtask subtask ∈ set.elems
  allowed : Allowed profile (.shuffle set.elems.length) perm
  selects : (applyPerm perm set.elems).find?
    (cfg.store.wsetSetElemsSt ws (applyPerm perm set.elems)).waitableHasEvent = some (.subtask subtask)

def ParkedPoll.delivered {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId} {profile : ProfileKind}
    (poll : ParkedPoll cfg subtask profile) : CStore (core3 grow) :=
  let shuffled := cfg.store.wsetSetElemsSt poll.ws (applyPerm poll.perm poll.set.elems)
  (shuffled.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none }).deliverResolveSt subtask

def ParkedPoll.steps {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId} {profile : ProfileKind}
    (poll : ParkedPoll cfg subtask profile) (index : Nat) (ready : HostReady (HostState sig))
    (impl : HostImpl (core3 grow) (HostState sig)) (initial : Config (core3 grow) (HostState sig))
    (leading : List (Label (core3 grow) (HostState sig))) : Prop :=
  let ptr := flatNat poll.out
  let delivered := poll.delivered
  let written := writeMemSt poll.memory (ptr + 4) (u32Bytes SubtaskState.returned.toNat)
    (writeMemSt poll.memory ptr (u32Bytes index) delivered)
  let labels := leading ++ (List.replicate 10 .tau ++ [.choice (.shuffle poll.set.elems.length) poll.perm] ++ List.replicate 4 .tau)
  let trapped := { cfg with store := StepDefs.lockdownSt delivered, ctl := [] }
  let resumed := { cfg with store := written, ctl := ⟨some poll.thread,
    .core ((core3 grow).resume written.core poll.core (.values [i32Flat EventCode.subtask.toNat])) poll.next,
    poll.segments⟩ :: poll.rest }
  let dispatch := specDispatch ready impl
  (ptr % 4 ≠ 0 → Steps profile ready dispatch initial (labels ++ [.trap .unalignedPointer]) trapped) ∧
  (∀ size, ptr % 4 = 0 → (core3 grow).memSize? cfg.store.core poll.memory = some size →
    (ptr + 8 ≤ size → Steps profile ready dispatch initial (labels ++ List.replicate 6 .tau) resumed) ∧
    (size < ptr + 8 → Steps profile ready dispatch initial (labels ++ [.tau, .trap .outOfBounds]) trapped))

/-- Admission of a Core wait callout, before the scheduler knows whether it
can return. In particular this carries no pending-event selection. -/
structure ParkedWait (cfg : Config (core3 grow) (HostState sig)) where
  memory : Nat
  slot : FlatValue
  out : FlatValue
  ws : WsetId
  thread : ThreadId
  active : Thread
  task : Task (core3 grow)
  instance_ : InstState
  core : (core3 grow).Thread (CanonHost (core3 grow))
  next : List FlatValue → Session grow sig (Ret (core3 grow))
  segments : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  focused : cfg.ctl = ⟨some thread, .core core next, segments⟩ :: rest
  callout : (core3 grow).status cfg.store.core core =
    .callout (.builtin (.waitableSetWait memory) task.inst) [slot, out]
  liveThread : ArenaField.threads.get? cfg.store thread = some active
  liveTask : ArenaField.tasks.get? cfg.store active.task = some task
  liveInst : ArenaField.insts.get? cfg.store task.inst = some instance_
  mayLeave : instance_.mayLeave = true
  handle : instance_.handles.get? (flatNat slot) = some (.wset ws)

def ParkedWait.takeEvent {cfg : Config (core3 grow) (HostState sig)} (wait : ParkedWait cfg) :
    Session grow sig (Ret (core3 grow)) := do
  let event ← wsetGetPendingEvent wait.ws
  let code ← unpackEvent (Builtins.eventCx wait.memory wait.task.inst) (flatNat wait.out) event
  pure (.flat [i32Flat code])

def ParkedWait.saved {cfg : Config (core3 grow) (HostState sig)} (wait : ParkedWait cfg) :
    Activation (core3 grow) (HostState sig) :=
  ⟨some wait.thread, .prog (modifyStore (CStore.wsetDecWaitingSt wait.ws) >>= fun () => wait.takeEvent),
    .core wait.core wait.next :: wait.segments⟩

def ParkedWait.blocked {cfg : Config (core3 grow) (HostState sig)} (wait : ParkedWait cfg) :
    Config (core3 grow) (HostState sig) :=
  { (cfg.setCont wait.thread (some wait.saved)) with
    store := StepDefs.threadStatusSt wait.thread .blocked
      ((cfg.store.wsetIncWaitingSt wait.ws).startWaitingSt wait.thread (.wsetHasEvent wait.ws))
    ctl := wait.rest }

/-- The host is allowed to tick, the actual saved activation still occupies
its slot, and the scheduler chooses it from the current ready candidates. -/
structure WaitTick {cfg : Config (core3 grow) (HostState sig)} (wait : ParkedWait cfg)
    (atHost : Config (core3 grow) (HostState sig)) (ready : HostReady (HostState sig)) (profile : ProfileKind) where
  hostReady : StepDefs.HostReadyCfg atHost
  saved : atHost.cont? wait.thread = some wait.saved
  first : ThreadId
  others : List ThreadId
  candidates : (StepDefs.enterHostSt atHost.store).candidates (ready atHost.host) = first :: others
  pick : Fin (others.length + 1)
  allowed : Allowed profile (.tickPick others.length) pick
  selected : (first :: others)[pick.val]'(by simpa only [List.length_cons] using pick.isLt) = wait.thread

def WaitTick.reached {cfg atHost : Config (core3 grow) (HostState sig)} {wait : ParkedWait cfg}
    {ready : HostReady (HostState sig)} {profile : ProfileKind} (_tick : WaitTick wait atHost ready profile) :
    Config (core3 grow) (HostState sig) :=
  { (atHost.setCont wait.thread none) with
    store := (StepDefs.threadStatusSt wait.thread .running
      ((StepDefs.enterHostSt atHost.store).stopWaitingSt wait.thread)).wsetDecWaitingSt wait.ws
    ctl := ⟨some wait.thread, .prog wait.takeEvent, .core wait.core wait.next :: wait.segments⟩ ::
      [Activation.ofProg none (modifyStore StepDefs.leaveHostSt >>= fun () => pure .unit)] }

def WaitTick.labels {cfg atHost : Config (core3 grow) (HostState sig)} {wait : ParkedWait cfg}
    {ready : HostReady (HostState sig)} {profile : ProfileKind} (tick : WaitTick wait atHost ready profile) :
    List (Label (core3 grow) (HostState sig)) :=
  [.host .tick, .tau, .tau, .tau, .choice (.tickPick tick.others.length) tick.pick] ++ List.replicate 4 .tau

/-- The shuffle and selection are read after the tick restores the waiter,
not at the initial callout or at publication. -/
structure WaitDelivery {cfg atHost : Config (core3 grow) (HostState sig)} {wait : ParkedWait cfg}
    {ready : HostReady (HostState sig)} {profile : ProfileKind} (tick : WaitTick wait atHost ready profile)
    (subtask : SubtaskId) where
  set : WaitableSet
  perm : List Nat
  setLive : tick.reached.store.wset? wait.ws = some set
  allowed : Allowed profile (.shuffle set.elems.length) perm
  selects : (applyPerm perm set.elems).find?
    (tick.reached.store.wsetSetElemsSt wait.ws (applyPerm perm set.elems)).waitableHasEvent = some (.subtask subtask)

section WaitDelivery

variable {cfg atHost : Config (core3 grow) (HostState sig)} {wait : ParkedWait cfg}
  {ready : HostReady (HostState sig)} {profile : ProfileKind} {tick : WaitTick wait atHost ready profile} {subtask : SubtaskId}

def WaitDelivery.delivered (delivery : WaitDelivery tick subtask) : CStore (core3 grow) :=
  let shuffled := tick.reached.store.wsetSetElemsSt wait.ws (applyPerm delivery.perm delivery.set.elems)
  (shuffled.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none }).deliverResolveSt subtask

def WaitDelivery.labels (delivery : WaitDelivery tick subtask) : List (Label (core3 grow) (HostState sig)) :=
  [.tau, .choice (.shuffle delivery.set.elems.length) delivery.perm, .tau, .tau, .tau, .tau]

def WaitDelivery.resumed (delivery : WaitDelivery tick subtask) (index : Nat) : Config (core3 grow) (HostState sig) :=
  let ptr := flatNat wait.out
  let written := writeMemSt wait.memory (ptr + 4) (u32Bytes SubtaskState.returned.toNat)
    (writeMemSt wait.memory ptr (u32Bytes index) delivery.delivered)
  { tick.reached with store := written, ctl := ⟨some wait.thread,
    .core ((core3 grow).resume written.core wait.core (.values [i32Flat EventCode.subtask.toNat])) wait.next,
    wait.segments⟩ :: tick.reached.ctl.drop 1 }

def WaitDelivery.outcomes (delivery : WaitDelivery tick subtask) (index : Nat)
    (impl : HostImpl (core3 grow) (HostState sig)) (initial : Config (core3 grow) (HostState sig))
    (prefixLabels : List (Label (core3 grow) (HostState sig))) : Prop :=
  let ptr := flatNat wait.out
  let labels := prefixLabels ++ delivery.labels
  let trapped := { tick.reached with store := StepDefs.lockdownSt delivery.delivered, ctl := [] }
  let dispatch := specDispatch ready impl
  (ptr % 4 ≠ 0 → Steps profile ready dispatch initial (labels ++ [.trap .unalignedPointer]) trapped) ∧
  (∀ size, ptr % 4 = 0 → (core3 grow).memSize? delivery.delivered.core wait.memory = some size →
    (ptr + 8 ≤ size → Steps profile ready dispatch initial (labels ++ List.replicate 6 .tau) (delivery.resumed index)) ∧
    (size < ptr + 8 → Steps profile ready dispatch initial (labels ++ [.tau, .trap .outOfBounds]) trapped))

end WaitDelivery

/-- The Core cancel builtin identifies a live subtask via the caller's handle table. -/
structure ParkedCancel (cfg : Config (core3 grow) (HostState sig)) (subtask : SubtaskId) where
  async_ : Bool
  slot : FlatValue
  thread : ThreadId
  active : Thread
  task : Task (core3 grow)
  instance_ : InstState
  core : (core3 grow).Thread (CanonHost (core3 grow))
  next : List FlatValue → Session grow sig (Ret (core3 grow))
  segments : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  focused : cfg.ctl = ⟨some thread, .core core next, segments⟩ :: rest
  callout : (core3 grow).status cfg.store.core core =
    .callout (.builtin (.subtaskCancel async_) task.inst) [slot]
  liveThread : ArenaField.threads.get? cfg.store thread = some active
  liveTask : ArenaField.tasks.get? cfg.store active.task = some task
  liveInst : ArenaField.insts.get? cfg.store task.inst = some instance_
  mayLeave : instance_.mayLeave = true
  handle : instance_.handles.get? (flatNat slot) = some (.waitable (.subtask subtask))

/-- The returned-event route of cancel is disjoint from cancellation requests:
the event was not already delivered, no request was made, and it is not in a set. -/
def CancelAvailable {E : CoreEngine} (store : CStore E) (subtask : SubtaskId) : Prop :=
  ∃ record, store.subtask? subtask = some record ∧ record.lenders.isSome = true ∧
    record.cancellationRequested = false ∧ record.common.wset = none

def cancelDelivered {E : CoreEngine} (store : CStore E) (subtask : SubtaskId) : CStore E :=
  (store.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none }).deliverResolveSt subtask

def ParkedCancel.resumed {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    (cancel : ParkedCancel cfg subtask) : Config (core3 grow) (HostState sig) :=
  let delivered := cancelDelivered cfg.store subtask
  let result := (subtaskCancelResult (some .returned))
  { cfg with store := delivered, ctl := ⟨some cancel.thread,
    .core ((core3 grow).resume delivered.core cancel.core (.values [i32Flat result])) cancel.next,
    cancel.segments⟩ :: cancel.rest }

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery
