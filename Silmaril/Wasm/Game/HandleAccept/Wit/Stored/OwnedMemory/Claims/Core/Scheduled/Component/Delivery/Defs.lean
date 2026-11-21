module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.AsyncRef
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence
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

/-- Admission of a public Core poll, before inspecting its waitable set. -/
structure PollAdmission (cfg : Config (core3 grow) (HostState sig)) where
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
    .callout (.builtin (.waitableSetPoll memory) task.inst) [slot, out]
  liveThread : ArenaField.threads.get? cfg.store thread = some active
  liveTask : ArenaField.tasks.get? cfg.store active.task = some task
  liveInst : ArenaField.insts.get? cfg.store task.inst = some instance_
  mayLeave : instance_.mayLeave = true
  handle : instance_.handles.get? (flatNat slot) = some (.wset ws)

/-- Reached caller and selection facts, independent of a proof that the
selected subtask still has its original pending returned event. -/
structure ParkedPoll (cfg : Config (core3 grow) (HostState sig)) (subtask : SubtaskId)
    (profile : ProfileKind) extends PollAdmission cfg where
  set : WaitableSet
  perm : List Nat
  setLive : cfg.store.wset? ws = some set
  member : .subtask subtask ∈ set.elems
  allowed : Allowed profile (.shuffle set.elems.length) perm
  selects : (applyPerm perm set.elems).find?
    (cfg.store.wsetSetElemsSt ws (applyPerm perm set.elems)).waitableHasEvent = some (.subtask subtask)

/-- An empty poll or an actual selection of another waitable. The event check is on
the shuffled store, and a different numerical index is not evidence of another waitable. -/
inductive PollRetention {E : CoreEngine} (profile : ProfileKind) (store : CStore E)
    (ws : WsetId) (target : SubtaskId) : Type where
  | empty (noEvent : store.wsetHasEvent ws = false)
  | other (set : WaitableSet) (perm : List Nat) (selected : Waitable) (event : EventTuple)
      (live : store.wset? ws = some set) (hasEvent : store.wsetHasEvent ws = true)
      (allowed : Allowed profile (.shuffle set.elems.length) perm)
      (selects : (applyPerm perm set.elems).find?
        (store.wsetSetElemsSt ws (applyPerm perm set.elems)).waitableHasEvent = some selected)
      (unrelated : selected ≠ .subtask target)
      (take : ((store.wsetSetElemsSt ws (applyPerm perm set.elems)).takeWaitableEvent selected).2 = some event)

def PollRetention.reached {E : CoreEngine} {profile : ProfileKind} {store : CStore E} {ws target} :
    PollRetention profile store ws target → CStore E × EventTuple
  | .empty _ => (store, EventTuple.none)
  | .other set perm selected event .. =>
    ((store.wsetSetElemsSt ws (applyPerm perm set.elems)).takeWaitableEventSt selected, event)

def PollRetention.labels {E : CoreEngine} {Host : Type} {profile : ProfileKind} {store : CStore E} {ws target} :
    PollRetention profile store ws target → List (Label E Host)
  | .empty _ => [.tau]
  | .other set perm .. => [.tau, .tau, .choice (.shuffle set.elems.length) perm, .tau, .tau, .tau, .tau]

def PollAdmission.unpack {cfg : Config (core3 grow) (HostState sig)} (poll : PollAdmission cfg)
    (event : EventTuple) : Session grow sig (Ret (core3 grow)) := do
  let code ← unpackEvent (Builtins.eventCx poll.memory poll.task.inst) (flatNat poll.out) event
  pure (.flat [i32Flat code])

def PollAdmission.beforeUnpack {cfg : Config (core3 grow) (HostState sig)} (poll : PollAdmission cfg)
    (reached : CStore (core3 grow) × EventTuple) : Config (core3 grow) (HostState sig) :=
  { cfg with
    store := reached.1
    ctl := ⟨some poll.thread, .prog (poll.unpack reached.2), .core poll.core poll.next :: poll.segments⟩ :: poll.rest }

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

def ParkedWait.early {cfg : Config (core3 grow) (HostState sig)} (wait : ParkedWait cfg) :
    Config (core3 grow) (HostState sig) :=
  { cfg with
    store := (cfg.store.wsetIncWaitingSt wait.ws).wsetDecWaitingSt wait.ws
    ctl := ⟨some wait.thread, .prog wait.takeEvent, .core wait.core wait.next :: wait.segments⟩ :: wait.rest }

def ParkedWait.readyLabels {E : CoreEngine} {Host : Type} (early : Bool) : List (Label E Host) :=
  List.replicate 11 .tau ++ [.choice (.earlyReturn .waitableSetWait) early] ++
    List.replicate (if early then 1 else 2) .tau

/-- A reached invocation of canonical `Thread.resume`, distinct from the
policy that selected it. The primitive does not consult the readiness predicate. -/
structure WaitResume {cfg : Config (core3 grow) (HostState sig)} (wait : ParkedWait cfg)
    (atResume : Config (core3 grow) (HostState sig)) where
  thread : Option ThreadId
  resumeAfter : Session grow sig (Ret (core3 grow))
  segments : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  focused : atResume.ctl = ⟨thread, .prog (Thread.resume wait.thread >>= fun () => resumeAfter), segments⟩ :: rest
  waiting : atResume.store.threadIs Thread.waiting wait.thread = true

def WaitResume.reached {cfg atResume : Config (core3 grow) (HostState sig)} {wait : ParkedWait cfg}
    (resume : WaitResume wait atResume) : Config (core3 grow) (HostState sig) :=
  { (atResume.setCont wait.thread none) with
    store := (StepDefs.threadStatusSt wait.thread .running (atResume.store.stopWaitingSt wait.thread))
      |>.wsetDecWaitingSt wait.ws
    ctl := ⟨some wait.thread, .prog wait.takeEvent, .core wait.core wait.next :: wait.segments⟩ ::
      ⟨resume.thread, .prog resume.resumeAfter, resume.segments⟩ :: resume.rest }

/-- Admission and selection of a thread from the reached scheduler candidates.
The saved activation in that slot is tracked separately. -/
structure SelectedTick (thread : ThreadId)
    (atHost : Config (core3 grow) (HostState sig)) (ready : HostReady (HostState sig)) (profile : ProfileKind) where
  hostReady : StepDefs.HostReadyCfg atHost
  first : ThreadId
  others : List ThreadId
  candidates : (StepDefs.enterHostSt atHost.store).candidates (ready atHost.host) = first :: others
  pick : Fin (others.length + 1)
  allowed : Allowed profile (.tickPick others.length) pick
  selected : (first :: others)[pick.val]'(by simpa only [List.length_cons] using pick.isLt) = thread

abbrev WaitTick {cfg : Config (core3 grow) (HostState sig)} (wait : ParkedWait cfg) :=
  SelectedTick (grow := grow) (sig := sig) wait.thread

def SelectedTick.atResume {thread : ThreadId} {atHost : Config (core3 grow) (HostState sig)}
    {ready : HostReady (HostState sig)} {profile : ProfileKind} (_tick : SelectedTick thread atHost ready profile) :
    Config (core3 grow) (HostState sig) :=
  { atHost with
    store := StepDefs.enterHostSt atHost.store
    ctl := [Activation.ofProg none (Thread.resume thread >>= fun () =>
      modifyStore StepDefs.leaveHostSt >>= fun () => pure .unit)] }

def SelectedTick.selectionLabels {thread : ThreadId} {atHost : Config (core3 grow) (HostState sig)}
    {ready : HostReady (HostState sig)} {profile : ProfileKind} (tick : SelectedTick thread atHost ready profile) :
    List (Label (core3 grow) (HostState sig)) :=
  [.host .tick, .tau, .tau, .tau, .choice (.tickPick tick.others.length) tick.pick]

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
  tick.selectionLabels ++ List.replicate 4 .tau

/-- Both invariants describe the same intervening execution. Each cut retains
the pending observation and each scheduler edit leaves the saved slot in place. -/
inductive ParkedRetaining {E : CoreEngine} {Host : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (thread : ThreadId) (subtask : SubtaskId) (index : Nat) :
    Config E Host → List (Label E Host) → Config E Host → Prop where
  | done (state : Config E Host) : ParkedRetaining profile ready dispatch thread subtask index state [] state
  | step {start next reached labels label} (run : Step profile ready dispatch start label next)
      (keepsSlot : (transitionEdit start label).follow (.saved thread.idx 0) = some (.saved thread.idx 0))
      (keepsEvent : PendingAt start.store subtask index → PendingAt next.store subtask index)
      (tail : ParkedRetaining profile ready dispatch thread subtask index next labels reached) :
      ParkedRetaining profile ready dispatch thread subtask index start (label :: labels) reached

def PollAdmission.retentionOutcomes {cfg : Config (core3 grow) (HostState sig)} (poll : PollAdmission cfg)
    {profile : ProfileKind} {target : SubtaskId} (selection : PollRetention profile cfg.store poll.ws target)
    (ready : HostReady (HostState sig)) (impl : HostImpl (core3 grow) (HostState sig))
    (saved : ThreadId) (index : Nat) : Prop :=
  let reached := poll.beforeUnpack selection.reached
  let event := selection.reached.2
  let ptr := flatNat poll.out
  let written := writeMemSt poll.memory (ptr + 4) (u32Bytes event.payload)
    (writeMemSt poll.memory ptr (u32Bytes event.index) reached.store)
  let resumed := { reached with
    store := written
    ctl := ⟨some poll.thread,
      .core ((core3 grow).resume written.core poll.core (.values [i32Flat event.code.toNat])) poll.next,
      poll.segments⟩ :: poll.rest }
  let retaining := ParkedRetaining profile ready (specDispatch ready impl) saved target index cfg
  let leading := List.replicate 8 .tau ++ selection.labels
  (ptr % 4 ≠ 0 → retaining (leading ++ [.trap .unalignedPointer]) (StepDefs.trapCfg reached)) ∧
    ∀ size, ptr % 4 = 0 → (core3 grow).memSize? reached.store.core poll.memory = some size →
      (ptr + 8 ≤ size → retaining (leading ++ List.replicate 6 .tau) resumed) ∧
      (size < ptr + 8 → retaining (leading ++ [.tau, .trap .outOfBounds]) (StepDefs.trapCfg reached))

/-- The shuffle and selection are read after the tick restores the waiter,
not at the initial callout or at publication. -/
structure WaitDelivery {cfg : Config (core3 grow) (HostState sig)} (wait : ParkedWait cfg)
    (reached : Config (core3 grow) (HostState sig)) (profile : ProfileKind) (subtask : SubtaskId) where
  set : WaitableSet
  perm : List Nat
  setLive : reached.store.wset? wait.ws = some set
  allowed : Allowed profile (.shuffle set.elems.length) perm
  selects : (applyPerm perm set.elems).find?
    (reached.store.wsetSetElemsSt wait.ws (applyPerm perm set.elems)).waitableHasEvent = some (.subtask subtask)

section WaitDelivery

variable {cfg reached : Config (core3 grow) (HostState sig)} {wait : ParkedWait cfg}
  {profile : ProfileKind} {subtask : SubtaskId}

def WaitDelivery.delivered (delivery : WaitDelivery wait reached profile subtask) : CStore (core3 grow) :=
  let shuffled := reached.store.wsetSetElemsSt wait.ws (applyPerm delivery.perm delivery.set.elems)
  (shuffled.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none }).deliverResolveSt subtask

def WaitDelivery.labels (delivery : WaitDelivery wait reached profile subtask) : List (Label (core3 grow) (HostState sig)) :=
  [.tau, .choice (.shuffle delivery.set.elems.length) delivery.perm, .tau, .tau, .tau, .tau]

def WaitDelivery.resumed (delivery : WaitDelivery wait reached profile subtask) (index : Nat) : Config (core3 grow) (HostState sig) :=
  let ptr := flatNat wait.out
  let written := writeMemSt wait.memory (ptr + 4) (u32Bytes SubtaskState.returned.toNat)
    (writeMemSt wait.memory ptr (u32Bytes index) delivery.delivered)
  { reached with store := written, ctl := ⟨some wait.thread,
    .core ((core3 grow).resume written.core wait.core (.values [i32Flat EventCode.subtask.toNat])) wait.next,
    wait.segments⟩ :: reached.ctl.drop 1 }

def WaitDelivery.outcomes (delivery : WaitDelivery wait reached profile subtask) (index : Nat)
    (ready : HostReady (HostState sig)) (impl : HostImpl (core3 grow) (HostState sig))
    (initial : Config (core3 grow) (HostState sig))
    (prefixLabels : List (Label (core3 grow) (HostState sig))) : Prop :=
  let ptr := flatNat wait.out
  let labels := prefixLabels ++ delivery.labels
  let trapped := { reached with store := StepDefs.lockdownSt delivery.delivered, ctl := [] }
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

def ParkedCancel.result {grow : SingleThreaded.GrowOracle} {sig : Signature} (subtask : SubtaskId) (resolved : Bool) :
    Session grow sig (Ret (core3 grow)) :=
  (if resolved then Builtins.subtaskCancelDeliver subtask else pure [i32Flat (subtaskCancelResult none)]) >>= fun words =>
    pure (.flat words)

def ParkedCancel.finish {grow : SingleThreaded.GrowOracle} {sig : Signature} (subtask : SubtaskId) :
    Session grow sig (Ret (core3 grow)) := do
  modifyStore (CStore.setSyncWaiterSt (.subtask subtask) none)
  let resolved ← Builtins.subtaskResolvedNow subtask
  ParkedCancel.result subtask resolved

def ParkedCancel.afterCallback {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    (cancel : ParkedCancel cfg subtask) (returned : Ret (core3 grow)) : Session grow sig (Ret (core3 grow)) := do
  let _ ← (match returned with
    | .unit => pure ()
    | _ => internal "late-bound call: expected Ret.unit" : Session grow sig Unit)
  Builtins.subtaskCancelSyncWait cancel.async_ subtask
  ParkedCancel.finish subtask

def ParkedCancel.callbackEntry {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    (cancel : ParkedCancel cfg subtask) (record : Subtask) (ready : HostReady (HostState sig))
    (impl : HostImpl (core3 grow) (HostState sig)) : Config (core3 grow) (HostState sig) :=
  { cfg with
    store := Builtins.WaitableSt.requestCancel subtask cancel.thread cfg.store
    ctl := ⟨some cancel.thread, .prog (specDispatch ready impl (.onCancel record.onCancel)),
      .prog cancel.afterCallback :: .core cancel.core cancel.next :: cancel.segments⟩ :: cancel.rest }

/-- A cancellation request through a guest task's actual implicit thread. -/
structure TaskCancelAdmission {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    (cancel : ParkedCancel cfg subtask) where
  record : Subtask
  taskId : TaskId
  callee : Task (core3 grow)
  implicitThread : ThreadId
  implicitState : Thread
  live : cfg.store.subtask? subtask = some record
  unresolved : record.state.resolved = false
  notDelivered : record.lenders.isSome = true
  notRequested : record.cancellationRequested = false
  notJoined : record.common.wset = none
  callback : record.onCancel = .task taskId
  taskLive : cfg.store.task? taskId = some callee
  implicitLive : callee.implicitThread = some implicitThread
  threadLive : cfg.store.thread? implicitThread = some implicitState

def TaskCancelAdmission.markedStore {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    {cancel : ParkedCancel cfg subtask} (request : TaskCancelAdmission cancel) : CStore (core3 grow) :=
  (Builtins.WaitableSt.requestCancel subtask cancel.thread cfg.store).setTaskState request.taskId .pendingCancel

/-- A started task whose implicit thread cannot reenter immediately. -/
structure StartedCancel {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    (cancel : ParkedCancel cfg subtask) extends TaskCancelAdmission cancel where
  started : callee.state = .started
  notCancellable : implicitState.cancellable = false

def StartedCancel.callbackReturned {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    {cancel : ParkedCancel cfg subtask} (request : StartedCancel cancel) : Config (core3 grow) (HostState sig) :=
  { cfg with
    store := request.toTaskCancelAdmission.markedStore
    ctl := ⟨some cancel.thread, .prog (cancel.afterCallback .unit),
      .core cancel.core cancel.next :: cancel.segments⟩ :: cancel.rest }

def StartedCancel.settledStore {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    {cancel : ParkedCancel cfg subtask} (request : StartedCancel cancel) : CStore (core3 grow) :=
  let marked := Builtins.WaitableSt.requestCancel subtask cancel.thread cfg.store
  let pending := marked.setTaskState request.taskId .pendingCancel
  pending.setSyncWaiterSt (.subtask subtask) none

def StartedCancel.resumed {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    {cancel : ParkedCancel cfg subtask} (request : StartedCancel cancel) : Config (core3 grow) (HostState sig) :=
  let store := request.settledStore
  { cfg with store := store, ctl := ⟨some cancel.thread,
    .core ((core3 grow).resume store.core cancel.core (.values [i32Flat (subtaskCancelResult none)])) cancel.next,
    cancel.segments⟩ :: cancel.rest }

/-- The reached callback return before K8 reads the subtask. -/
structure SyncCancelWait {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    (cancel : ParkedCancel cfg subtask) (atReturn : Config (core3 grow) (HostState sig)) where
  synchronous : cancel.async_ = false
  unresolved : atReturn.store.subtaskResolved subtask = false
  rest : List (Activation (core3 grow) (HostState sig))
  focused : atReturn.ctl = ⟨some cancel.thread, .prog (cancel.afterCallback .unit),
    .core cancel.core cancel.next :: cancel.segments⟩ :: rest

def ParkedCancel.saved {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    (cancel : ParkedCancel cfg subtask) : Activation (core3 grow) (HostState sig) :=
  ⟨some cancel.thread, .prog (ParkedCancel.finish subtask), .core cancel.core cancel.next :: cancel.segments⟩

def SyncCancelWait.blocked {cfg atReturn : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    {cancel : ParkedCancel cfg subtask} (wait : SyncCancelWait cancel atReturn) : Config (core3 grow) (HostState sig) :=
  { (atReturn.setCont cancel.thread (some cancel.saved)) with
    store := StepDefs.threadStatusSt cancel.thread .blocked
      (atReturn.store.startWaitingSt cancel.thread (.subtaskResolved subtask))
    ctl := wait.rest }

/-- A reached resumer, not an assumption that a scheduler always produces one. -/
structure SyncCancelResume {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    (cancel : ParkedCancel cfg subtask) (atResume : Config (core3 grow) (HostState sig)) where
  thread : Option ThreadId
  resumeAfter : Session grow sig (Ret (core3 grow))
  segments : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  focused : atResume.ctl = ⟨thread, .prog (Thread.resume cancel.thread >>= fun () => resumeAfter),
    segments⟩ :: rest
  waiting : atResume.store.threadIs Thread.waiting cancel.thread = true

def SyncCancelResume.reached {cfg atResume : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    {cancel : ParkedCancel cfg subtask} (resume : SyncCancelResume cancel atResume) : Config (core3 grow) (HostState sig) :=
  { (atResume.setCont cancel.thread none) with
    store := StepDefs.threadStatusSt cancel.thread .running (atResume.store.stopWaitingSt cancel.thread)
    ctl := cancel.saved :: ⟨resume.thread, .prog resume.resumeAfter, resume.segments⟩ :: resume.rest }

def SyncCancelResume.delivered {cfg atResume : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    {cancel : ParkedCancel cfg subtask} (resume : SyncCancelResume cancel atResume) : Config (core3 grow) (HostState sig) :=
  let reached := resume.reached
  let store := cancelDelivered (reached.store.setSyncWaiterSt (.subtask subtask) none) subtask
  { reached with store, ctl := ⟨some cancel.thread,
    .core ((core3 grow).resume store.core cancel.core (.values [i32Flat (subtaskCancelResult (some .returned))]))
      cancel.next, cancel.segments⟩ :: ⟨resume.thread, .prog resume.resumeAfter, resume.segments⟩ :: resume.rest }

def SyncCancelResume.afterTick {cfg atHost : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    {ready : HostReady (HostState sig)} {profile : ProfileKind} {cancel : ParkedCancel cfg subtask}
    (tick : SelectedTick cancel.thread atHost ready profile)
    (waiting : tick.atResume.store.threadIs Thread.waiting cancel.thread = true) : SyncCancelResume cancel tick.atResume :=
  ⟨none, modifyStore StepDefs.leaveHostSt >>= fun () => pure .unit, [], [], rfl, waiting⟩

/-- The initial route forces a resume. The started route checks readiness
after marking the pending task, using the actual host state. -/
inductive TaskCancelReentry {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    {cancel : ParkedCancel cfg subtask} (request : TaskCancelAdmission cancel) (ready : HostReady (HostState sig)) : Prop
  | initial (state : request.callee.state = .initial)
  | started (state : request.callee.state = .started) (cancellable : request.implicitState.cancellable = true)
      (available : request.markedStore.threadReady (ready cfg.host) request.implicitThread = true)

def TaskCancelAdmission.waiting {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    {cancel : ParkedCancel cfg subtask} (request : TaskCancelAdmission cancel) : Bool :=
  request.markedStore.threadIs Thread.waiting request.implicitThread

def TaskCancelAdmission.reentrySteps {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    {cancel : ParkedCancel cfg subtask} (request : TaskCancelAdmission cancel) : Nat :=
  (if request.callee.state = .initial then 16 else 19) + (if request.waiting then 3 else 2)

def ParkedCancel.callbackTail {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    (cancel : ParkedCancel cfg subtask) : List (Activation (core3 grow) (HostState sig)) :=
  ⟨some cancel.thread, .prog (pure .unit),
    .prog cancel.afterCallback :: .core cancel.core cancel.next :: cancel.segments⟩ :: cancel.rest

def TaskCancelAdmission.reentered {cfg : Config (core3 grow) (HostState sig)} {subtask : SubtaskId}
    {cancel : ParkedCancel cfg subtask} (request : TaskCancelAdmission cancel)
    (callee : Activation (core3 grow) (HostState sig)) : Config (core3 grow) (HostState sig) :=
  let store := if request.waiting then request.markedStore.stopWaitingSt request.implicitThread else request.markedStore
  { (cfg.setCont request.implicitThread none) with
    store := StepDefs.threadStatusSt request.implicitThread .running store
    ctl := callee :: cancel.callbackTail }

/-- An actual lift-side K1 wait reached before its entry count is incremented. -/
structure K1Wait (cfg : Config (core3 grow) (HostState sig)) (thread : ThreadId) (task : TaskId) where
  instance_ : InstId
  exclusive : Bool
  next : Bool → Session grow sig (Ret (core3 grow))
  segments : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  focused : cfg.ctl = ⟨some thread, .prog (Task.backpressureWait task instance_ exclusive >>= next),
    segments⟩ :: rest

variable {thread : ThreadId} {taskId : TaskId} {atWait : Config (core3 grow) (HostState sig)}

def K1Wait.condition (wait : K1Wait atWait thread taskId) : ReadyCond :=
  .backpressure wait.instance_ wait.exclusive

def K1Wait.incremented (wait : K1Wait atWait thread taskId) : CStore (core3 grow) :=
  ArenaField.insts.modify atWait.store wait.instance_ InstState.incWaitingToEnter

def K1Wait.saved (wait : K1Wait atWait thread taskId) : Activation (core3 grow) (HostState sig) :=
  ⟨some thread, .prog (do
    modifyInst wait.instance_ InstState.decWaitingToEnter
    let cancelled ← Task.deliverPendingCancel taskId
    (if cancelled then Task.cancel taskId >>= fun () => pure false else pure true : Session grow sig Bool) >>= wait.next),
    wait.segments⟩

def K1Wait.blocked (wait : K1Wait atWait thread taskId) : Config (core3 grow) (HostState sig) :=
  { (atWait.setCont thread (some wait.saved)) with
    store := StepDefs.threadStatusSt thread .blocked (wait.incremented.startWaitingSt thread wait.condition)
    ctl := wait.rest }

def K1Wait.deliveredStore (wait : K1Wait atWait thread taskId) (store : CStore (core3 grow)) : CStore (core3 grow) :=
  (ArenaField.insts.modify store wait.instance_ InstState.decWaitingToEnter).setTaskState taskId .cancelDelivered

def K1Wait.afterResolve (wait : K1Wait atWait thread taskId) (returned : Ret (core3 grow)) :
    Session grow sig (Ret (core3 grow)) :=
  match returned with
  | .unit => modifyStore (CStore.setTaskState taskId .resolved) >>= fun () => wait.next false
  | _ => internal "late-bound call: expected Ret.unit"

def K1Wait.resolveEntry (wait : K1Wait atWait thread taskId) (atResume : Config (core3 grow) (HostState sig))
    (caller : CallerId) (ready : HostReady (HostState sig)) (impl : HostImpl (core3 grow) (HostState sig))
    (rest : List (Activation (core3 grow) (HostState sig))) : Config (core3 grow) (HostState sig) :=
  { atResume with
    store := wait.deliveredStore atResume.store
    ctl := ⟨some thread, .prog (specDispatch ready impl (.onResolve caller none)),
      .prog wait.afterResolve :: wait.segments⟩ :: rest }

def K1Wait.borrowTrap (wait : K1Wait atWait thread taskId) (atResume : Config (core3 grow) (HostState sig)) :
    Config (core3 grow) (HostState sig) :=
  StepDefs.trapCfg { atResume with store := wait.deliveredStore atResume.store }

/-- The specification entry gate of the actual implicit thread. A positive
entry count can send the thread to K1 even if the condition is already ready. -/
structure K1GateEntry (cfg : Config (core3 grow) (HostState sig)) (thread : ThreadId) (taskId : TaskId) where
  task : Task (core3 grow)
  instance_ : InstState
  next : Bool → Session grow sig (Ret (core3 grow))
  segments : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  focused : cfg.ctl = ⟨some thread, .prog (Task.enterImplicitThread .none taskId >>= next), segments⟩ :: rest
  liveTask : cfg.store.task? taskId = some task
  asynchronous : task.ft.async_ = true
  liveInst : cfg.store.inst? task.inst = some instance_
  gated : (instance_.hasBackpressure task.needsExclusive || decide (instance_.numWaitingToEnter > 0)) = true

variable {atGate : Config (core3 grow) (HostState sig)}

def K1GateEntry.afterWait (entry : K1GateEntry atGate thread taskId)
    (task : Task (core3 grow)) (entered : Bool) : Session grow sig (Ret (core3 grow)) := do
  let accepted ← (if entered then do
    (if task.needsExclusive then modifyInst task.inst (InstState.withExclusive (some thread)) else pure () : Session grow sig Unit)
    pure true
  else pure false : Session grow sig Bool)
  let registered ← (if accepted then do
    let _ ← Task.registerThread taskId thread
    pure true
  else pure false : Session grow sig Bool)
  entry.next registered

def K1GateEntry.markedTask (entry : K1GateEntry atGate thread taskId) : Task (core3 grow) :=
  { entry.task with implicitThread := some thread }

def K1GateEntry.waitingEntry (entry : K1GateEntry atGate thread taskId) : Config (core3 grow) (HostState sig) :=
  { atGate with
    store := atGate.store.setImplicitThread taskId thread
    ctl := ⟨some thread, .prog (Task.backpressureWait taskId entry.task.inst entry.task.needsExclusive >>=
      entry.afterWait entry.markedTask), entry.segments⟩ :: entry.rest }

def K1GateEntry.wait (entry : K1GateEntry atGate thread taskId) : K1Wait entry.waitingEntry thread taskId :=
  ⟨entry.task.inst, entry.task.needsExclusive, entry.afterWait entry.markedTask, entry.segments, entry.rest, rfl⟩

/-- The lift continuation after the canonical implicit-thread admission. -/
def liftAdmissionTail (task : TaskId) (callee : (core3 grow).FuncAddr) (entered : Bool) :
    Session grow sig (Ret (core3 grow)) := do
  if !entered then return .unit
  let record ← getTask task
  let args ← Task.start task
  liftArgumentsBody .spec .none task callee record args

/-- The caller and subtask read by the reached canonical `onResolve(none)`.
The caller record selects the subtask; the cancel request alone does not. -/
structure LowerCancelResolution (store : CStore (core3 grow)) (caller : CallerId) (subtask : SubtaskId) where
  context : LiftLowerContext (core3 grow)
  args : List FlatValue
  position : Nat
  ft : WIT.FuncType Empty RtId
  maxParams : Nat
  maxResults : Nat
  record : Subtask
  callerLive : ArenaField.callers.get? store caller = some (.lower subtask context args position ft maxParams maxResults)
  live : store.subtask? subtask = some record
  requested : record.cancellationRequested = true
  active : record.state = .starting ∨ record.state = .started

variable {store : CStore (core3 grow)} {caller : CallerId} {subtask : SubtaskId}

def LowerCancelResolution.progressStore (resolution : LowerCancelResolution store caller subtask) : CStore (core3 grow) :=
  if resolution.record.index.isSome then store.setPendingSt (.subtask subtask) (.subtask subtask) else store

def LowerCancelResolution.cancelledState (resolution : LowerCancelResolution store caller subtask) : SubtaskState :=
  if resolution.record.state = .starting then .cancelledBeforeStarted else .cancelledBeforeReturned

def LowerCancelResolution.resolvedStore (resolution : LowerCancelResolution store caller subtask) : CStore (core3 grow) :=
  resolution.progressStore.subtaskResolveSt subtask resolution.cancelledState []

def LowerCancelResolution.resolvedRecord (resolution : LowerCancelResolution store caller subtask) : Subtask :=
  { resolution.record with
    state := resolution.cancelledState
    flatResults := []
    common := if resolution.record.index.isSome then { resolution.record.common with pending := some (.subtask subtask) }
      else resolution.record.common }

def LowerCancelResolution.callbackSteps (resolution : LowerCancelResolution store caller subtask) : Nat :=
  if resolution.record.index.isSome then 8 else 7

def LowerCancelResolution.continued (wait : K1Wait atWait thread taskId) (atResume : Config (core3 grow) (HostState sig))
    (resolution : LowerCancelResolution (wait.deliveredStore atResume.store) caller subtask)
    (rest : List (Activation (core3 grow) (HostState sig))) : Config (core3 grow) (HostState sig) :=
  { atResume with
    store := resolution.resolvedStore.setTaskState taskId .resolved
    ctl := ⟨some thread, .prog (wait.next false), wait.segments⟩ :: rest }

/-- The resolved-cancellation caller finishes on the reached store, clearing
the temporary waiter before taking the pending event and releasing its lends. -/
def ParkedCancel.cancelledReply {cfg : Config (core3 grow) (HostState sig)}
    (cancel : ParkedCancel cfg subtask) (atExit : Config (core3 grow) (HostState sig)) (state : SubtaskState) :
    Config (core3 grow) (HostState sig) :=
  let delivered := cancelDelivered (atExit.store.setSyncWaiterSt (.subtask subtask) none) subtask
  let result := subtaskCancelResult (some state)
  { atExit with
    store := delivered
    ctl := ⟨some cancel.thread, .core ((core3 grow).resume delivered.core cancel.core (.values [i32Flat result])) cancel.next,
      cancel.segments⟩ :: cancel.rest }

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery
