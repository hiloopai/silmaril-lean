module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Callback.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Traversal.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.AsyncRef
open PayloadPrefix (Cursor)

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}

abbrev State (grow : SingleThreaded.GrowOracle) (sig : Signature) := Config (core3 grow) (HostState sig)
abbrev Trace (grow : SingleThreaded.GrowOracle) (sig : Signature) := List (Label (core3 grow) (HostState sig))

inductive BufferResult where
  | replied
  | trapped (reason : TrapReason)

inductive GivePhase where
  | entered
  | refused (issue : Stored.Endpoints.RecordLower.Issue)
  | placementTrap (reason : TrapReason)
  | returned
  | bodyRefused (issue : Stored.Endpoints.RecordLower.Issue)
  | bodyTrap (reason : TrapReason)
  | refusalReplied (issue : Stored.Endpoints.RecordLower.Issue)
  | allocatorPrefix (mark : Option ReturnFrame.Occurrence.Location)

def BufferResult.finish {α : Type} (result : BufferResult) (resumed trapped : α) : α :=
  match result with
  | .replied => resumed
  | .trapped _ => trapped

/-- Buffer validation is after event consumption. The size is read in the
state used by the corresponding canonical bounds check. -/
inductive BufferBranch (store : CStore (core3 grow)) (memory ptr : Nat) :
    BufferResult → Trace grow sig → Prop where
  | unaligned (bad : ptr % 4 ≠ 0) : BufferBranch store memory ptr (.trapped .unalignedPointer) [.trap .unalignedPointer]
  | outside {size} (aligned : ptr % 4 = 0) (sized : (core3 grow).memSize? store.core memory = some size)
      (bad : size < ptr + 8) : BufferBranch store memory ptr (.trapped .outOfBounds) [.tau, .trap .outOfBounds]
  | inside {size} (aligned : ptr % 4 = 0) (sized : (core3 grow).memSize? store.core memory = some size)
      (fits : ptr + 8 ≤ size) : BufferBranch store memory ptr .replied (List.replicate 6 .tau)

/-- The reference side stops at a real prefix on a checked refusal. Only
the trap case requires both traces to end with an actual canonical trap. -/
inductive GiveStop {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (check : Cursor (E := core3 grow) (HostState sig)) :
    GivePhase → Trace grow sig → State grow sig → State grow sig → Prop where
  | refused {issue labels reached reference}
      (control : reached.ctl = check.control (site.reply (.error issue))) :
      GiveStop site check (.bodyRefused issue) labels reached reference
  | trapped {reason labels reached reference}
      (checked : reached.ctl = []) (canonical : reference.ctl = [])
      (trapLabel : ∃ leading, PayloadPrefix.visible labels = leading ++ [.trap reason]) :
      GiveStop site check (.bodyTrap reason) labels reached reference

/-- Transport only compared stopped prefixes, not every schedule or all
implementations of any host-function hook they may reach. -/
def GiveCutDispatch (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (callees : List (Callee sig)) {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) : Prop :=
  ∀ {checkLabels canonLabels reached reference check phase},
    GiveStop site check phase canonLabels reached reference →
    reached.store = reference.store → PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels →
    Steps profile ready (Dispatch.coreOnly ready bindings) site.checked checkLabels reached →
    Steps profile ready (Dispatch.coreOnly ready bindings) (site.reference site.referenceReply) canonLabels reference →
    Dispatch.Compatible profile ready bindings callees site.checked checkLabels reached ∧
    Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonLabels reference

/-- Both allocator traces follow the same installed occurrence. A saved
mark denotes suspension; an absent mark is not a return or a suspension. -/
structure AllocatorCut (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right reached reference : State grow sig) (checkLabels canonLabels : Trace grow sig)
    (mark : Option ReturnFrame.Occurrence.Location) : Prop where
  checked : ReturnFrame.Occurrence.Trail profile ready (Dispatch.coreOnly ready bindings)
    left (some (.active 0 0)) checkLabels reached mark
  canonical : ReturnFrame.Occurrence.Trail profile ready (Dispatch.coreOnly ready bindings)
    right (some (.active 0 0)) canonLabels reference mark
  paired : HostFrame.Related.Paired changes reached reference
  outside : ReturnFrame.Occurrence.Outside older (ReturnFrame.Occurrence.segmentStorage reached)
    (ReturnFrame.Occurrence.segmentStorage reference) mark
  seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels

def refusedBodyReply {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (reached : State grow sig)
    (check : Cursor (E := core3 grow) (HostState sig)) (segments : List (Seg (core3 grow) (HostState sig)))
    (issue : Stored.Endpoints.RecordLower.Issue) : State grow sig :=
  let reply := route.reply site.destination site.start.host.nextTicket (.error issue)
  { reached with
    host := reached.host.record reply.1
    ctl := ⟨check.thread, .core ((core3 grow).resume reached.store.core site.core (.values reply.2)) site.resume,
      segments⟩ :: check.rest }

def pollReply {start : State grow sig} {target : SubtaskId} (poll : ParkedPoll start target profile)
    (index : Nat) : State grow sig :=
  let ptr := flatNat poll.out
  let written := writeMemSt poll.memory (ptr + 4) (u32Bytes SubtaskState.returned.toNat)
    (writeMemSt poll.memory ptr (u32Bytes index) poll.delivered)
  { start with store := written, ctl := ⟨some poll.thread,
      .core ((core3 grow).resume written.core poll.core (.values [i32Flat EventCode.subtask.toNat])) poll.next,
      poll.segments⟩ :: poll.rest }

def pollLabels {start : State grow sig} {target : SubtaskId} (poll : ParkedPoll start target profile) : Trace grow sig :=
  List.replicate 10 .tau ++ [.choice (.shuffle poll.set.elems.length) poll.perm] ++ List.replicate 4 .tau

def eventFor (record : Subtask) : EventTuple := ⟨.subtask, record.index.getD 0, record.state.toNat⟩

def invokeCaller (start : State grow sig) : CallerId :=
  (ArenaField.callers (E := core3 grow)).mkId (ArenaField.callers.size start.store)

def invokeReturn (reply : Ret (core3 grow)) : P (core3 grow) (HostState sig) (Ret (core3 grow)) := do
  modifyStore StepDefs.leaveHostSt
  pure reply

def invokeStart (start : State grow sig) (call : CallId) (func : FuncId) (args : List Value.Val) : State grow sig :=
  { start with pending := start.pending ++ [(call, func, args)], ctl := [.ofProg none (StepDefs.invokeProg call func args)] }

def invokeCall (start : State grow sig) (call : CallId) (func : FuncId) (args : List Value.Val) : State grow sig :=
  { start with
    store := StepDefs.enterHostSt (ArenaOps.allocSt ArenaField.callers (.host call args 0) start.store)
    ctl := [.ofProg none (.op (.call (.funcInst func (invokeCaller start))) invokeReturn)] }

/-- The first canonical lift instruction, with the original host continuation
still waiting for its cancel handle. The arguments are in the fresh caller. -/
def invokeLift (start : State grow sig) (call : CallId) (func : FuncId) (args : List Value.Val)
    (core : (core3 grow).FuncAddr) (fnType : WIT.FuncType Empty RtId) (opts : CanonOpts (core3 grow))
    (inst : InstId) : State grow sig :=
  { invokeCall (invokeStart start call func args) call func args with
    ctl := [⟨none, .prog (canonLift Limits.spec Quirks.none core fnType opts inst (invokeCaller start)), [.prog invokeReturn]⟩] }

/-- The reached canonical lift retains the activation that invoked it. -/
structure LiftSite (grow : SingleThreaded.GrowOracle) (sig : Signature) where
  start : State grow sig
  core : (core3 grow).FuncAddr
  fnType : WIT.FuncType Empty RtId
  opts : CanonOpts (core3 grow)
  inst : InstId
  caller : CallerId
  parent : Option ThreadId
  frames : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  focused : start.ctl = ⟨parent, .prog (canonLift Limits.spec Quirks.none core fnType opts inst caller), frames⟩ :: rest

def LiftSite.ofInvoke (start : State grow sig) (call : CallId) (func : FuncId) (args : List Value.Val)
    (core : (core3 grow).FuncAddr) (fnType : WIT.FuncType Empty RtId) (opts : CanonOpts (core3 grow))
    (inst : InstId) : LiftSite grow sig :=
  ⟨invokeLift start call func args core fnType opts inst, core, fnType, opts, inst, invokeCaller start,
    none, [.prog invokeReturn], [], rfl⟩

def liftTaskData (fnType : WIT.FuncType Empty RtId) (opts : CanonOpts (core3 grow)) (inst : InstId) (caller : CallerId) :
    Task (core3 grow) :=
  { ft := fnType, opts, inst, caller }

def liftAfterThread (task : TaskId) (asyncMode : Bool) : Session grow sig (Ret (core3 grow)) := do
  (if !asyncMode then callUnit (.loop (.syncLiftLoop task)) else pure () : Session grow sig Unit)
  return .cancel (.task task)

def LiftSite.storeAndTask (site : LiftSite grow sig) : CStore (core3 grow) × TaskId :=
  ArenaField.tasks.alloc site.start.store (liftTaskData site.fnType site.opts site.inst site.caller)

def LiftSite.storeAndThread (site : LiftSite grow sig) : CStore (core3 grow) × ThreadId :=
  ArenaField.threads.alloc site.storeAndTask.1 { task := site.storeAndTask.2 }

def LiftSite.activation (site : LiftSite grow sig) : Activation (core3 grow) (HostState sig) :=
  .ofProg (some site.storeAndThread.2) (liftThreadBody Limits.spec Quirks.none site.storeAndTask.2 site.core)

def LiftSite.launched (site : LiftSite grow sig) : State grow sig :=
  let thread := site.storeAndThread.2
  { ((site.start.setCont thread (some site.activation)).setCont thread none) with
    store := StepDefs.threadStatusSt thread .running site.storeAndThread.1
    ctl := site.activation :: ⟨site.parent, .prog (liftAfterThread site.storeAndTask.2 site.fnType.async_), site.frames⟩ :: site.rest }

/-- The direct-entry branch of the canonical gate. The exclusive update is
made before registration, whose table capacity is checked on that instance. -/
def LiftSite.entryInstance (site : LiftSite grow sig) (instance_ : InstState) : InstState :=
  if site.fnType.async_ && (liftTaskData site.fnType site.opts site.inst site.caller).needsExclusive then
    instance_.withExclusive (some site.storeAndThread.2)
  else instance_

def LiftSite.markedTask (site : LiftSite grow sig) : Task (core3 grow) :=
  { liftTaskData site.fnType site.opts site.inst site.caller with implicitThread := some site.storeAndThread.2 }

def LiftSite.entryStore (site : LiftSite grow sig) : CStore (core3 grow) :=
  let marked := site.launched.store.setImplicitThread site.storeAndTask.2 site.storeAndThread.2
  if site.fnType.async_ && site.markedTask.needsExclusive then
    ArenaField.insts.modify marked site.inst (InstState.withExclusive (some site.storeAndThread.2))
  else marked

def LiftSite.registeredTask (site : LiftSite grow sig) : Task (core3 grow) :=
  { site.markedTask with threads := site.markedTask.threads ++ [site.storeAndThread.2] }

def LiftSite.argumentsTail (site : LiftSite grow sig) : List Value.Val → Session grow sig (Ret (core3 grow)) :=
  liftArgumentsBody Limits.spec Quirks.none site.storeAndTask.2 site.core site.registeredTask

def LiftSite.workerTail (site : LiftSite grow sig) : List (Activation (core3 grow) (HostState sig)) :=
  ⟨site.parent, .prog (liftAfterThread site.storeAndTask.2 site.fnType.async_), site.frames⟩ :: site.rest

def LiftSite.onStart (site : LiftSite grow sig) : State grow sig :=
  { site.launched with
    store := (site.entryStore.registerThreadSt site.storeAndTask.2 site.storeAndThread.2).setTaskState site.storeAndTask.2 .started
    ctl := ⟨some site.storeAndThread.2, .prog (callVals (.onStart site.registeredTask.caller) >>= site.argumentsTail), []⟩ :: site.workerTail }

def LiftSite.withArguments (site : LiftSite grow sig) (args : List Value.Val) : State grow sig :=
  { site.onStart with ctl := ⟨some site.storeAndThread.2, .prog (site.argumentsTail args), []⟩ :: site.workerTail }

def LiftSite.coreEnteredAt (site : LiftSite grow sig) (state : State grow sig) (flat : List FlatValue)
    (next : List FlatValue → Session grow sig (Ret (core3 grow))) : State grow sig :=
  { state with ctl := ⟨some site.storeAndThread.2, .core ((core3 grow).invoke site.core flat) next, []⟩ :: site.workerTail }

def LiftSite.coreEntered (site : LiftSite grow sig) (flat : List FlatValue)
    (next : List FlatValue → Session grow sig (Ret (core3 grow))) : State grow sig :=
  site.coreEnteredAt site.onStart flat next

/-- The scheduler selected the actual saved K1 activation at this host cut. -/
structure K1Resume {atWait : State grow sig} {thread : ThreadId} {task : TaskId}
    (wait : K1Wait atWait thread task) (atHost : State grow sig)
    (ready : HostReady (HostState sig)) (profile : ProfileKind) where
  tick : SelectedTick thread atHost ready profile
  saved : atHost.cont? thread = some wait.saved

section

variable {atWait atHost : State grow sig} {thread : ThreadId} {task : TaskId}
  {wait : K1Wait atWait thread task} {ready : HostReady (HostState sig)}

def K1Resume.reached (resume : K1Resume wait atHost ready profile) : State grow sig :=
  { (resume.tick.atResume.setCont thread none) with
    store := StepDefs.threadStatusSt thread .running (resume.tick.atResume.store.stopWaitingSt thread)
    ctl := wait.saved :: [Activation.ofProg none (modifyStore StepDefs.leaveHostSt >>= fun () => pure .unit)] }

def K1Resume.labels (resume : K1Resume wait atHost ready profile) : Trace grow sig :=
  resume.tick.selectionLabels ++ [.tau, .tau, .tau]

def K1Resume.admitted (resume : K1Resume wait atHost ready profile) : State grow sig :=
  { resume.reached with
    store := ArenaField.insts.modify resume.reached.store wait.instance_ InstState.decWaitingToEnter
    ctl := ⟨some thread, .prog (wait.next true), wait.segments⟩ :: resume.reached.ctl.drop 1 }

end

/-- K1 takes the exclusive lock according to its saved admission branch,
then registration consults the live task and the reached instance table. -/
def K1Resume.entryStore {atGate atHost : State grow sig} {thread : ThreadId} {task : TaskId}
    {entry : K1GateEntry atGate thread task} {ready : HostReady (HostState sig)}
    (resume : K1Resume entry.wait atHost ready profile) : CStore (core3 grow) :=
  if entry.markedTask.needsExclusive then
    ArenaField.insts.modify resume.admitted.store entry.markedTask.inst (InstState.withExclusive (some thread))
  else resume.admitted.store

structure K1LiftStart {atGate atHost : State grow sig} {thread : ThreadId} {task : TaskId}
    {entry : K1GateEntry atGate thread task} {ready : HostReady (HostState sig)}
    (resume : K1Resume entry.wait atHost ready profile) where
  callee : (core3 grow).FuncAddr
  body : entry.next = liftAdmissionTail task callee
  record : Task (core3 grow)
  live : resume.reached.store.task? task = some record
  instance_ : InstState
  liveInstance : (resume.entryStore (entry := entry)).inst? record.inst = some instance_
  index : Nat
  installed : InstState
  capacity : instance_.addThread? thread = some (index, installed)

section

variable {atGate atHost : State grow sig} {thread : ThreadId} {task : TaskId}
  {entry : K1GateEntry atGate thread task} {ready : HostReady (HostState sig)}
  {resume : K1Resume entry.wait atHost ready profile}

def K1LiftStart.registered (start : K1LiftStart resume) : Task (core3 grow) :=
  { start.record with threads := start.record.threads ++ [thread] }

def K1LiftStart.onStart (start : K1LiftStart resume) : State grow sig :=
  { resume.admitted with
    store := ((resume.entryStore (entry := entry)).registerThreadSt task thread).setTaskState task .started
    ctl := ⟨some thread, .prog (callVals (.onStart start.registered.caller) >>=
      liftArgumentsBody .spec .none task start.callee start.registered), entry.segments⟩ :: resume.admitted.ctl.drop 1 }

def K1LiftStart.labels (_start : K1LiftStart resume) : Trace grow sig :=
  List.replicate (if entry.markedTask.needsExclusive then 7 else 6) .tau

end

/-- Direct parameters that need neither allocating nor nondeterministic lowering. -/
inductive DirectArgument where
  | bool (value : Bool)
  | u32 (value : BitVec 32)

def DirectArgument.type : DirectArgument → Stored.TypeOf
  | .bool _ => .prim .bool
  | .u32 _ => .prim .u32

def DirectArgument.value : DirectArgument → Value.Val
  | .bool value => .bool value
  | .u32 value => .int .u32 value.toNat

def DirectArgument.flat : DirectArgument → FlatValue
  | .bool value => i32Flat (if value then 1 else 0)
  | .u32 value => lowerFlatInt .u32 value.toNat

def DirectArgument.byteCount : DirectArgument → Nat
  | .bool _ => 1
  | .u32 _ => 4

def DirectArgument.decode (arg : DirectArgument) (bytes : ByteArray) : Value.Val :=
  match arg with
  | .bool _ => .bool (convertIntToBool (intOfLE false bytes))
  | .u32 _ => .int .u32 (intOfLE false bytes)

def DirectArgument.address (arg : DirectArgument) (width : AddrType) (ptr : Nat) : Nat :=
  ABI.alignTo ptr (ABI.layout width arg.type).alignment

/-- The reached bytes and decoded values at each canonical tuple-field offset. -/
inductive ScalarSpill (store : CStore (core3 grow)) (memory : (core3 grow).MemAddr) (width : AddrType) :
    List DirectArgument → Nat → Prop where
  | nil (ptr : Nat) : ScalarSpill store memory width [] ptr
  | cons {arg args ptr} (bytes : ByteArray)
      (read : (core3 grow).memRead? store.core memory (arg.address width ptr) arg.byteCount = some bytes)
      (decoded : arg.decode bytes = arg.value)
      (rest : ScalarSpill store memory width args (arg.address width ptr + (ABI.layout width arg.type).size)) :
      ScalarSpill store memory width (arg :: args) ptr

/-- The exact host request reached in a guest activation, with the Core
continuation that the machine will park beneath the callout. -/
structure CoreCallSite (start : State grow sig) where
  thread : Option ThreadId
  core : (core3 grow).Thread (CanonHost (core3 grow))
  next : List FlatValue → Session grow sig (Ret (core3 grow))
  segments : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  target : CanonHost (core3 grow)
  args : List FlatValue
  focused : start.ctl = ⟨thread, .core core next, segments⟩ :: rest
  calling : (core3 grow).status start.store.core core = .callout target args

def CoreCallSite.reached {start : State grow sig} (site : CoreCallSite start)
    (ready : HostReady (HostState sig)) (impl : HostImpl (core3 grow) (HostState sig)) : State grow sig :=
  let body := match calloutEntry start.store site.thread site.target with
    | some reason => trap reason
    | none => calloutBody Limits.spec Quirks.none ready impl start.store site.thread site.target site.args
  { start with ctl := ⟨site.thread, .prog body, .core site.core site.next :: site.segments⟩ :: site.rest }

/-- The lowered import must be the actual reached Core request, with its
instance entry check already discharged. The lower body still reads mayLeave. -/
structure LowerRequest {start : State grow sig} (site : CoreCallSite start) where
  callee : FuncId
  fnType : WIT.FuncType Empty RtId
  opts : CanonOpts (core3 grow)
  inst : InstId
  target : site.target = .lowered callee fnType opts inst
  admitted : calloutEntry start.store site.thread site.target = none

section

variable {start : State grow sig}

def LowerRequest.storeAndSubtask {site : CoreCallSite start} (request : LowerRequest site) : CStore (core3 grow) × SubtaskId :=
  ArenaField.subtasks.alloc start.store { inst := request.inst }

def LowerRequest.callerData {site : CoreCallSite start} (request : LowerRequest site) : Caller (core3 grow) :=
  let sub := request.storeAndSubtask.2
  let limits := lowerLimits request.opts.async_
  .lower sub { opts := request.opts, inst := request.inst, scope := .subtask sub } site.args 0
    request.fnType limits.1 limits.2

def LowerRequest.storeAndCaller {site : CoreCallSite start} (request : LowerRequest site) : CStore (core3 grow) × CallerId :=
  ArenaField.callers.alloc request.storeAndSubtask.1 request.callerData

def LowerRequest.afterCall {site : CoreCallSite start} (request : LowerRequest site)
    (result : Ret (core3 grow)) : Session grow sig (Ret (core3 grow)) :=
  ((match result with
    | .cancel cancel => pure cancel
    | _ => internal "late-bound call: expected Ret.cancel") >>=
    lowerAfterCallee request.inst request.storeAndSubtask.2 request.opts.async_) >>= fun values => pure (.flat values)

def LowerRequest.allocated {site : CoreCallSite start} (request : LowerRequest site) : State grow sig :=
  { start with
    store := request.storeAndCaller.1
    ctl := ⟨site.thread, .prog (.op (.call (.funcInst request.callee request.storeAndCaller.2)) request.afterCall),
      .core site.core site.next :: site.segments⟩ :: site.rest }

def LowerRequest.lifted {site : CoreCallSite start} (request : LowerRequest site)
    (core : (core3 grow).FuncAddr) (fnType : WIT.FuncType Empty RtId) (opts : CanonOpts (core3 grow))
    (inst : InstId) : LiftSite grow sig :=
  let caller := request.storeAndCaller.2
  let program : Session grow sig (Ret (core3 grow)) := canonLift Limits.spec Quirks.none core fnType opts inst caller
  let frames := .prog request.afterCall :: .core site.core site.next :: site.segments
  ⟨{ request.allocated with ctl := ⟨site.thread, .prog program, frames⟩ :: site.rest },
    core, fnType, opts, inst, caller, site.thread, frames, site.rest, rfl⟩

end

/-- An actual return to this lower's saved continuation, above its parked
Core caller. The reached store need not equal the lower's allocation store. -/
structure LowerReturn {initial : State grow sig} {site : CoreCallSite initial}
    (request : LowerRequest site) (reached : State grow sig) where
  cancel : CancelRef
  focused : reached.ctl = ⟨site.thread, .prog (.pure (.cancel cancel)),
    .prog request.afterCall :: .core site.core site.next :: site.segments⟩ :: site.rest

section

variable {initial reached : State grow sig} {site : CoreCallSite initial} {request : LowerRequest site}

def LowerReturn.subtask (_ : LowerReturn request reached) : SubtaskId := request.storeAndSubtask.2

def LowerReturn.atProgram (_ : LowerReturn request reached) (store : CStore (core3 grow))
    (body : Session grow sig (Ret (core3 grow))) : State grow sig :=
  { reached with store, ctl := ⟨site.thread, .prog body, .core site.core site.next :: site.segments⟩ :: site.rest }

def LowerReturn.cancelInstalled (returned : LowerReturn request reached) : State grow sig :=
  returned.atProgram (LowerSt.setOnCancelSt returned.subtask returned.cancel reached.store)
    (lowerAfterCancel request.inst returned.subtask request.opts.async_ >>= fun values => pure (.flat values))

def LowerReturn.indexedStore (returned : LowerReturn request reached) (index : Nat) : CStore (core3 grow) :=
  LowerSt.addSubtaskSt request.inst returned.subtask index returned.cancelInstalled.store

def LowerReturn.pendingValues (record : Subtask) (index : Nat) : List FlatValue :=
  [i32Flat (AsyncLowerResult.pending record.state index).pack]

def LowerReturn.delivered (returned : LowerReturn request reached) : State grow sig :=
  returned.atProgram (returned.cancelInstalled.store.deliverResolveSt returned.subtask)
    (.pure (.flat [i32Flat AsyncLowerResult.returned.pack]))

def LowerReturn.pending (returned : LowerReturn request reached) (record : Subtask) (index : Nat) : State grow sig :=
  returned.atProgram (returned.indexedStore index) (.pure (.flat (LowerReturn.pendingValues record index)))

def LowerReturn.pendingReply (returned : LowerReturn request reached) (record : Subtask) (index : Nat) : State grow sig :=
  { returned.pending record index with ctl :=
    ⟨site.thread, .core ((core3 grow).resume (returned.indexedStore index).core site.core
      (.values (LowerReturn.pendingValues record index))) site.next, site.segments⟩ :: site.rest }

def LowerReturn.tableFull (returned : LowerReturn request reached) : State grow sig :=
  returned.atProgram returned.cancelInstalled.store (trap .tableFull >>= fun values : List FlatValue => pure (.flat values))

end

/-- The reached `onStart` call and its saved worker continuation, independent
of whether admission was immediate or resumed from a K1 park. -/
structure OnStartSite (state : State grow sig) where
  thread : ThreadId
  caller : CallerId
  next : List Value.Val → Session grow sig (Ret (core3 grow))
  segments : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  focused : state.ctl = ⟨some thread, .prog (callVals (.onStart caller) >>= next), segments⟩ :: rest

def OnStartSite.entered {state : State grow sig} (site : OnStartSite state) (reached : State grow sig)
    (callee : (core3 grow).FuncAddr) (flat : List FlatValue)
    (next : List FlatValue → Session grow sig (Ret (core3 grow))) : State grow sig :=
  { reached with ctl := ⟨some site.thread, .core ((core3 grow).invoke callee flat) next, site.segments⟩ :: site.rest }

def LiftSite.startCursor (site : LiftSite grow sig) : OnStartSite site.onStart :=
  ⟨site.storeAndThread.2, site.registeredTask.caller, site.argumentsTail, [], site.workerTail, rfl⟩

def K1LiftStart.startCursor {atGate atHost : State grow sig} {thread : ThreadId} {task : TaskId}
    {entry : K1GateEntry atGate thread task} {ready : HostReady (HostState sig)}
    {resume : K1Resume entry.wait atHost ready profile} (handoff : K1LiftStart resume) : OnStartSite handoff.onStart :=
  ⟨thread, handoff.registered.caller, liftArgumentsBody .spec .none task handoff.callee handoff.registered,
    entry.segments, resume.admitted.ctl.drop 1, rfl⟩

/-- The lower caller read by the admitted lift, including the live progress
record. Re-reading it distinguishes eager start from a pending event replacement. -/
structure LowerStartAt {state : State grow sig} (site : OnStartSite state) where
  subtask : SubtaskId
  context : LiftLowerContext (core3 grow)
  flat : List FlatValue
  pos : Nat
  fnType : WIT.FuncType Empty RtId
  maxParams : Nat
  maxResults : Nat
  record : Subtask
  callerLive : ArenaField.callers.get? state.store site.caller =
    some (.lower subtask context flat pos fnType maxParams maxResults)
  subtaskLive : ArenaField.subtasks.get? state.store subtask = some record

abbrev LowerStart (site : LiftSite grow sig) := LowerStartAt site.startCursor

section

variable {state : State grow sig} {site : OnStartSite state}

def LowerStartAt.readArgs (handoff : LowerStartAt site) : Session grow sig (Ret (core3 grow)) :=
  (do
    let (values, cursor) ← liftFlatValues Limits.spec Quirks.none handoff.context handoff.maxParams
      ⟨handoff.flat, handoff.pos⟩ (handoff.fnType.params.map (·.2))
    modifyStore (LowerSt.setCallerPosSt site.caller cursor.pos)
    pure values) >>= fun values => pure (.vals values)

def OnStartSite.resume (site : OnStartSite state) (result : Ret (core3 grow)) : Session grow sig (Ret (core3 grow)) :=
  (match result with
  | .vals values => pure values
  | _ => internal "late-bound call: expected Ret.vals") >>= site.next

def LowerStartAt.progress (handoff : LowerStartAt site) : CStore (core3 grow) :=
  let store := state.store
  if handoff.record.index.isSome then CStore.setPendingSt (.subtask handoff.subtask) (.subtask handoff.subtask) store else store

def LowerStartAt.reading (handoff : LowerStartAt site) : State grow sig :=
  { state with
    store := LowerSt.startSt handoff.subtask handoff.progress
    ctl := ⟨some site.thread, .prog handoff.readArgs, .prog site.resume :: site.segments⟩ :: site.rest }

def LowerStartAt.types (handoff : LowerStartAt site) : List Stored.TypeOf := handoff.fnType.params.map (·.2)

def LowerStartAt.cursor (handoff : LowerStartAt site) : FlatCursor := ⟨handoff.flat, handoff.pos⟩

def LowerStartAt.readWidth (handoff : LowerStartAt site) : AddrType := ptrTypeIn handoff.reading.store handoff.context

def LowerStartAt.finishRead (_handoff : LowerStartAt site) (result : List Value.Val × FlatCursor) :
    Session grow sig (Ret (core3 grow)) := do
  modifyStore (LowerSt.setCallerPosSt site.caller result.2.pos)
  pure (.vals result.1)

def LowerStartAt.readControl (_handoff : LowerStartAt site) (body : Session grow sig (Ret (core3 grow))) :
    List (Activation (core3 grow) (HostState sig)) :=
  ⟨some site.thread, .prog body, .prog site.resume :: site.segments⟩ :: site.rest

def LowerStartAt.spillLayout (handoff : LowerStartAt site) (width : AddrType) : ABI.Layout :=
  ABI.layout width (.tuple handoff.types : Stored.TypeOf)

def LowerStartAt.readAt (handoff : LowerStartAt site) (width : AddrType) : Session grow sig (List Value.Val × FlatCursor) :=
  if (ABI.flattenTypes width handoff.types).length > handoff.maxParams then do
    let (pointer, cursor) ← handoff.cursor.next (ABI.pointerType width)
    let layout := handoff.spillLayout width
    trapIf (decide (flatNat pointer ≠ ABI.alignTo (flatNat pointer) layout.alignment)) .unalignedPointer
    checkInBounds handoff.context (flatNat pointer) layout.size
    let values ← loadTypesAt .spec .none handoff.context width handoff.types (flatNat pointer)
    pure (values, cursor)
  else liftFlatTypes .spec .none handoff.context width handoff.types handoff.cursor

def LowerStartAt.selectedRead (handoff : LowerStartAt site) : State grow sig :=
  { handoff.reading with ctl := handoff.readControl (handoff.readAt handoff.readWidth >>= handoff.finishRead) }

/-- A returned spill pointer is consumed once, independently of the number of loaded fields. -/
def LowerStartAt.spillCursor (handoff : LowerStartAt site) : FlatCursor :=
  { handoff.cursor with pos := handoff.pos + 1 }

def LowerStartAt.spillBody (handoff : LowerStartAt site) (pointer : FlatValue) : State grow sig :=
  { handoff.selectedRead with ctl := handoff.readControl (do
      let values ← loadTypesAt .spec .none handoff.context handoff.readWidth handoff.types (flatNat pointer)
      handoff.finishRead (values, handoff.spillCursor)) }

def LowerStartAt.spillLoaded (handoff : LowerStartAt site) (values : List Value.Val) : State grow sig :=
  { handoff.selectedRead with ctl := handoff.readControl (handoff.finishRead (values, handoff.spillCursor)) }

/-- The original `onStart` result frame has reached the caller cursor update.
Its store may already include effects from lifting the arguments. -/
structure LowerArgumentReturn (handoff : LowerStartAt site) (reached : State grow sig) where
  values : List Value.Val
  cursor : FlatCursor
  focused : reached.ctl = handoff.readControl (handoff.finishRead (values, cursor))

def LowerArgumentReturn.resumed {handoff : LowerStartAt site} {reached : State grow sig}
    (returned : LowerArgumentReturn handoff reached) : State grow sig :=
  { reached with
    store := LowerSt.setCallerPosSt site.caller returned.cursor.pos reached.store
    ctl := ⟨some site.thread, .prog (site.next returned.values), site.segments⟩ :: site.rest }

/-- The callee argument program installed by committing the reached caller cursor. -/
structure CalleeArguments {handoff : LowerStartAt site} {reached : State grow sig}
    (returned : LowerArgumentReturn handoff reached) where
  task : TaskId
  callee : (core3 grow).FuncAddr
  record : Task (core3 grow)
  body : site.next = liftArgumentsBody .spec .none task callee record

variable {handoff : LowerStartAt site} {reached : State grow sig} {returned : LowerArgumentReturn handoff reached}

def CalleeArguments.context (args : CalleeArguments returned) : LiftLowerContext (core3 grow) :=
  { opts := args.record.opts, inst := args.record.inst, scope := .task args.task }

def CalleeArguments.width (args : CalleeArguments returned) : AddrType :=
  ptrTypeIn returned.resumed.store args.context

def CalleeArguments.types (args : CalleeArguments returned) := paramTypes args.record.ft

def CalleeArguments.layout (args : CalleeArguments returned) : ABI.Layout :=
  ABI.layout args.width (.tuple args.types)

def CalleeArguments.atProgram (_ : CalleeArguments returned) (state : State grow sig)
    (program : Session grow sig (Ret (core3 grow))) : State grow sig :=
  { state with ctl := ⟨some site.thread, .prog program, site.segments⟩ :: site.rest }

def CalleeArguments.enter (args : CalleeArguments returned) (flat : List FlatValue) : Session grow sig (Ret (core3 grow)) :=
  liftArgumentsTail .spec .none args.task args.callee args.record args.context flat

def CalleeArguments.direct (args : CalleeArguments returned) : State grow sig :=
  args.atProgram returned.resumed (lowerFlatTypes .spec .none args.context args.width returned.values args.types >>= args.enter)

def CalleeArguments.write (args : CalleeArguments returned) (pointer : Nat) : Session grow sig (Ret (core3 grow)) := do
  store .spec .none args.context (.record returned.values) (.tuple args.types) pointer
  args.enter [ptrFlat args.width pointer]

def CalleeArguments.place (args : CalleeArguments returned) (pointer : Nat) : Session grow sig (Ret (core3 grow)) := do
  trapIf (decide (pointer ≠ ABI.alignTo pointer args.layout.alignment)) .unalignedPointer
  checkInBounds args.context pointer args.layout.size
  args.write pointer

def CalleeArguments.request (args : CalleeArguments returned) : Call (core3 grow) :=
  .reallocate args.context 0 0 args.layout.alignment.bytes args.layout.size

def CalleeArguments.afterAllocate (args : CalleeArguments returned) : Ret (core3 grow) → Session grow sig (Ret (core3 grow))
  | .nat pointer => args.place pointer
  | _ => internal "late-bound call: expected Ret.nat"

def CalleeArguments.allocating (args : CalleeArguments returned) : State grow sig :=
  args.atProgram returned.resumed (.op (.call args.request) args.afterAllocate)

def CalleeArguments.installed (args : CalleeArguments returned)
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))) : State grow sig :=
  { returned.resumed with ctl :=
      ⟨some site.thread, .prog (dispatch args.request), .prog args.afterAllocate :: site.segments⟩ :: site.rest }

/-- The reached return to the saved spill frame. All placement checks use
the reached store, which can differ from the store at allocator entry. -/
structure CalleeSpillReturn (args : CalleeArguments returned) (state : State grow sig) where
  pointer : Nat
  segments : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  focused : state.ctl =
    ⟨some site.thread, .prog (.pure (.nat pointer)), .prog args.afterAllocate :: segments⟩ :: rest

def CalleeSpillReturn.writing {args : CalleeArguments returned} {state : State grow sig}
    (result : CalleeSpillReturn args state) : State grow sig :=
  { state with ctl := ⟨some site.thread, .prog (args.write result.pointer), result.segments⟩ :: result.rest }

def LiftSite.withLowerValues (site : LiftSite grow sig) (state : State grow sig) (args : List Value.Val)
    (pos : Nat) : State grow sig :=
  { state with
    store := LowerSt.setCallerPosSt site.registeredTask.caller pos state.store
    ctl := ⟨some site.storeAndThread.2, .prog (site.argumentsTail args), []⟩ :: site.workerTail }

def LowerStartAt.startedRecord (handoff : LowerStartAt site) : Subtask :=
  { handoff.record with
    state := .started
    common := if handoff.record.index.isSome then { handoff.record.common with pending := some (.subtask handoff.subtask) }
      else handoff.record.common }

def LowerStartAt.steps (handoff : LowerStartAt site) : Nat :=
  if handoff.record.index.isSome then 6 else 5

end

/-- The return continuation of a lift with async canonical options and no callback. -/
def stackfulTail (task : TaskId) (_flat : List FlatValue) : Session grow sig (Ret (core3 grow)) := do
  Task.exitImplicitThread task
  pure .unit

/-- A reached Core return, after any intervening guest and scheduler effects. -/
structure StackfulReturn (reached : State grow sig) where
  taskId : TaskId
  thread : ThreadId
  core : (core3 grow).Thread (CanonHost (core3 grow))
  values : List FlatValue
  segments : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  focused : reached.ctl = ⟨some thread, .core core (stackfulTail taskId), segments⟩ :: rest
  returned : (core3 grow).status reached.store.core core = .returned (.values values)

/-- Registration witnessed in the store at Core return, not the store at admission. -/
structure StackfulExit {reached : State grow sig} (site : StackfulReturn reached) where
  record : Task (core3 grow)
  registration : Thread
  inst : InstState
  slot : Nat
  removed : InstState
  taskLive : reached.store.task? site.taskId = some record
  implicitThread : record.implicitThread = some site.thread
  allowed : ((record.threads.erase site.thread).isEmpty && !decide (record.state = .resolved)) = false
  threadLive : ArenaField.threads.get? reached.store site.thread = some registration
  index : registration.index = some slot
  instanceLive : reached.store.inst? record.inst = some inst
  remove : inst.removeThread? slot = some (site.thread, removed)

def StackfulExit.completed {reached : State grow sig} {site : StackfulReturn reached}
    (exit : StackfulExit site) : State grow sig :=
  let unregistered := reached.store.unregisterThreadSt site.taskId site.thread exit.slot
  { reached with
    store := if exit.record.ft.async_ && exit.record.needsExclusive then
      ArenaField.insts.modify unregistered exit.record.inst (InstState.withExclusive none)
    else unregistered
    ctl := ⟨some site.thread, .prog (.pure .unit), site.segments⟩ :: site.rest }

def StackfulExit.finished {reached : State grow sig} {site : StackfulReturn reached}
    (exit : StackfulExit site) : State grow sig :=
  { exit.completed with
    store := StepDefs.threadStatusSt site.thread .exited exit.completed.store
    ctl := site.rest }

def StackfulExit.labels {reached : State grow sig} {site : StackfulReturn reached}
    (exit : StackfulExit site) : Trace grow sig :=
  List.replicate (6 + (exit.record.ft.async_ && exit.record.needsExclusive).toNat) .tau

/-- No K1 wait is entered on this branch. Full registration tables are not
classified as admitted and must take the canonical trap branch instead. -/
structure LiftAdmission (site : LiftSite grow sig) where
  instance_ : InstState
  live : site.start.store.inst? site.inst = some instance_
  ungated : site.fnType.async_ = true →
    (instance_.hasBackpressure site.markedTask.needsExclusive || decide (instance_.numWaitingToEnter > 0)) = false
  index : Nat
  registered : InstState
  capacity : (site.entryInstance instance_).addThread? site.storeAndThread.2 = some (index, registered)

def LiftSite.admissionLength (site : LiftSite grow sig) : Nat :=
  9 + (if site.fnType.async_ then 1 else 0) + (if site.fnType.async_ && site.markedTask.needsExclusive then 1 else 0)

/-- A semantic action is not a machine label: one action can emit several
machine labels, including choices, and a callback take need not reply to Core. -/
inductive Action where
  | invoke (call : CallId) (func : FuncId)
  | invokePrologue (call : CallId) (func : FuncId)
  | liftedLookup (func : FuncId) (caller : CallerId)
  | liftLaunch (task : TaskId) (thread : ThreadId)
  | liftAdmit (task : TaskId) (thread : ThreadId)
  | liftArguments (call : CallId)
  | coreEnter (thread : ThreadId)
  | coreCallout
  | lowerAllocate (subtask : SubtaskId) (caller : CallerId)
  | lowerStart (subtask : SubtaskId) (indexed : Bool)
  | lowerEmptyArgs (caller : CallerId)
  | lowerReadWidth (caller : CallerId)
  | lowerSpill (caller : CallerId)
  | lowerLoadScalars (caller : CallerId)
  | lowerArgsReturn (caller : CallerId)
  | calleeArguments (thread : ThreadId) (spill : Bool)
  | calleeSpillPlacement (thread : ThreadId) (trap : Option TrapReason)
  | calleeAllocationPrefix (thread : ThreadId) (mark : ReturnFrame.Occurrence.Location)
  | lowerSpillTrap (caller : CallerId) (reason : TrapReason)
  | lowerInstallCancel (subtask : SubtaskId)
  | lowerEagerDelivery (subtask : SubtaskId)
  | lowerPending (subtask : SubtaskId) (index : Nat)
  | lowerTableFull (subtask : SubtaskId)
  | coreReply (values : List FlatValue)
  | invokeReturn (cancel : CancelRef)
  | tick (selected : ThreadId)
  | k1Resume (thread : ThreadId)
  | k1Admit (task : TaskId)
  | k1Start (task : TaskId)
  | coreStep
  | coreReturn
  | coreTrap
  | commit (target : SubtaskId) (index : Nat)
  | poll (target : SubtaskId) (index : Nat) (result : BufferResult)
  | stackfulComplete (task : TaskId)
  | stackfulUnresolved (task : TaskId)
  | workerExit (thread : ThreadId)
  | wait (target : SubtaskId) (index : Nat) (result : BufferResult)
  | waitEnter (thread : ThreadId) (early : Bool)
  | waitResume (thread : ThreadId)
  | cancel (target : SubtaskId) (state : SubtaskState)
  | cancelRequest (target : SubtaskId)
  | cancelReentry (target : SubtaskId) (thread : ThreadId)
  | cancelCallbackDone (target : SubtaskId)
  | cancelPark (target : SubtaskId)
  | cancelResume (target : SubtaskId)
  | callbackCancelled (thread : ThreadId)
  | callbackPark (thread : ThreadId)
  | callbackResume (thread : ThreadId)
  | callbackTake (target : SubtaskId) (event : EventTuple)
  | callbackResolveCancel (target : SubtaskId) (index : Nat)
  | callbackBorrowTrap (thread : ThreadId)
  | callbackExit (thread : ThreadId)
  | closedCallback (tracked : SubtaskId)
  | give (route : GiveEffectRoute) (phase : GivePhase)

/-- Each edge starts at the exact preceding machine cut. In particular there
is no cross-edge pending invariant: a take clears the reached record, and a
resolution uses the reached state and installs its own pending result. -/
inductive Transition (profile : ProfileKind) (ready : HostReady (HostState sig)) (impl : HostImpl (core3 grow) (HostState sig)) :
    State grow sig → Action → Trace grow sig → State grow sig → Prop where
  | invoke {start call func args} (hostReady : StepDefs.HostReadyCfg start)
      (fresh : ∀ entry ∈ start.pending, entry.1 ≠ call) :
      Transition profile ready impl start (.invoke call func) [.host (.invoke call func args)]
        (invokeStart start call func args)
  | invokePrologue {start call func args} (focused : start.ctl = [.ofProg none (StepDefs.invokeProg call func args)]) :
      Transition profile ready impl start (.invokePrologue call func) [.tau, .tau, .tau] (invokeCall start call func args)
  | liftedLookup {start thread func caller next frames rest core fnType opts inst}
      (focused : start.ctl = ⟨thread, .prog (.op (.call (.funcInst func caller)) next), frames⟩ :: rest)
      (lookup : start.store.func? func = some (.lifted core fnType opts inst)) :
      Transition profile ready impl start (.liftedLookup func caller) [.tau, .tau]
        { start with ctl := ⟨thread, .prog (canonLift Limits.spec Quirks.none core fnType opts inst caller),
          .prog next :: frames⟩ :: rest }
  | liftLaunch (site : LiftSite grow sig) :
      Transition profile ready impl site.start (.liftLaunch site.storeAndTask.2 site.storeAndThread.2)
        [.tau, .tau, .tau, .tau, .tau] site.launched
  | liftAdmit (site : LiftSite grow sig) (admission : LiftAdmission site) :
      Transition profile ready impl site.launched (.liftAdmit site.storeAndTask.2 site.storeAndThread.2)
        (List.replicate site.admissionLength .tau) site.onStart
  | liftArguments {call args} (site : LiftSite grow sig)
      (live : ArenaField.callers.get? site.start.store site.caller = some (.host call args 0)) :
      Transition profile ready impl site.onStart (.liftArguments call) [.tau, .tau, .obs (.started call), .tau]
        (site.withArguments args)
  | directCore {site : LiftSite grow sig} {args : List DirectArgument} {next}
      (entry : Steps profile ready (specDispatch ready impl) (site.withArguments (args.map DirectArgument.value))
        [.tau, .tau] (site.coreEntered (args.map DirectArgument.flat) next)) :
      Transition profile ready impl (site.withArguments (args.map DirectArgument.value))
        (.coreEnter site.storeAndThread.2) [.tau, .tau] (site.coreEntered (args.map DirectArgument.flat) next)
  | coreCallout {start : State grow sig} (site : CoreCallSite start) :
      Transition profile ready impl start .coreCallout [.tau, .tau, .tau] (site.reached ready impl)
  | lowerAllocate {start : State grow sig} {site : CoreCallSite start} (request : LowerRequest site)
      {instance_ : InstState} (live : start.store.inst? request.inst = some instance_) (allowed : instance_.mayLeave = true) :
      Transition profile ready impl (site.reached ready impl) (.lowerAllocate request.storeAndSubtask.2 request.storeAndCaller.2)
        [.tau, .tau, .tau, .tau, .tau] request.allocated
  | lowerStart {start} {site : OnStartSite start} (handoff : LowerStartAt site) :
      Transition profile ready impl start (.lowerStart handoff.subtask handoff.record.index.isSome)
        (List.replicate handoff.steps .tau) handoff.reading
  | lowerReadWidth {start} {site : OnStartSite start} (handoff : LowerStartAt site) :
      Transition profile ready impl handoff.reading (.lowerReadWidth site.caller) [.tau] handoff.selectedRead
  | lowerSpill {start} {site : OnStartSite start} (handoff : LowerStartAt site)
      {pointer : FlatValue} {memory : (core3 grow).MemAddr} {size : Nat}
      (spilled : handoff.maxParams < (ABI.flattenTypes handoff.readWidth handoff.types).length)
      (found : handoff.flat[handoff.pos]? = some pointer)
      (aligned : flatNat pointer = ABI.alignTo (flatNat pointer) (handoff.spillLayout handoff.readWidth).alignment)
      (selected : handoff.context.opts.memory = some memory)
      (sized : (core3 grow).memSize? handoff.selectedRead.store.core memory = some size)
      (fits : flatNat pointer + (handoff.spillLayout handoff.readWidth).size ≤ size) :
      Transition profile ready impl handoff.selectedRead (.lowerSpill site.caller) [.tau] (handoff.spillBody pointer)
  | lowerSpillRangeTrap {start} {site : OnStartSite start} (handoff : LowerStartAt site)
      {pointer : FlatValue} {memory : (core3 grow).MemAddr} {size : Nat}
      (spilled : handoff.maxParams < (ABI.flattenTypes handoff.readWidth handoff.types).length)
      (found : handoff.flat[handoff.pos]? = some pointer)
      (aligned : flatNat pointer = ABI.alignTo (flatNat pointer) (handoff.spillLayout handoff.readWidth).alignment)
      (selected : handoff.context.opts.memory = some memory)
      (sized : (core3 grow).memSize? handoff.selectedRead.store.core memory = some size)
      (outside : size < flatNat pointer + (handoff.spillLayout handoff.readWidth).size) :
      Transition profile ready impl handoff.selectedRead (.lowerSpillTrap site.caller .outOfBounds)
        [.tau, .trap .outOfBounds] (StepDefs.trapCfg handoff.selectedRead)
  | lowerLoadScalars {start} {site : OnStartSite start} (handoff : LowerStartAt site)
      {pointer : FlatValue} {memory : (core3 grow).MemAddr} {args : List DirectArgument}
      (schema : handoff.types = args.map DirectArgument.type)
      (selected : handoff.context.opts.memory = some memory)
      (fields : ScalarSpill handoff.selectedRead.store memory handoff.readWidth args (flatNat pointer)) :
      Transition profile ready impl (handoff.spillBody pointer) (.lowerLoadScalars site.caller)
        (List.replicate args.length .tau) (handoff.spillLoaded (args.map DirectArgument.value))
  | lowerArgsReturn {start reached} {site : OnStartSite start} {handoff : LowerStartAt site}
      (returned : LowerArgumentReturn handoff reached) :
      Transition profile ready impl reached (.lowerArgsReturn site.caller) [.tau, .tau] returned.resumed
  | calleeDirect {start reached} {site : OnStartSite start} {handoff : LowerStartAt site}
      {returned : LowerArgumentReturn handoff reached} (args : CalleeArguments returned)
      (fits : (ABI.flattenTypes args.width args.types).length ≤ ABI.maxFlatParams) :
      Transition profile ready impl returned.resumed (.calleeArguments site.thread false) [.tau] args.direct
  | calleeAllocate {start reached} {site : OnStartSite start} {handoff : LowerStartAt site}
      {returned : LowerArgumentReturn handoff reached} (args : CalleeArguments returned)
      (spill : ABI.maxFlatParams < (ABI.flattenTypes args.width args.types).length) :
      Transition profile ready impl returned.resumed (.calleeArguments site.thread true) [.tau, .tau]
        (args.installed (specDispatch ready impl))
  | calleeAllocationPrefix {start reached state labels mark} {site : OnStartSite start} {handoff : LowerStartAt site}
      {returned : LowerArgumentReturn handoff reached} (args : CalleeArguments returned)
      (path : ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready impl)
        (args.installed (specDispatch ready impl)) (.active 0 0) labels state mark) :
      Transition profile ready impl (args.installed (specDispatch ready impl))
        (.calleeAllocationPrefix site.thread mark) labels state
  | calleeUnaligned {start reached state} {site : OnStartSite start} {handoff : LowerStartAt site}
      {returned : LowerArgumentReturn handoff reached} {args : CalleeArguments returned} (result : CalleeSpillReturn args state)
      (bad : result.pointer ≠ ABI.alignTo result.pointer args.layout.alignment) :
      Transition profile ready impl state (.calleeSpillPlacement site.thread (some .unalignedPointer))
        [.tau, .trap .unalignedPointer] (StepDefs.trapCfg state)
  | calleePlaced {start reached state} {site : OnStartSite start} {handoff : LowerStartAt site}
      {returned : LowerArgumentReturn handoff reached} {args : CalleeArguments returned} (result : CalleeSpillReturn args state)
      {memory size} (aligned : result.pointer = ABI.alignTo result.pointer args.layout.alignment)
      (selected : args.context.opts.memory = some memory) (sized : (core3 grow).memSize? state.store.core memory = some size)
      (fits : result.pointer + args.layout.size ≤ size) :
      Transition profile ready impl state (.calleeSpillPlacement site.thread none) [.tau, .tau]
        result.writing
  | calleeOutside {start reached state} {site : OnStartSite start} {handoff : LowerStartAt site}
      {returned : LowerArgumentReturn handoff reached} {args : CalleeArguments returned} (result : CalleeSpillReturn args state)
      {memory size} (aligned : result.pointer = ABI.alignTo result.pointer args.layout.alignment)
      (selected : args.context.opts.memory = some memory) (sized : (core3 grow).memSize? state.store.core memory = some size)
      (outside : size < result.pointer + args.layout.size) :
      Transition profile ready impl state (.calleeSpillPlacement site.thread (some .outOfBounds))
        [.tau, .tau, .trap .outOfBounds] (StepDefs.trapCfg state)
  | calleeStackfulCore {start reached state} {site : OnStartSite start} {handoff : LowerStartAt site}
      {returned : LowerArgumentReturn handoff reached} (args : CalleeArguments returned) {flat segments rest}
      (focused : state.ctl = ⟨some site.thread, .prog (args.enter flat), segments⟩ :: rest)
      (asyncMode : args.record.opts.async_ = true) (callback : args.record.opts.callback = none) :
      Transition profile ready impl state (.coreEnter site.thread) [.tau]
        { state with ctl :=
            ⟨some site.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), segments⟩ :: rest }
  | lowerDirectCore {start reached} {site : OnStartSite start} {callee flat next read}
      (focused : reached.ctl = ⟨some site.thread, .prog (.op .get read), site.segments⟩ :: site.rest)
      (selected : read reached.store = .op (.callCore callee flat) next) :
      Transition profile ready impl reached (.coreEnter site.thread) [.tau, .tau] (site.entered reached callee flat next)
  | lowerEmptyArgs {site : LiftSite grow sig} (handoff : LowerStart site) (empty : handoff.fnType.params = []) :
      Transition profile ready impl handoff.reading (.lowerEmptyArgs site.registeredTask.caller) [.tau, .tau, .tau]
        (site.withLowerValues handoff.reading [] handoff.pos)
  | lowerEmptyCore {site : LiftSite grow sig} (handoff : LowerStart site) {next}
      (entry : Steps profile ready (specDispatch ready impl) (site.withLowerValues handoff.reading [] handoff.pos)
        [.tau, .tau] (site.coreEnteredAt (site.withLowerValues handoff.reading [] handoff.pos) [] next)) :
      Transition profile ready impl (site.withLowerValues handoff.reading [] handoff.pos)
        (.coreEnter site.storeAndThread.2) [.tau, .tau] (site.coreEnteredAt (site.withLowerValues handoff.reading [] handoff.pos) [] next)
  | invokeReturn {start cancel} (focused : start.ctl = [⟨none, .prog (.pure (.cancel cancel)), [.prog invokeReturn]⟩]) :
      Transition profile ready impl start (.invokeReturn cancel) [.tau, .tau, .tau]
        (StepDefs.hostFinish (.cancel cancel) [] { start with store := StepDefs.leaveHostSt start.store })
  | lowerInstallCancel {initial reached : State grow sig} {site : CoreCallSite initial} {request : LowerRequest site}
      (returned : LowerReturn request reached) :
      Transition profile ready impl reached (.lowerInstallCancel returned.subtask) [.tau, .tau] returned.cancelInstalled
  | stackfulComplete {reached} {site : StackfulReturn reached} (exit : StackfulExit site) :
      Transition profile ready impl reached (.stackfulComplete site.taskId) exit.labels exit.completed
  | stackfulUnresolved {reached} (site : StackfulReturn reached) {record : Task (core3 grow)}
      (live : reached.store.task? site.taskId = some record)
      (implicitThread : record.implicitThread = some site.thread)
      (last : (record.threads.erase site.thread).isEmpty = true) (unresolved : record.state ≠ .resolved) :
      Transition profile ready impl reached (.stackfulUnresolved site.taskId)
        [.tau, .tau, .tau, .trap .taskNotResolved] (StepDefs.trapCfg reached)
  | stackfulExit {reached} {site : StackfulReturn reached} (exit : StackfulExit site) (empty : site.segments = []) :
      Transition profile ready impl exit.completed (.workerExit site.thread) [.tau] exit.finished
  | lowerEagerDelivery {initial reached : State grow sig} {site : CoreCallSite initial} {request : LowerRequest site}
      (returned : LowerReturn request reached) (asyncLower : request.opts.async_ = true)
      (resolved : returned.cancelInstalled.store.subtaskResolved returned.subtask = true) :
      Transition profile ready impl returned.cancelInstalled (.lowerEagerDelivery returned.subtask) [.tau, .tau]
        returned.delivered
  | lowerPending {initial reached : State grow sig} {site : CoreCallSite initial} {request : LowerRequest site}
      (returned : LowerReturn request reached) {instance_ nextInstance : InstState} {index : Nat} {record : Subtask}
      (asyncLower : request.opts.async_ = true)
      (recordLive : reached.store.subtask? returned.subtask = some record) (unresolved : record.state.resolved = false)
      (live : returned.cancelInstalled.store.inst? request.inst = some instance_)
      (room : instance_.addHandle? (.waitable (.subtask returned.subtask)) = some (index, nextInstance)) :
      Transition profile ready impl returned.cancelInstalled (.lowerPending returned.subtask index)
        [.tau, .tau, .tau, .tau] (returned.pending { record with onCancel := returned.cancel, index := some index } index)
  | lowerTableFull {initial reached : State grow sig} {site : CoreCallSite initial} {request : LowerRequest site}
      (returned : LowerReturn request reached) {instance_ : InstState}
      (asyncLower : request.opts.async_ = true)
      (unresolved : returned.cancelInstalled.store.subtaskResolved returned.subtask = false)
      (live : returned.cancelInstalled.store.inst? request.inst = some instance_)
      (full : instance_.addHandle? (.waitable (.subtask returned.subtask)) = none) :
      Transition profile ready impl returned.cancelInstalled (.lowerTableFull returned.subtask)
        [.tau, .tau, .trap .tableFull] (StepDefs.trapCfg returned.tableFull)
  | coreReply {start thread core next segments rest values}
      (focused : start.ctl = ⟨thread, .prog (.pure (.flat values)), .core core next :: segments⟩ :: rest) :
      Transition profile ready impl start (.coreReply values) [.tau]
        { start with ctl := ⟨thread, .core ((core3 grow).resume start.store.core core (.values values)) next, segments⟩ :: rest }
  | tick {start thread} (tick : SelectedTick thread start ready profile) :
      Transition profile ready impl start (.tick thread) tick.selectionLabels tick.atResume
  | k1Resume {atWait start thread task} {wait : K1Wait atWait thread task}
      (resume : K1Resume wait start ready profile) :
      Transition profile ready impl start (.k1Resume thread) resume.labels resume.reached
  | k1Admit {atWait start thread task} {wait : K1Wait atWait thread task}
      (resume : K1Resume wait start ready profile) {record : Task (core3 grow)}
      (live : resume.reached.store.task? task = some record) (notPending : record.state ≠ .pendingCancel) :
      Transition profile ready impl resume.reached (.k1Admit task) [.tau, .tau] resume.admitted
  | k1Start {atGate start thread task} {entry : K1GateEntry atGate thread task}
      {resume : K1Resume entry.wait start ready profile} (handoff : K1LiftStart resume) :
      Transition profile ready impl resume.admitted (.k1Start task) handoff.labels handoff.onStart
  | coreInternal {start thread core next segments rest coreStore advanced}
      (focused : start.ctl = ⟨thread, .core core next, segments⟩ :: rest)
      (running : (core3 grow).status start.store.core core = .running ∨ (core3 grow).status start.store.core core = .stuck)
      (step : (core3 grow).Internal (start.store.core, core) (coreStore, advanced)) :
      Transition profile ready impl start .coreStep [.core]
        { start with store := { start.store with core := coreStore }, ctl := ⟨thread, .core advanced next, segments⟩ :: rest }
  | coreReturned {start thread core next segments rest values}
      (focused : start.ctl = ⟨thread, .core core next, segments⟩ :: rest)
      (returned : (core3 grow).status start.store.core core = .returned (.values values)) :
      Transition profile ready impl start .coreReturn [.tau] { start with ctl := ⟨thread, .prog (next values), segments⟩ :: rest }
  | coreTrap {start thread core next segments rest}
      (focused : start.ctl = ⟨thread, .core core next, segments⟩ :: rest)
      (trapped : (core3 grow).status start.store.core core = .returned .trap) :
      Transition profile ready impl start .coreTrap [.trap .coreTrap] (StepDefs.trapCfg start)
  | commit {start target index} (resolve : LinkedResolution start target index) :
      Transition profile ready impl start (.commit target index) (List.replicate 17 .tau) resolve.committed
  | poll {start target index result suffix} (poll : ParkedPoll start target profile)
      (pending : PendingAt start.store target index) (branch : BufferBranch start.store poll.memory (flatNat poll.out) result suffix) :
      Transition profile ready impl start (.poll target index result) (pollLabels poll ++ suffix)
        (result.finish (pollReply poll index) { start with store := StepDefs.lockdownSt poll.delivered, ctl := [] })
  | waitBlock {start} (wait : ParkedWait start) (empty : start.store.wsetHasEvent wait.ws = false) :
      Transition profile ready impl start (.waitEnter wait.thread false) (List.replicate 13 .tau) wait.blocked
  | waitReady {start} (wait : ParkedWait start) (available : start.store.wsetHasEvent wait.ws = true)
      (early : Bool) (allowed : Allowed profile (.earlyReturn .waitableSetWait) early) :
      Transition profile ready impl start (.waitEnter wait.thread early) (ParkedWait.readyLabels early)
        (if early then wait.early else wait.blocked)
  | waitResume {initial start} {wait : ParkedWait initial} (resume : WaitResume wait start)
      (saved : start.cont? wait.thread = some wait.saved) :
      Transition profile ready impl start (.waitResume wait.thread) (List.replicate 4 .tau) resume.reached
  | waitTake {initial start target index result suffix} {wait : ParkedWait initial}
      (delivery : WaitDelivery wait start profile target)
      (focused : start.ctl = ⟨some wait.thread, .prog wait.takeEvent, .core wait.core wait.next :: wait.segments⟩ :: start.ctl.drop 1)
      (pending : PendingAt start.store target index)
      (branch : BufferBranch delivery.delivered wait.memory (flatNat wait.out) result suffix) :
      Transition profile ready impl start (.wait target index result) (delivery.labels ++ suffix)
        (result.finish (delivery.resumed index) { start with store := StepDefs.lockdownSt delivery.delivered, ctl := [] })
  | cancelReturned {start target index} (cancel : ParkedCancel start target)
      (pending : PendingAt start.store target index) (available : CancelAvailable start.store target) :
      Transition profile ready impl start (.cancel target .returned) (List.replicate 15 .tau) cancel.resumed
  | cancelReply {initial start target} (cancel : ParkedCancel initial target) (record : Subtask)
      (focused : start.ctl = cancel.callbackTail) (live : start.store.subtask? target = some record)
      (cancelled : record.state = .cancelledBeforeStarted ∨ record.state = .cancelledBeforeReturned)
      (pending : record.common.pending = some (.subtask target)) :
      Transition profile ready impl start (.cancel target record.state) (List.replicate 8 .tau) (cancel.cancelledReply start record.state)
  | cancelRequest {start target} (cancel : ParkedCancel start target) (record : Subtask)
      (live : start.store.subtask? target = some record) (unresolved : record.state.resolved = false)
      (notDelivered : record.lenders.isSome = true) (notRequested : record.cancellationRequested = false)
      (notJoined : record.common.wset = none) :
      Transition profile ready impl start (.cancelRequest target) (List.replicate 14 .tau) (cancel.callbackEntry record ready impl)
  | cancelReentry {start target callee} {cancel : ParkedCancel start target} (request : TaskCancelAdmission cancel)
      (mode : TaskCancelReentry request ready) (saved : start.cont? request.implicitThread = some callee) :
      Transition profile ready impl start (.cancelReentry target request.implicitThread)
        (List.replicate request.reentrySteps .tau) (request.reentered callee)
  | cancelCallbackDone {start target} {cancel : ParkedCancel start target} (request : StartedCancel cancel) :
      Transition profile ready impl start (.cancelCallbackDone target) (List.replicate 20 .tau) request.callbackReturned
  | cancelPark {initial start target} {cancel : ParkedCancel initial target} (wait : SyncCancelWait cancel start) :
      Transition profile ready impl start (.cancelPark target) (List.replicate 5 .tau) wait.blocked
  | cancelResume {initial start target} {cancel : ParkedCancel initial target} (resume : SyncCancelResume cancel start)
      (saved : start.cont? cancel.thread = some cancel.saved) :
      Transition profile ready impl start (.cancelResume target) (List.replicate 3 .tau) resume.reached
  | cancelTake {initial atResume target index} {cancel : ParkedCancel initial target} (resume : SyncCancelResume cancel atResume)
      (pending : PendingAt resume.reached.store target index) :
      Transition profile ready impl resume.reached (.cancel target .returned) (List.replicate 6 .tau) resume.delivered
  | callbackCancelled {start rest liveTask callback} (wait : CallbackWait grow sig) (focused : start.ctl = wait.saved :: rest)
      (live : start.store.task? wait.taskId = some liveTask) (pending : liveTask.state = .pendingCancel)
      (chosen : wait.task.opts.callback = some callback) :
      Transition profile ready impl start (.callbackCancelled wait.thread) (List.replicate wait.cancelSteps .tau)
        (wait.called start callback rest)
  | callbackPark {start rest available} (wait : CallbackWait grow sig)
      (availability : wait.condition.eval (fun _ => false) (wait.released start.store) = available) :
      Transition profile ready impl (wait.entry start rest) (.callbackPark wait.thread) (wait.parkLabels available) (wait.blocked start rest)
  | callbackResume {start} {wait : CallbackWait grow sig} (resume : CallbackResume wait start)
      (saved : start.cont? wait.thread = some wait.saved) :
      Transition profile ready impl start (.callbackResume wait.thread) resume.labels resume.resumed
  | callbackTake {start rest set liveTask record permutation target pendingRecord callback} (wait : CallbackWait grow sig)
      (kind : wait.kind = .wait set) (focused : start.ctl = wait.saved :: rest)
      (live : start.store.task? wait.taskId = some liveTask) (noCancel : liveTask.state ≠ .pendingCancel)
      (setLive : (wait.decrement start.store).wset? set = some record)
      (allowed : Allowed profile (.shuffle record.elems.length) permutation)
      (selects : (applyPerm permutation record.elems).find? (wait.shuffled start.store set record permutation).waitableHasEvent =
        some (.subtask target))
      (tracked : start.store.subtask? target = some pendingRecord) (resolved : pendingRecord.state.resolved = true)
      (pending : pendingRecord.common.pending = some (.subtask target)) (chosen : wait.task.opts.callback = some callback) :
      Transition profile ready impl start (.callbackTake target (eventFor pendingRecord))
        (List.replicate 3 .tau ++ [.choice (.shuffle record.elems.length) permutation] ++ List.replicate 6 .tau)
        (wait.eventCall start (cancelDelivered (wait.shuffled start.store set record permutation) target) callback
          (eventFor pendingRecord) rest)
  | callbackResolveCancel {start target index} {wait : CallbackWait grow sig} (entry : CallbackCancelImport wait start)
      (empty : entry.liveTask.numBorrows = 0) (resolution : LowerCancelResolution start.store entry.liveTask.caller target)
      (started : resolution.record.state = .started) (indexed : resolution.record.index = some index) :
      Transition profile ready impl start (.callbackResolveCancel target index)
        (List.replicate 9 .tau ++ List.replicate (resolution.callbackSteps + 1) .tau) (entry.resumed resolution)
  | callbackBorrowTrap {start} {wait : CallbackWait grow sig} (entry : CallbackCancelImport wait start)
      (borrows : entry.liveTask.numBorrows > 0) :
      Transition profile ready impl start (.callbackBorrowTrap wait.thread)
        (List.replicate 8 .tau ++ [.trap .borrowsRemain]) (StepDefs.trapCfg start)
  | callbackExit {start} {wait : CallbackWait grow sig} (exit : CallbackExit wait start) :
      Transition profile ready impl start (.callbackExit wait.thread) exit.labels exit.unwound
  | closedCallback {start finish target labels} (path : ClosedCallbackPrefix profile ready impl target start labels finish) :
      Transition profile ready impl start (.closedCallback target) labels finish
  | giveEntry {route bindings labels} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      (silent : PayloadPrefix.visible labels = [])
      (placed : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok ())
      (prepared : OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
      (run : Steps profile ready (specDispatch ready impl) site.start labels site.checked) :
      Transition profile ready impl site.start (.give route .entered) labels site.checked
  | giveRefused {route bindings labels} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      (issue : Stored.Endpoints.RecordLower.Issue) (silent : PayloadPrefix.visible labels = [])
      (run : Steps profile ready (specDispatch ready impl) site.start labels (site.withBody (site.reply (.error issue)))) :
      Transition profile ready impl site.start (.give route (.refused issue)) (labels ++ [.tau, .tau, .tau]) (site.refusedReply issue)
  | givePlacementTrap {route bindings} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      (reason : TrapReason) (count : Nat)
      (verdict : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .error reason)
      (run : Steps profile ready (specDispatch ready impl) site.start (List.replicate count .tau ++ [.trap reason])
        (StepDefs.trapCfg site.checked)) :
      Transition profile ready impl site.start (.give route (.placementTrap reason))
        (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg site.checked)
  | giveReturned {route bindings callees checkLabels canonLabels reached reference left right}
      (site : PayloadRoot.Site grow sig route) (value : route.output.Result)
      (overlay : impl = hostWithComponent bindings callees)
      (checked : Dispatch.Compatible profile ready bindings callees site.checked checkLabels reached)
      (canonical : Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonLabels reference)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
      (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference left right) :
      Transition profile ready impl site.checked (.give route .returned) (checkLabels ++ [.tau, .tau, .tau]) left
  | giveStopped {route bindings callees checkLabels canonLabels reached reference check phase}
      (site : PayloadRoot.Site grow sig route) (overlay : impl = hostWithComponent bindings callees)
      (checked : Dispatch.Compatible profile ready bindings callees site.checked checkLabels reached)
      (canonical : Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonLabels reference)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
      (store : reached.store = reference.store) (stopped : GiveStop site check phase canonLabels reached reference) :
      Transition profile ready impl site.checked (.give route phase) checkLabels reached
  | giveRefusalReply {route reached check segments issue} (site : PayloadRoot.Site grow sig route)
      (control : reached.ctl = check.control (site.reply (.error issue)))
      (caller : check.frames = .core site.core site.resume :: segments) :
      Transition profile ready impl reached (.give route (.refusalReplied issue)) [.tau, .tau, .tau]
        (refusedBodyReply site reached check segments issue)
  | giveAllocatorPrefix {route bindings callees older changes beforeCheck beforeCanon left right reached reference mark
      checkEntryLabels canonEntryLabels checkLabels canonLabels}
      (site : PayloadRoot.Site grow sig route) (overlay : impl = hostWithComponent bindings callees)
      (checkEntry : Dispatch.Compatible profile ready bindings callees site.checked checkEntryLabels beforeCheck)
      (canonEntry : Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonEntryLabels beforeCanon)
      (seenEntry : PayloadPrefix.visible checkEntryLabels = PayloadPrefix.visible canonEntryLabels)
      (checkInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCheck [.tau, .tau, .tau] left)
      (canonInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCanon [.tau, .tau] right)
      (checked : Dispatch.Compatible profile ready bindings callees left checkLabels reached)
      (canonical : Dispatch.Compatible profile ready bindings callees right canonLabels reference)
      (cut : AllocatorCut profile ready bindings older changes left right reached reference checkLabels canonLabels mark) :
      Transition profile ready impl site.checked (.give route (.allocatorPrefix mark)) (checkEntryLabels ++ [.tau, .tau, .tau] ++ checkLabels) reached

/-- Keep the original compared traces at a returning cut. A stopped cut
already induces a checked session edge and has no canonical reply step. -/
inductive GiveBodyCut (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (callees : List (Callee sig)) {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (check canon : Cursor (E := core3 grow) (HostState sig)) : Prop where
  | returned {value checkLabels canonLabels reached reference}
      (checked : Steps profile ready (Dispatch.coreOnly ready bindings) site.checked checkLabels reached)
      (canonical : Steps profile ready (Dispatch.coreOnly ready bindings) (site.reference site.referenceReply) canonLabels reference)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels) (store : reached.store = reference.store)
      (checkControl : reached.ctl = check.control (site.reply (.ok value)))
      (canonControl : reference.ctl = canon.control (site.referenceReply value)) :
      GiveBodyCut profile ready bindings callees site check canon
  | stopped {phase labels canonLabels reached reference}
      (stop : GiveStop site check phase canonLabels reached reference)
      (edge : Transition profile ready (hostWithComponent bindings callees) site.checked (.give route phase) labels reached) :
      GiveBodyCut profile ready bindings callees site check canon

/-- Finite concatenation, with machine labels in their original order. A run
can stop at a parked callback, at a producer, or at a delivery trap. -/
inductive Run (profile : ProfileKind) (ready : HostReady (HostState sig)) (impl : HostImpl (core3 grow) (HostState sig)) :
    State grow sig → List Action → Trace grow sig → State grow sig → Prop where
  | stop (state : State grow sig) : Run profile ready impl state [] [] state
  | next {start middle finish action actions leading trailing}
      (head : Transition profile ready impl start action leading middle)
      (tail : Run profile ready impl middle actions trailing finish) :
      Run profile ready impl start (action :: actions) (leading ++ trailing) finish

/-- The return proof already derives paired paths from the compiled body.
This contract concerns only dispatch at the late-bound calls on those paths;
it does not assume successful recursive lowering or common endpoints. -/
def GiveBodyAgreement (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (callees : List (Callee sig)) {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (reached reference : State grow sig) : Prop :=
  ∀ checkLabels canonLabels,
    ReturnFrame.Occurrence.RetainsActiveSlots profile ready (Dispatch.coreOnly ready bindings) site.checked checkLabels reached →
    ReturnFrame.Occurrence.RetainsActiveSlots profile ready (Dispatch.coreOnly ready bindings)
      (site.reference site.referenceReply) canonLabels reference →
    Dispatch.Compatible profile ready bindings callees site.checked checkLabels reached ∧
    Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonLabels reference

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
