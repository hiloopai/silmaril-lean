module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Callback.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Traversal.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.AsyncRef

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

/-- A semantic action is not a machine label: one action can emit several
machine labels, including choices, and a callback take need not reply to Core. -/
inductive Action where
  | invoke (call : CallId) (func : FuncId)
  | invokePrologue (call : CallId) (func : FuncId)
  | liftedLookup (func : FuncId) (caller : CallerId)
  | invokeReturn (cancel : CancelRef)
  | tick (selected : ThreadId)
  | coreStep
  | coreReturn
  | coreTrap
  | commit (target : SubtaskId) (index : Nat)
  | poll (target : SubtaskId) (index : Nat) (result : BufferResult)
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
  | invokeReturn {start cancel} (focused : start.ctl = [⟨none, .prog (.pure (.cancel cancel)), [.prog invokeReturn]⟩]) :
      Transition profile ready impl start (.invokeReturn cancel) [.tau, .tau, .tau]
        (StepDefs.hostFinish (.cancel cancel) [] { start with store := StepDefs.leaveHostSt start.store })
  | tick {start thread} (tick : SelectedTick thread start ready profile) :
      Transition profile ready impl start (.tick thread) tick.selectionLabels tick.atResume
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
