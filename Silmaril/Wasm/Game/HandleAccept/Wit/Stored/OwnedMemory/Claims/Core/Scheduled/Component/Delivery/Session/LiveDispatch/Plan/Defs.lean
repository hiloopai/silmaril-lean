module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Traversal.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

/-- A raw host assignment is not a closed guest step. In particular, the
absence of a host read does not rule out an assignment installed by an open hook. -/
def NoHostAssignment (state : Config (core3 grow) (HostState sig)) : Prop :=
  ∀ thread value next frames rest,
    state.ctl ≠ ⟨thread, .prog (.op (.hostSet value) next), frames⟩ :: rest

/-- Reached allocator steps before a protected return. Ordinary steps must
not install an overlaid give or assign the host; confined gives and the
actual synchronous readiness read have their own rules. The endpoint may
be suspended, trapped, ready to pop a protected frame, or at an open hook. -/
inductive ClosedCallbackPrefix (bindings : List (Binding sig)) (profile : ProfileKind)
    (ready : HostReady (HostState sig)) (base : HostImpl (core3 grow) (HostState sig))
    (protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop) :
    Config (core3 grow) (HostState sig) → Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | done (state : Config (core3 grow) (HostState sig)) : ClosedCallbackPrefix bindings profile ready base protectedReturn state [] state
  | step {start next finish label seen}
      (interior : HostFrame.InteriorFor protectedReturn start) (unchanged : UnchangedAt bindings start)
      (noAssignment : NoHostAssignment start) (grows : CoreUpdateGrows start)
      (run : Step profile ready (specDispatch ready base) start label next)
      (tail : ClosedCallbackPrefix bindings profile ready base protectedReturn next seen finish) :
      ClosedCallbackPrefix bindings profile ready base protectedReturn start (PayloadPrefix.visible [label] ++ seen) finish
  | confinedGive {start finish seen} (callout : LinkedCallback.ClosedGive bindings start)
      (tail : ClosedCallbackPrefix bindings profile ready base protectedReturn callout.resume seen finish) :
      ClosedCallbackPrefix bindings profile ready base protectedReturn start seen finish
  | syncReady {start finish seen task inst thread frames rest}
      (focused : start.ctl = ⟨thread, .prog (.op .hostGet (fun current =>
        syncLiftCandidates task (start.store.instCandidates (ready current) inst))), frames⟩ :: rest)
      (agrees : LinkedCallback.ReadyAgreement ready start inst)
      (tail : ClosedCallbackPrefix bindings profile ready base protectedReturn { start with ctl := ⟨thread,
        .prog (syncLiftCandidates task (start.store.instCandidates (ready start.host) inst)), frames⟩ :: rest } seen finish) :
      ClosedCallbackPrefix bindings profile ready base protectedReturn start seen finish

/-- The installed allocator occurrence migrates through actual scheduler
edits. Older substitutions remain valid off that mark, even if it is lost
to a trap or the callback is still suspended. -/
structure AllocatorMark (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checkEntry canonEntry : Config (core3 grow) (HostState sig)) (checkTrace canonTrace : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) (mark : Option ReturnFrame.Occurrence.Location) : Prop where
  outside : ReturnFrame.Occurrence.Outside older (ReturnFrame.Occurrence.segmentStorage checked)
    (ReturnFrame.Occurrence.segmentStorage canonical) mark
  checkedTrail : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready base)
    checkEntry (some (.active 0 0)) checkTrace checked mark
  canonicalTrail : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready (LiveDispatch.host bindings base))
    canonEntry (some (.active 0 0)) canonTrace canonical mark

def stringAllocatorEntry (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat) (alignment : ABI.Alignment) (size : Nat)
    (state : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig)) : Config (core3 grow) (HostState sig) :=
  let request := Call.reallocate cx (oldSize.elim 0 (fun _ => ptr)) (oldSize.getD 0) alignment.bytes size
  { state with ctl := { cursor with frames := .prog resume :: cursor.frames }.control (dispatch request) }

/-- Validate the pointer from an actual marked return. The invalid branches
trap at the reached stores. The valid branch exposes the real checked live
verdict and the canonical child-entry program, before either executes children. -/
def CollectionRangeCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (destination : RecordDestination) (area : ABI.Layout) (count pointer : Nat)
    (plan : List Stored.Endpoints.RecordLower.Object)
    (checkNext : Nat → Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow))) : Prop :=
  let checkedDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  let traps := fun reason =>
    (∃ steps, Steps profile ready checkedDispatch checked (List.replicate steps .tau ++ [.trap reason]) (StepDefs.trapCfg checked)) ∧
    (∃ steps, Steps profile ready canonDispatch canonical (List.replicate steps .tau ++ [.trap reason]) (StepDefs.trapCfg canonical))
  ∃ canonCursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig), ∃ bytes,
    (core3 grow).memAddrType? checked.store.core destination.memory = some destination.width ∧
    (core3 grow).memSize? checked.store.core destination.memory = some bytes ∧
    LinkedCallback.ChildFrameOver older checked canonical cursor canonCursor ∧
    if pointer ≠ ABI.alignTo pointer area.alignment then traps .unalignedPointer
    else if pointer + count * area.size ≤ bytes then
      (∃ trace, (∀ label ∈ trace, label = .tau) ∧ ReturnFrame.Occurrence.RetainsBelowTop profile ready checkedDispatch checked trace
        { checked with ctl := cursor.control (checkNext pointer (OwnedMemory.Claims.Record.prepare checked.store checked.host.writer plan)) }) ∧
      (∃ trace, (∀ label ∈ trace, label = .tau) ∧ ReturnFrame.Occurrence.RetainsBelowTop profile ready canonDispatch canonical trace
        { canonical with ctl := canonCursor.control (canonNext pointer) })
    else traps .outOfBounds

/-- Continuations reached after consuming a marked allocator return. A
typed refusal only enters the checked continuation; the canonical cursor
has not executed the children. The retained slots exclude the popped frame. -/
def CollectionReturn (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) {Result : Type}
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (childEntry : Session grow sig (Ret (core3 grow))) : Prop :=
  let checkedDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  ∃ (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (outcome : PayloadPrefix.Outcome Result)
    (checkLabels canonLabels : Trace grow sig) (left right : Config (core3 grow) (HostState sig)),
    Steps profile ready checkedDispatch checked checkLabels left ∧ Steps profile ready canonDispatch canonical canonLabels right ∧
    left.store = right.store ∧ PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
    match outcome with
    | .trapped reason => left.ctl = [] ∧ right.ctl = [] ∧ ∃ leading, PayloadPrefix.visible canonLabels = leading ++ [.trap reason]
    | .returned value => LinkedCallback.ChildFrameOver older left right check canon ∧
        left.ctl = check.control (checkNext (.ok value)) ∧ right.ctl = canon.control (canonNext value) ∧
        ReturnFrame.Occurrence.RetainsBelowTop profile ready checkedDispatch checked checkLabels left ∧
        ReturnFrame.Occurrence.RetainsBelowTop profile ready canonDispatch canonical canonLabels right
    | .refused issue => left.ctl = check.control (checkNext (.error issue)) ∧ right.ctl = canon.control childEntry ∧
        ReturnFrame.Occurrence.RetainsBelowTop profile ready checkedDispatch checked checkLabels left ∧
        ReturnFrame.Occurrence.RetainsBelowTop profile ready canonDispatch canonical canonLabels right

/-- Complete the actual public replies from a reached allocator return.
Only a returned descriptor rejoins both machines. A typed refusal records
the checked completion and rejoins its caller, leaving canonical suspended
at the child-entry program. A canonical trap executes no reply. -/
def CollectionReplies (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (checked canonical : Config (core3 grow) (HostState sig))
    (childEntry : Session grow sig (Ret (core3 grow))) : Prop :=
  ∃ (outcome : PayloadPrefix.Outcome route.output.Result) (checkLabels canonLabels : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)),
    Steps profile ready (specDispatch ready base) checked checkLabels left ∧
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical canonLabels right ∧
    left.store = right.store ∧ PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
    match outcome with
    | .returned value => ∃ before canonBefore,
        (∀ dispatch, Steps profile ready dispatch before [.tau, .tau, .tau] left) ∧
        (∀ dispatch, Steps profile ready dispatch canonBefore [.tau] right) ∧
        left.host = before.host.record (route.reply site.destination site.start.host.nextTicket (.ok value)).1 ∧
        right.host = canonBefore.host ∧ HostFrame.Related.Paired older left right
    | .refused issue => ∃ (before : Config (core3 grow) (HostState sig)) (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
        left.host = before.host.record (route.reply site.destination site.start.host.nextTicket (.error issue)).1 ∧
        (∀ dispatch, Steps profile ready dispatch before [.tau, .tau, .tau] left) ∧ right.ctl = canon.control childEntry
    | .trapped reason => left.ctl = [] ∧ right.ctl = [] ∧ ∃ leading, PayloadPrefix.visible canonLabels = leading ++ [.trap reason]

/-- Stops before the recursive body. A checked preflight refusal resumes its
caller; a bad placement traps the checked machine. Neither executes the
canonical body, whose memory placement is a precondition. -/
inductive RootStop (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) :
    Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | refused (issue : Stored.Endpoints.RecordLower.Issue) {labels}
      (silent : PayloadPrefix.visible labels = [])
      (edge : Transition profile ready base site.start (.give route (.refused issue)) labels (site.refusedReply issue)) :
      RootStop profile ready base site labels (site.refusedReply issue)
  | placementTrap (reason : TrapReason) (count : Nat)
      (edge : Transition profile ready base site.start (.give route (.placementTrap reason))
        (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg site.checked)) :
      RootStop profile ready base site (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg site.checked)

/-- A finite decomposition of a checked run into scheduler segments and
compared gives. The canonical body of a give is itself a plan, so callouts
under a parked allocator can be compared before following the outer suffix.
Local body evidence names the actual replies or stop; it does not supply a
run at the replacement host or the older paired frames. -/
inductive NestedPlan (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) :
    Config (core3 grow) (HostState sig) → Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | segment {start labels finish}
      (run : Steps profile ready (specDispatch ready base) start labels finish) :
      NestedPlan bindings profile ready base start labels finish
  | localSegment {start labels finish}
      (run : PayloadPrefix.LocalSteps profile ready (specDispatch ready base) start labels finish) :
      NestedPlan bindings profile ready base start labels finish
  | closedGive {start count} (callout : LinkedCallback.ClosedGive bindings start)
      (run : Steps profile ready (specDispatch ready base) start (List.replicate count .tau) callout.resume) :
      NestedPlan bindings profile ready base start (List.replicate count .tau) callout.resume
  | syncReady {start task inst thread frames rest}
      (focused : start.ctl = ⟨thread, .prog (.op .hostGet (fun current =>
        syncLiftCandidates task (start.store.instCandidates (ready current) inst))), frames⟩ :: rest)
      (agrees : LinkedCallback.ReadyAgreement ready start inst) :
      NestedPlan bindings profile ready base start [.tau] { start with ctl := ⟨thread,
        .prog (syncLiftCandidates task (start.store.instCandidates (ready start.host) inst)), frames⟩ :: rest }
  | commit {start target index} (resolve : ComponentCall.Delivery.LinkedResolution start target index) :
      NestedPlan bindings profile ready base start (List.replicate 17 .tau) resolve.committed
  | poll {start target index result suffix} (poll : ComponentCall.Delivery.ParkedPoll start target profile)
      (pending : ComponentCall.Delivery.PendingAt start.store target index)
      (branch : BufferBranch start.store poll.memory (flatNat poll.out) result suffix) :
      NestedPlan bindings profile ready base start (pollLabels poll ++ suffix)
        (result.finish (pollReply poll index) { start with store := StepDefs.lockdownSt poll.delivered, ctl := [] })
  | waitBlock {start} (wait : ComponentCall.Delivery.ParkedWait start) (empty : start.store.wsetHasEvent wait.ws = false) :
      NestedPlan bindings profile ready base start (List.replicate 13 .tau) wait.blocked
  | waitReady {start} (wait : ComponentCall.Delivery.ParkedWait start) (available : start.store.wsetHasEvent wait.ws = true)
      (early : Bool) (allowed : Allowed profile (.earlyReturn .waitableSetWait) early) :
      NestedPlan bindings profile ready base start (ComponentCall.Delivery.ParkedWait.readyLabels early)
        (if early then wait.early else wait.blocked)
  | waitResume {initial start} {wait : ComponentCall.Delivery.ParkedWait initial}
      (resume : ComponentCall.Delivery.WaitResume wait start) (saved : start.cont? wait.thread = some wait.saved) :
      NestedPlan bindings profile ready base start (List.replicate 4 .tau) resume.reached
  | waitTake {initial start target index result suffix} {wait : ComponentCall.Delivery.ParkedWait initial}
      (delivery : ComponentCall.Delivery.WaitDelivery wait start profile target)
      (focused : start.ctl = ⟨some wait.thread, .prog wait.takeEvent, .core wait.core wait.next :: wait.segments⟩ :: start.ctl.drop 1)
      (pending : ComponentCall.Delivery.PendingAt start.store target index)
      (branch : BufferBranch delivery.delivered wait.memory (flatNat wait.out) result suffix) :
      NestedPlan bindings profile ready base start (delivery.labels ++ suffix)
        (result.finish (delivery.resumed index) { start with store := StepDefs.lockdownSt delivery.delivered, ctl := [] })
  | cancelReturned {start target index} (cancel : ComponentCall.Delivery.ParkedCancel start target)
      (pending : ComponentCall.Delivery.PendingAt start.store target index)
      (available : ComponentCall.Delivery.CancelAvailable start.store target) :
      NestedPlan bindings profile ready base start (List.replicate 15 .tau) cancel.resumed
  | cancelRequest {start target} (cancel : ComponentCall.Delivery.ParkedCancel start target) (record : Subtask)
      (live : start.store.subtask? target = some record) (unresolved : record.state.resolved = false)
      (notDelivered : record.lenders.isSome = true) (notRequested : record.cancellationRequested = false)
      (notJoined : record.common.wset = none) :
      NestedPlan bindings profile ready base start (List.replicate 14 .tau) (cancel.callbackEntry record ready base)
  | cancelReentry {start target callee} {cancel : ComponentCall.Delivery.ParkedCancel start target}
      (request : ComponentCall.Delivery.TaskCancelAdmission cancel) (mode : ComponentCall.Delivery.TaskCancelReentry request ready)
      (saved : start.cont? request.implicitThread = some callee) :
      NestedPlan bindings profile ready base start (List.replicate request.reentrySteps .tau) (request.reentered callee)
  | cancelCallbackDone {start target} {cancel : ComponentCall.Delivery.ParkedCancel start target}
      (request : ComponentCall.Delivery.StartedCancel cancel) :
      NestedPlan bindings profile ready base start (List.replicate 20 .tau) request.callbackReturned
  | cancelPark {initial start target} {cancel : ComponentCall.Delivery.ParkedCancel initial target}
      (wait : ComponentCall.Delivery.SyncCancelWait cancel start) :
      NestedPlan bindings profile ready base start (List.replicate 5 .tau) wait.blocked
  | cancelResume {initial start target} {cancel : ComponentCall.Delivery.ParkedCancel initial target}
      (resume : ComponentCall.Delivery.SyncCancelResume cancel start) (saved : start.cont? cancel.thread = some cancel.saved) :
      NestedPlan bindings profile ready base start (List.replicate 3 .tau) resume.reached
  | cancelFinish {initial start target rest} (cancel : ComponentCall.Delivery.ParkedCancel initial target) (record : Subtask)
      (focused : start.ctl = ⟨some cancel.thread, .prog (ComponentCall.Delivery.ParkedCancel.finish target),
        .core cancel.core cancel.next :: cancel.segments⟩ :: rest)
      (live : start.store.subtask? target = some record) (resolved : record.state.resolved = true)
      (pending : record.common.pending = some (.subtask target)) :
      NestedPlan bindings profile ready base start (List.replicate 6 .tau) (cancel.finishReply start record.state rest)
  | sequence {start middle finish leading trailing}
      (front : NestedPlan bindings profile ready base start leading middle)
      (back : NestedPlan bindings profile ready base middle trailing finish) :
      NestedPlan bindings profile ready base start (leading ++ trailing) finish
  | rootStop {route} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings) {labels checked}
      (stop : RootStop profile ready base site labels checked) :
      NestedPlan bindings profile ready base site.start labels checked
  | compilerStop {start route issue count} {request : CoreGiveRequest bindings start}
      (selection : request.Selected route) (refused : selection.preflight = .error issue)
      (checked : Steps profile ready (specDispatch ready base) start (List.replicate count .tau) (selection.compilerRefused issue)) :
      NestedPlan bindings profile ready base start (List.replicate count .tau) (selection.compilerRefused issue)
  | give {route} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      {entryLabels checkLabels referenceLabels reached reference checked baseline}
      (entry : Transition profile ready base site.start (.give route .entered) entryLabels site.checked)
      (checkedBody : Steps profile ready (specDispatch ready base) site.checked checkLabels reached)
      (body : NestedPlan bindings profile ready base (site.reference site.referenceReply) (referenceLabels ++ [.tau]) baseline)
      (value : route.output.Result)
      (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible referenceLabels) :
      NestedPlan bindings profile ready base site.start (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked
  | stop {route} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      {entryLabels checkLabels referenceLabels reached reference phase check}
      (entry : Transition profile ready base site.start (.give route .entered) entryLabels site.checked)
      (checkedBody : Steps profile ready (specDispatch ready base) site.checked checkLabels reached)
      (body : NestedPlan bindings profile ready base (site.reference site.referenceReply) referenceLabels reference)
      (stop : GiveStop site check phase referenceLabels reached reference)
      (store : reached.store = reference.store)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible referenceLabels) :
      NestedPlan bindings profile ready base site.start (entryLabels ++ checkLabels) reached

/-- An exact callback trace reaches a dispatch lookup not covered by the
classified window. The prefix retains its specialized edges, and the
source suffix is retained but not replayed. A window ending at a lifted
install does not assert that the subsequent arena read will disagree. -/
def CallbackOverlayCut (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) (start : Config (core3 grow) (HostState sig))
    (labels : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ middle after leading window suffix, labels = leading ++ window ++ suffix ∧
    NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) start leading middle ∧
    Dispatch.LookupCut profile ready bindings callees middle window after ∧
    Steps profile ready (Dispatch.coreOnly ready bindings) after suffix finish

/-- At a fully classified window, retain both the exact dispatcher comparison
and the specialized edges needed to replay against a paired host. -/
def CallbackOverlayPlan (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) (start : Config (core3 grow) (HostState sig))
    (labels : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  Dispatch.Compatible profile ready bindings callees start labels finish ∧
    NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) start labels finish

/-- The comparison at an actual successful return. If a dispatcher window
cannot be transported, the checked/canonical replies from the narrower
comparison remain evidence, not a claim of a live canonical reply. -/
def LinkedGiveExit (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (entryLabels : Trace grow sig) (value : route.output.Result)
    (reached reference : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checkLabels canonLabels checked baseline,
    LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline ∧
    (NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) site.start
        (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked ∨
      CallbackOverlayCut bindings profile ready callees site.checked checkLabels reached ∨
      CallbackOverlayCut bindings profile ready callees (site.reference site.referenceReply) canonLabels reference)

/-- Reasons to stop at an actual live configuration. A local checked stop
has a matched store and observed trace, but does not rejoin (including when
the plan has a later checked-only suffix). Unselected roots are not assumed
to retain their previous tree across earlier compared episodes. -/
inductive NestedCut (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) :
    Config (core3 grow) (HostState sig) → Prop where
  | request {before incoming label after}
      (paired : HostFrame.Related.Paired older before incoming)
      (install : GiveInstall bindings (specDispatch ready base) before label after) :
      NestedCut bindings profile ready base older incoming
  | boundary {before incoming label after reached}
      (paired : HostFrame.Related.Paired older before incoming)
      (cut : HostFrame.Related.Boundary older before incoming label after reached)
      (checkedStep : Step profile ready (specDispatch ready base) before label after)
      (referenceStep : Step profile ready (specDispatch ready (host bindings base)) incoming label reached) :
      NestedCut bindings profile ready base older reached
  | unselected {route incoming} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      (paired : HostFrame.Related.Paired older site.start incoming)
      (selection : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle ≠ some site.tree) :
      NestedCut bindings profile ready base older incoming
  | rootStop {route reached labels checked} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      (stop : RootStop profile ready base site labels checked)
      (installed : HostFrame.Related.Paired older (site.reference site.referenceReply) reached) :
      NestedCut bindings profile ready base older reached
  | compilerLookup {start route incoming} {request : CoreGiveRequest bindings start}
      (selection : request.Selected route) (paired : HostFrame.Related.Paired older start incoming)
      (different : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle ≠ some selection.tree) :
      NestedCut bindings profile ready base older incoming
  | compilerStop {start route issue reached count} {request : CoreGiveRequest bindings start}
      (selection : request.Selected route) (refused : selection.preflight = .error issue)
      (checked : Steps profile ready (specDispatch ready base) start (List.replicate count .tau) (selection.compilerRefused issue))
      (installed : HostFrame.Related.Paired older selection.canonicalPending reached) :
      NestedCut bindings profile ready base older reached
  | publication {start target index incoming} (resolve : ComponentCall.Delivery.LinkedResolution start target index)
      (paired : HostFrame.Related.Paired older start incoming)
      (different : ¬ ∃ writer, incoming.host.writer.register resolve.tree = .ok writer ∧
        writer.accepted.length = resolve.writer.accepted.length) :
      NestedCut bindings profile ready base older incoming
  | cancelReadiness {start target incoming} {cancel : ComponentCall.Delivery.ParkedCancel start target}
      (request : ComponentCall.Delivery.TaskCancelAdmission cancel) (mode : ComponentCall.Delivery.TaskCancelReentry request ready)
      (paired : HostFrame.Related.Paired older start incoming)
      (different : ¬ (request.callee.state = .started →
        request.markedStore.threadReady (ready incoming.host) request.implicitThread = true)) :
      NestedCut bindings profile ready base older incoming
  | stopped {route phase checkLabels referenceLabels liveLabels liveStart checked reference reached check}
      (site : PayloadRoot.Site grow sig route) (stop : GiveStop site check phase referenceLabels checked reference)
      (checkedBody : Steps profile ready (specDispatch ready base) site.checked checkLabels checked)
      (referenceBody : Steps profile ready (specDispatch ready (host bindings base)) liveStart liveLabels reached)
      (paired : HostFrame.Related.Paired older reference reached)
      (store : checked.store = reached.store)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible liveLabels) :
      NestedCut bindings profile ready base older reached

/-- Use the actual public entry cut before asking for a recursive body comparison. -/
inductive RootAdmission (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (body : Prop) : Prop where
  | stopped {labels checked} (stop : RootStop profile ready base site labels checked)
      (plan : NestedPlan bindings profile ready base site.start labels checked) :
      RootAdmission bindings profile ready base site body
  | entered {labels} (entry : Transition profile ready base site.start (.give route .entered) labels site.checked)
      (compared : body) : RootAdmission bindings profile ready base site body

/-- Entry and the recursive success continuation for either public ABI under
the worker's linked dispatcher. This supplies no callback return or progress. -/
def LinkedRootExit (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) (route : GiveEffectRoute) : PayloadRoot.Site grow sig route → Prop :=
  match route with
  | .memory _ => fun site => ∃ depth,
    RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedMemoryBody site depth profile ready bindings (fun reached reference =>
        ∃ entryLabels, LinkedGiveExit bindings profile ready callees site entryLabels () reached reference))
  | .flat _ => fun site => ∃ flatDepth entryDepth,
    RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedFlatResult site flatDepth entryDepth profile ready bindings (fun value reached reference =>
        ∃ entryLabels, LinkedGiveExit bindings profile ready callees site entryLabels value reached reference))

/-- Compiler rejection has no emitter or canonical typed error. Success
supplies the real compiled site, whose later entry guards still execute. -/
inductive ReachedGiveAdmission (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {bindings : List (Binding sig)} {start : Config (core3 grow) (HostState sig)}
    {request : CoreGiveRequest bindings start} {route : GiveEffectRoute} (selection : request.Selected route) : Prop where
  | refused {issue count} (preflight : selection.preflight = .error issue)
      (checked : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        start (List.replicate count .tau) (selection.compilerRefused issue))
  | compiled {tag payload arity children field plan} (preflight : selection.preflight = .ok (field, plan))
      (root : selection.tree = .tag ⟨tag, payload⟩ arity children)
      (linked : (selection.site tag payload arity children field).Linked bindings)
      (exit : LinkedRootExit bindings profile ready callees route (selection.site tag payload arity children field))

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch
