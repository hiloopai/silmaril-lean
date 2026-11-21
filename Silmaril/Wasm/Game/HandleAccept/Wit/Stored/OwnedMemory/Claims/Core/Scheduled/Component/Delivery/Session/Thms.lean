module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Traversal.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Session

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open PayloadPrefix (Cursor)
open Stored.Endpoints.RecordLower

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start middle finish : State grow sig}

theorem Transition.steps {action labels} (edge : Transition profile ready impl start action labels finish) :
    Steps profile ready (specDispatch ready impl) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.transitionSteps edge

section LowerReturn

variable {initial reached : State grow sig} {site : CoreCallSite initial} {request : LowerRequest site}

theorem LowerReturn.cancel_record (returned : LowerReturn request reached) {record : Subtask}
    (live : reached.store.subtask? returned.subtask = some record) :
    returned.cancelInstalled.store.subtask? returned.subtask = some { record with onCancel := returned.cancel } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.lowerCancelRecord returned live

/-- The pending handle insertion changes the index without taking an event. -/
theorem LowerReturn.indexed_record (returned : LowerReturn request reached) {record : Subtask} (index : Nat)
    (live : reached.store.subtask? returned.subtask = some record) :
    (returned.indexedStore index).subtask? returned.subtask = some { record with onCancel := returned.cancel, index := some index } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.lowerIndexedRecord returned index live

/-- Eager delivery releases lends but is not a pending-event take. Neither
this cut nor the pending-result cut has resumed the parked Core yet. -/
theorem LowerReturn.delivered_record (returned : LowerReturn request reached) {record : Subtask}
    (live : reached.store.subtask? returned.subtask = some record) :
    returned.delivered.store.subtask? returned.subtask = some { record with onCancel := returned.cancel, lenders := none } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.lowerDeliveredRecord returned live

end LowerReturn

/-- Soundness for finite classified sessions, including those stopping at a
park or a trap. Neither a scheduler choice nor eventual delivery is promised. -/
theorem Run.steps {actions labels} (path : Run profile ready impl start actions labels finish) :
    Steps profile ready (specDispatch ready impl) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.runSteps path

/-- Compare the actual finite callback from a collection's installed allocator.
The mark may be saved; the return continuation's premise is not used. -/
theorem AllocatorCut.of_collection_prefix {bindings : List (Binding sig)}
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {destination : RecordDestination} {inst : InstId} {type element : Stored.TypeOf}
    {entries : List Stored.Endpoints.RecordLower.Field} {index : Nat} {output : Stored.Lower.Output}
    {left right last : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {checkNext canonNext returned seen protectedReturn}
    (replay : LinkedCallback.CollectionReplayFor profile ready bindings older destination inst type element
      entries index output left right check canon checkNext canonNext returned) :
    let area := ABI.layout destination.width element
    let mode := Stored.Endpoints.RecordLower.CanonicalTree.EntryMode.forOutput destination.width type output
    let first := PayloadPrefix.checkedCollectionResume destination inst entries area index output checkNext
    let second := PayloadPrefix.canonicalCollectionResume destination inst entries area output canonNext mode
    let entered := PayloadPrefix.collectionEntry destination inst area entries.length (Dispatch.coreOnly ready bindings) left check first
    let reference := PayloadPrefix.collectionEntry destination inst area entries.length (Dispatch.coreOnly ready bindings) right canon second
    let changes := ReturnFrame.Extend older first second
    LinkedCallback.PrefixFor profile ready bindings protectedReturn entered seen last →
    (∀ first second, changes first second → protectedReturn first) →
    ∃ other mark checkLabels canonLabels,
      Steps profile ready (Dispatch.coreOnly ready bindings) entered checkLabels last ∧
      Steps profile ready (Dispatch.coreOnly ready bindings) reference canonLabels other ∧
      AllocatorCut profile ready bindings older changes entered reference last other checkLabels canonLabels mark :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.collectionAllocatorPrefix replay

/-- The collection installation itself needs no host-hook agreement: the
actual reads and realloc request reach the same allocator under the overlay. -/
theorem AllocatorCut.collection_install {bindings : List (Binding sig)} {callees : List (Callee sig)}
    {destination : RecordDestination} {inst : InstId} {type element : Stored.TypeOf}
    {entries : List Field} {index : Nat} {output : Stored.Lower.Output}
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {checkNext canonNext}
    (width : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (prepared : Stored.OwnedMemory.Claims.Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = check.control (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let area := ABI.layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width type output
    let first := PayloadPrefix.checkedCollectionResume destination inst entries area index output checkNext
    let second := PayloadPrefix.canonicalCollectionResume destination inst entries area output canonNext mode
    let entered := PayloadPrefix.collectionEntry destination inst area entries.length (Dispatch.coreOnly ready bindings) left check first
    let reference := PayloadPrefix.collectionEntry destination inst area entries.length (Dispatch.coreOnly ready bindings) right canon second
    Steps profile ready (Dispatch.linked ready bindings callees) left [.tau, .tau, .tau] entered ∧
      Steps profile ready (Dispatch.linked ready bindings callees) right [.tau, .tau] reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.collectionInstallLinked
    width prepared checkAt canonAt

/-- A saved mark identifies the original installed segments, not merely
two syntactically equal return programs elsewhere in the stacks. -/
theorem AllocatorCut.saved_segments {bindings : List (Binding sig)} {older changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right reached reference : State grow sig} {checkLabels canonLabels slot depth}
    (cut : AllocatorCut profile ready bindings older changes left right reached reference checkLabels canonLabels (some (.saved slot depth))) :
    ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage reached) (.saved slot depth) =
      ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage left) (.active 0 0) ∧
    ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage reference) (.saved slot depth) =
      ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage right) (.active 0 0) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.allocatorSaved cut

/-- Enter the finite session relation at an observed allocator cut. Keep the
actual canonical prefix and its visible labels even when no result returned. -/
theorem AllocatorCut.session {route : GiveEffectRoute} {bindings : List (Binding sig)} {callees : List (Callee sig)}
    {site : PayloadRoot.Site grow sig route} {older changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {beforeCheck beforeCanon left right reached reference : State grow sig}
    {checkEntryLabels canonEntryLabels checkLabels canonLabels mark}
    (cut : AllocatorCut profile ready bindings older changes left right reached reference checkLabels canonLabels mark)
    (checkEntry : Dispatch.Compatible profile ready bindings callees site.checked checkEntryLabels beforeCheck)
    (canonEntry : Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonEntryLabels beforeCanon)
    (seenEntry : PayloadPrefix.visible checkEntryLabels = PayloadPrefix.visible canonEntryLabels)
    (checkInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCheck [.tau, .tau, .tau] left)
    (canonInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCanon [.tau, .tau] right)
    (checked : Dispatch.Compatible profile ready bindings callees left checkLabels reached)
    (canonical : Dispatch.Compatible profile ready bindings callees right canonLabels reference) :
    let checkTrace := checkEntryLabels ++ [.tau, .tau, .tau] ++ checkLabels
    let canonTrace := canonEntryLabels ++ [.tau, .tau] ++ canonLabels
    Transition profile ready (hostWithComponent bindings callees) site.checked (.give route (.allocatorPrefix mark)) checkTrace reached ∧
      Steps profile ready (Dispatch.linked ready bindings callees) (site.reference site.referenceReply) canonTrace reference ∧
      PayloadPrefix.visible checkTrace = PayloadPrefix.visible canonTrace :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.allocatorSession
    checkEntry canonEntry seenEntry checkInstall canonInstall checked canonical cut

/-- Use an actual paired compiler-body cut, including a natural allocator
return from the collection visit theorem. A live typed refusal
leaves the canonical side at its reached prefix. A trap retains the
reached locked-down store, with the actual trap label on both sides. -/
theorem GiveBodyCut.of_reaches {bindings : List (Binding sig)} {callees : List (Callee sig)} {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) {check canon : Cursor (E := core3 grow) (HostState sig)} {keep}
    (path : PayloadPrefix.ReachesKeeping profile ready (Dispatch.coreOnly ready bindings) keep site.checked
      (site.reference site.referenceReply) check canon site.reply site.referenceReply)
    (dispatch : GiveCutDispatch profile ready bindings callees site) :
    GiveBodyCut profile ready bindings callees site check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.giveBodyCut site path dispatch

/-- At the collection return, use the selected bounds/claim branch and its
actual traces. In particular, a late range trap is not a placement trap. -/
theorem GiveBodyCut.of_collection_return {bindings : List (Binding sig)} {callees : List (Callee sig)} {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {type : Stored.TypeOf} {area : ABI.Layout} {entries : List Stored.Endpoints.RecordLower.Field}
    {index pointer : Nat} {left right last : State grow sig} {check : Cursor (E := core3 grow) (HostState sig)}
    {seen checkLabels canonLabels}
    (entry : Steps profile ready (Dispatch.coreOnly ready bindings) site.checked checkLabels left)
    (referenceEntry : Steps profile ready (Dispatch.coreOnly ready bindings) (site.reference site.referenceReply) canonLabels right)
    (seenEntry : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
    (cut : LinkedCallback.CollectionVisit.Outcome profile ready bindings older site.destination site.inst type area entries index pointer
      route.output left right last check site.reply site.referenceReply seen
      (LinkedCallback.CollectionVisit.reachesNext profile ready bindings left.store site.reply site.referenceReply))
    (dispatch : GiveCutDispatch profile ready bindings callees site) :
    ∃ canon, GiveBodyCut profile ready bindings callees site check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.giveCollectionCut
    site entry referenceEntry seenEntry cut dispatch

/-- Closed reached traces need no component-function hook agreement. -/
theorem GiveCutDispatch.of_closed {bindings : List (Binding sig)} {callees : List (Callee sig)} {route : GiveEffectRoute}
    {site : PayloadRoot.Site grow sig route}
    (closed : ∀ {checkLabels canonLabels reached reference check phase},
      GiveStop site check phase canonLabels reached reference →
      Steps profile ready (Dispatch.coreOnly ready bindings) site.checked checkLabels reached →
      Steps profile ready (Dispatch.coreOnly ready bindings) (site.reference site.referenceReply) canonLabels reference →
      Dispatch.ClosedThrough profile ready bindings site.checked checkLabels reached ∧
      Dispatch.ClosedThrough profile ready bindings (site.reference site.referenceReply) canonLabels reference) :
    GiveCutDispatch profile ready bindings callees site := fun stop _ _ checked canonical =>
  let paths := closed stop checked canonical
  ⟨Dispatch.Compatible.of_closed checked paths.1, Dispatch.Compatible.of_closed canonical paths.2⟩

/-- The original marked Core occurrence can receive the checked refusal.
This records the typed completion on the reached host, does not roll back
earlier effects, and has no matching canonical reply. -/
theorem Transition.give_refusal_reply {bindings : List (Binding sig)} {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) {check : Cursor (E := core3 grow) (HostState sig)} {issue labels}
    (control : start.ctl = check.control (site.reply (.error issue)))
    (path : ReturnFrame.Occurrence.Prefix profile ready (Dispatch.coreOnly ready bindings)
      site.checked (.active 0 0) labels start (.active 0 0)) :
    ∃ segments, Transition profile ready impl start (.give route (.refusalReplied issue)) [.tau, .tau, .tau]
      (refusedBodyReply site start check segments issue) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.giveRefusalReply site control path

/-- A host invocation of a reached lifted export enters the real canonical
lift with its freshly allocated caller and original host return frame. Caller
allocation and host nesting updates do not change the selected function slot. -/
theorem Run.invoke_lifted {call func args core fnType opts inst}
    (hostReady : StepDefs.HostReadyCfg start) (fresh : ∀ entry ∈ start.pending, entry.1 ≠ call)
    (lookup : start.store.func? func = some (.lifted core fnType opts inst)) :
    Run profile ready impl start [.invoke call func, .invokePrologue call func, .liftedLookup func (invokeCaller start)]
      [.host (.invoke call func args), .tau, .tau, .tau, .tau, .tau]
      (invokeLift start call func args core fnType opts inst) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.invokeLifted hostReady fresh lookup

theorem Run.append {first second leading trailing} (left : Run profile ready impl start first leading middle)
    (right : Run profile ready impl middle second trailing finish) :
    Run profile ready impl start (first ++ second) (leading ++ trailing) finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.runAppend left right

/-- Both dispatchers follow the same selected K1 continuation and read the
task at the reached store. This branch does not deliver a pending cancel. -/
theorem K1Resume.linked_admission {atWait atHost : State grow sig} {thread : ThreadId} {task : TaskId}
    {wait : K1Wait atWait thread task} (resume : K1Resume wait atHost ready profile)
    {record : Task (core3 grow)} (live : resume.reached.store.task? task = some record)
    (notPending : record.state ≠ .pendingCancel) (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig)) :
    Steps profile ready (Dispatch.coreOnly ready bindings) atHost (resume.labels ++ [.tau, .tau]) resume.admitted ∧
      Steps profile ready (Dispatch.linked ready bindings callees) atHost (resume.labels ++ [.tau, .tau]) resume.admitted :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.k1ResumePair resume live notPending bindings callees

/-- A parked prefix can end before selection. If selected and not cancelled,
extend the run with the resume and live admission as separate actions. -/
theorem Run.resume_k1 {atWait : State grow sig} {thread : ThreadId} {task : TaskId}
    {wait : K1Wait atWait thread task} (resume : K1Resume wait middle ready profile) {actions labels}
    (run : Run profile ready impl start actions labels middle) {record : Task (core3 grow)}
    (live : resume.reached.store.task? task = some record) (notPending : record.state ≠ .pendingCancel) :
    Run profile ready impl start (actions ++ [.k1Resume thread, .k1Admit task]) (labels ++ (resume.labels ++ [.tau, .tau])) resume.admitted :=
  run.append (.next (.k1Resume resume) (.next (.k1Admit resume live notPending) (.stop _)))

/-- Register the resumed worker and reach the new `onStart` call. The live
instance controls registration capacity and the current task selects the caller. -/
theorem K1LiftStart.start_steps {atGate atHost : State grow sig} {thread : ThreadId} {task : TaskId}
    {entry : K1GateEntry atGate thread task} {resume : K1Resume entry.wait atHost ready profile}
    (handoff : K1LiftStart resume) :
    Steps profile ready (specDispatch ready impl) resume.admitted handoff.labels handoff.onStart :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.k1StartLift handoff

/-- Join selected resumption, the live cancellation check and registration on
both closed dispatchers. The actual `onStart` request is the next cut. -/
theorem K1LiftStart.linked_start {atGate atHost : State grow sig} {thread : ThreadId} {task : TaskId}
    {entry : K1GateEntry atGate thread task} {resume : K1Resume entry.wait atHost ready profile}
    (handoff : K1LiftStart resume) (notPending : handoff.record.state ≠ .pendingCancel)
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig)) :
    let labels := (resume.labels ++ [.tau, .tau]) ++ handoff.labels
    Steps profile ready (Dispatch.coreOnly ready bindings) atHost labels handoff.onStart ∧
      Steps profile ready (Dispatch.linked ready bindings callees) atHost labels handoff.onStart :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.k1LiftStartPair handoff notPending bindings callees

/-- Extend a finite run that reached the original lower continuation. The
result is ready to reply; it has not popped the saved Core caller. -/
theorem Run.finish_pending_lower {initial reached : State grow sig} {site : CoreCallSite initial} {request : LowerRequest site}
    {actions labels} (run : Run profile ready impl start actions labels reached) (returned : LowerReturn request reached)
    {instance_ nextInstance : InstState} {index : Nat} {record : Subtask} (asyncLower : request.opts.async_ = true)
    (recordLive : reached.store.subtask? returned.subtask = some record) (unresolved : record.state.resolved = false)
    (live : returned.cancelInstalled.store.inst? request.inst = some instance_)
    (room : instance_.addHandle? (.waitable (.subtask returned.subtask)) = some (index, nextInstance)) :
    Run profile ready impl start (actions ++ [.lowerInstallCancel returned.subtask, .lowerPending returned.subtask index])
      (labels ++ [.tau, .tau, .tau, .tau, .tau, .tau])
      (returned.pending { record with onCancel := returned.cancel, index := some index } index) :=
  run.append (.next (.lowerInstallCancel returned) (.next (.lowerPending returned asyncLower recordLive unresolved live room) (.stop _)))

theorem Run.finish_eager_lower {initial reached : State grow sig} {site : CoreCallSite initial} {request : LowerRequest site}
    {actions labels} (run : Run profile ready impl start actions labels reached) (returned : LowerReturn request reached)
    (asyncLower : request.opts.async_ = true) (resolved : returned.cancelInstalled.store.subtaskResolved returned.subtask = true) :
    Run profile ready impl start (actions ++ [.lowerInstallCancel returned.subtask, .lowerEagerDelivery returned.subtask])
      (labels ++ [.tau, .tau, .tau, .tau]) returned.delivered :=
  run.append (.next (.lowerInstallCancel returned) (.next (.lowerEagerDelivery returned asyncLower resolved) (.stop _)))

/-- The actual implicit-thread install and forced resume take five silent
steps under either dispatcher. The fresh thread has no waiting condition. -/
theorem LiftSite.launch_steps (site : LiftSite grow sig) :
    Steps profile ready (specDispatch ready impl) site.start [.tau, .tau, .tau, .tau, .tau] site.launched :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.liftLaunchSteps site

theorem LiftSite.live_task (site : LiftSite grow sig) :
    site.launched.store.task? site.storeAndTask.2 = some (liftTaskData site.fnType site.opts site.inst site.caller) :=
  ArenaField.get?_alloc_self ArenaField.tasks site.start.store (liftTaskData site.fnType site.opts site.inst site.caller)

/-- The launch supplies the active worker and its fresh live task to the
actual K1 gate. The backpressure and instance are read, not assumed away. -/
theorem LiftSite.k1_gate (site : LiftSite grow sig) {instance_ : InstState}
    (live : site.start.store.inst? site.inst = some instance_) (asyncMode : site.fnType.async_ = true)
    (gated : (instance_.hasBackpressure (liftTaskData site.fnType site.opts site.inst site.caller).needsExclusive ||
      decide (instance_.numWaitingToEnter > 0)) = true) :
    ∃ entry : K1GateEntry site.launched site.storeAndThread.2 site.storeAndTask.2,
      Steps profile ready (specDispatch ready impl) site.launched (List.replicate 4 .tau) entry.waitingEntry ∧
      entry.wait.next false = .pure .unit ∧ entry.wait.segments = [] ∧ entry.next = liftAdmissionTail site.storeAndTask.2 site.core :=
  lift_k1_gate site.core _ instance_ _ rfl site.live_task asyncMode live gated

/-- A real K1 park in a nested async lift yields the fresh task's cancel
handle to the original lower. The worker stays saved, and the unstarted
subtask comes from the original allocation, not a post-park assumption. -/
theorem LowerRequest.k1_parent {site : CoreCallSite start} (request : LowerRequest site) {core fnType opts inst instance_}
    (live : start.store.inst? inst = some instance_) (asyncMode : fnType.async_ = true)
    (pressure : instance_.hasBackpressure (liftTaskData fnType opts inst request.storeAndCaller.2).needsExclusive = true) :
    let lift := request.lifted core fnType opts inst
    ∃ (entry : K1GateEntry lift.launched lift.storeAndThread.2 lift.storeAndTask.2)
      (returned : LowerReturn request entry.wait.blocked),
      Steps profile ready (specDispatch ready impl) lift.start (List.replicate 14 .tau) entry.wait.blocked ∧
      returned.cancel = .task lift.storeAndTask.2 ∧
      entry.wait.blocked.store.subtask? returned.subtask = some { inst := request.inst } ∧
      returned.cancelInstalled.cont? lift.storeAndThread.2 = some entry.wait.saved ∧
      returned.cancelInstalled.store.inst? request.inst = (start.store.inst? request.inst).map
        (fun caller => if inst = request.inst then caller.incWaitingToEnter else caller) ∧
      entry.next = liftAdmissionTail lift.storeAndTask.2 core :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.lowerK1Parent request live asyncMode pressure

/-- A pending reply returns the index selected by the original caller's
handle table. Even a same-instance K1 park only increments the wait count
before insertion; the callee stays saved and its pending event is untouched. -/
theorem LowerRequest.k1_pending_reply {site : CoreCallSite start} (request : LowerRequest site)
    {core fnType opts inst} {instance_ caller : InstState} {index : Nat}
    (live : start.store.inst? inst = some instance_) (asyncMode : fnType.async_ = true)
    (pressure : instance_.hasBackpressure (liftTaskData fnType opts inst request.storeAndCaller.2).needsExclusive = true)
    (asyncLower : request.opts.async_ = true) (callerLive : start.store.inst? request.inst = some caller)
    (room : (caller.handles.add? (.waitable (.subtask request.storeAndSubtask.2))).map Prod.fst = some index) :
    let lift := request.lifted core fnType opts inst
    let record : Subtask := { inst := request.inst, onCancel := .task lift.storeAndTask.2, index := some index }
    ∃ (entry : K1GateEntry lift.launched lift.storeAndThread.2 lift.storeAndTask.2)
      (returned : LowerReturn request entry.wait.blocked),
      Steps profile ready (specDispatch ready impl) lift.start (List.replicate 21 .tau) (returned.pendingReply record index) ∧
      (returned.pendingReply record index).cont? lift.storeAndThread.2 = some entry.wait.saved ∧
      (returned.pendingReply record index).store.subtask? returned.subtask = some record ∧
      entry.next = liftAdmissionTail lift.storeAndTask.2 core :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.lowerK1PendingReply
    request live asyncMode pressure asyncLower callerLive room

/-- Full capacity traps after the same K1 park and cancellation-handle
installation, without returning an index or running the parked caller. -/
theorem LowerRequest.k1_full_trap {site : CoreCallSite start} (request : LowerRequest site)
    {core fnType opts inst} {instance_ caller : InstState}
    (live : start.store.inst? inst = some instance_) (asyncMode : fnType.async_ = true)
    (pressure : instance_.hasBackpressure (liftTaskData fnType opts inst request.storeAndCaller.2).needsExclusive = true)
    (asyncLower : request.opts.async_ = true) (callerLive : start.store.inst? request.inst = some caller)
    (full : caller.handles.add? (.waitable (.subtask request.storeAndSubtask.2)) = none) :
    let lift := request.lifted core fnType opts inst
    ∃ (entry : K1GateEntry lift.launched lift.storeAndThread.2 lift.storeAndTask.2)
      (returned : LowerReturn request entry.wait.blocked),
      Steps profile ready (specDispatch ready impl) lift.start (List.replicate 18 .tau ++ [.trap .tableFull])
        (StepDefs.trapCfg returned.tableFull) ∧
      (StepDefs.trapCfg returned.tableFull).store.subtask? returned.subtask =
        some { inst := request.inst, onCancel := .task lift.storeAndTask.2 } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.lowerK1FullTrap
    request live asyncMode pressure asyncLower callerLive full

/-- A host invocation starts the actual lift body and leaves the parent
continuation pending. It does not assume the body returns or delivers. -/
theorem Run.invoke_launched {call func args core fnType opts inst}
    (hostReady : StepDefs.HostReadyCfg start) (fresh : ∀ entry ∈ start.pending, entry.1 ≠ call)
    (lookup : start.store.func? func = some (.lifted core fnType opts inst)) :
    let site := LiftSite.ofInvoke start call func args core fnType opts inst
    Run profile ready impl start
      [.invoke call func, .invokePrologue call func, .liftedLookup func (invokeCaller start),
        .liftLaunch site.storeAndTask.2 site.storeAndThread.2]
      (.host (.invoke call func args) :: List.replicate 10 .tau) site.launched :=
  (Run.invoke_lifted hostReady fresh lookup).append
    (.next (.liftLaunch (LiftSite.ofInvoke start call func args core fnType opts inst)) (.stop _))

/-- The reached direct gate checks registration on the post-lock instance
and marks the task started before asking for the caller's arguments. -/
theorem LiftSite.admission_steps (site : LiftSite grow sig) (admission : LiftAdmission site) :
    Steps profile ready (specDispatch ready impl) site.launched (List.replicate site.admissionLength .tau) site.onStart :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.liftAdmission site admission

/-- The actual top-level caller supplies the original arguments and the
start observation. This cut precedes canonical argument lowering. -/
theorem Run.invoke_arguments {call func args core fnType opts inst}
    (hostReady : StepDefs.HostReadyCfg start) (fresh : ∀ entry ∈ start.pending, entry.1 ≠ call)
    (lookup : start.store.func? func = some (.lifted core fnType opts inst))
    (admission : LiftAdmission (LiftSite.ofInvoke start call func args core fnType opts inst)) :
    let site := LiftSite.ofInvoke start call func args core fnType opts inst
    Run profile ready impl start
      ([.invoke call func, .invokePrologue call func, .liftedLookup func (invokeCaller start),
        .liftLaunch site.storeAndTask.2 site.storeAndThread.2] ++
        [.liftAdmit site.storeAndTask.2 site.storeAndThread.2, .liftArguments call])
      ((.host (.invoke call func args) :: List.replicate 10 .tau) ++
        (List.replicate site.admissionLength .tau ++ [.tau, .tau, .obs (.started call), .tau]))
      (site.withArguments args) :=
  (Run.invoke_launched hostReady fresh lookup).append
    (.next (.liftAdmit _ admission)
      (.next (.liftArguments _ (ArenaField.get?_alloc_self ArenaField.callers start.store (.host call args 0))) (.stop _)))

/-- A run through the original empty-argument handoff reaches the actual Core
activation in two more steps, retaining the pending parent continuation. It
does not assume that the Core activation terminates or replies. -/
theorem Run.enter_empty_core {site : LiftSite grow sig} {actions labels}
    (run : Run profile ready impl start actions labels (site.withArguments []))
    (empty : paramTypes site.registeredTask.ft = []) :
    ∃ next, Steps profile ready (specDispatch ready impl) start (labels ++ [.tau, .tau]) (site.coreEntered [] next) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.runEmptyCore run empty

/-- Direct Boolean and unsigned word parameters are lowered by the original canonical
program after the live width read. No argument effect needs an open hook, and the reached
Core activation is a composable session cut. Spill and allocating arguments are separate. -/
theorem Run.enter_direct_core {site : LiftSite grow sig} {actions labels} (args : List DirectArgument)
    (run : Run profile ready impl start actions labels (site.withArguments (args.map DirectArgument.value)))
    (schema : paramTypes site.registeredTask.ft = args.map DirectArgument.type)
    (fits : args.length ≤ ABI.maxFlatParams) :
    ∃ next, Run profile ready impl start (actions ++ [.coreEnter site.storeAndThread.2])
      (labels ++ [.tau, .tau]) (site.coreEntered (args.map DirectArgument.flat) next) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.runDirectCore args run schema fits

/-- Park the actual Core continuation and read the live caller and store. An entry
denial focuses the canonical trap, rather than executing the body or erasing the caller. -/
theorem Run.enter_core_callout {actions labels}
    (run : Run profile ready impl start actions labels middle) (site : CoreCallSite middle) :
    Run profile ready impl start (actions ++ [.coreCallout]) (labels ++ [.tau, .tau, .tau])
      (site.reached ready impl) :=
  run.append (.next (.coreCallout site) (.stop _))

/-- Both dispatchers follow the same reached Core request through its actual
entry check. The body is only installed: later open requests must be classified separately. -/
theorem CoreCallSite.linked_entry (site : CoreCallSite start) (bindings : List (Binding sig)) (callees : List (Callee sig)) :
    Steps profile ready (Dispatch.coreOnly ready bindings) start [.tau, .tau, .tau] (site.reached ready (host bindings)) ∧
      Steps profile ready (Dispatch.linked ready bindings callees) start [.tau, .tau, .tau] (site.reached ready (host bindings)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.coreCalloutPair site bindings callees

/-- Allocate the actual subtask and caller from the live store, stopping before
the callee can run. The parked Core frame and the real lower suffix remain in place. -/
theorem LowerRequest.allocate_steps {site : CoreCallSite start} (request : LowerRequest site) {instance_ : InstState}
    (live : start.store.inst? request.inst = some instance_) (allowed : instance_.mayLeave = true) :
    Steps profile ready (specDispatch ready impl) (site.reached ready impl)
      [.tau, .tau, .tau, .tau, .tau] request.allocated :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.lowerAllocate request live allowed

theorem Run.allocate_lowered {site : CoreCallSite middle} {actions labels}
    (run : Run profile ready impl start actions labels (site.reached ready impl))
    (request : LowerRequest site) {instance_ : InstState}
    (live : middle.store.inst? request.inst = some instance_) (allowed : instance_.mayLeave = true) :
    Run profile ready impl start (actions ++ [.lowerAllocate request.storeAndSubtask.2 request.storeAndCaller.2])
      (labels ++ [.tau, .tau, .tau, .tau, .tau]) request.allocated :=
  run.append (.next (.lowerAllocate request live allowed) (.stop _))

/-- The allocated caller is still at position zero and binds the original
flat arguments to the fresh subtask's borrow scope. -/
theorem LowerRequest.live_caller {site : CoreCallSite start} (request : LowerRequest site) :
    ArenaField.callers.get? request.allocated.store request.storeAndCaller.2 = some request.callerData :=
  ArenaField.get?_alloc_self ArenaField.callers request.storeAndSubtask.1 request.callerData

/-- Both dispatchers reach the lift selected by the live function slot,
with the genuine return continuation above the same parked Core frame. -/
theorem LowerRequest.linked_lift {site : CoreCallSite start} (request : LowerRequest site)
    (bindings : List (Binding sig)) (callees : List (Callee sig)) {instance_ : InstState} {core fnType opts inst}
    (live : start.store.inst? request.inst = some instance_) (allowed : instance_.mayLeave = true)
    (lookup : start.store.func? request.callee = some (.lifted core fnType opts inst)) :
    Steps profile ready (Dispatch.coreOnly ready bindings) start (List.replicate 10 .tau)
        (request.lifted core fnType opts inst).start ∧
      Steps profile ready (Dispatch.linked ready bindings callees) start (List.replicate 10 .tau)
        (request.lifted core fnType opts inst).start :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.lowerLinkedLift request bindings callees live allowed lookup

/-- Extend the session through the actual lower request and the selected lift. -/
theorem Run.enter_lowered_lift {site : CoreCallSite middle} {actions labels}
    (run : Run profile ready impl start actions labels middle)
    (request : LowerRequest site) {instance_ : InstState} {core fnType opts inst}
    (live : middle.store.inst? request.inst = some instance_) (allowed : instance_.mayLeave = true)
    (lookup : middle.store.func? request.callee = some (.lifted core fnType opts inst)) :
    Run profile ready impl start
      (actions ++ [.coreCallout, .lowerAllocate request.storeAndSubtask.2 request.storeAndCaller.2,
        .liftedLookup request.callee request.storeAndCaller.2]) (labels ++ List.replicate 10 .tau)
      (request.lifted core fnType opts inst).start :=
  run.append (.next (.coreCallout site) (.next (.lowerAllocate request live allowed)
    (.next (.liftedLookup (start := request.allocated) rfl lookup) (.stop _))))

/-- Dispatch the actual lower caller's start request. An unindexed record
does not touch its event; an indexed one replaces the pending event before
marking the subtask started. The remaining program lifts the original cursor. -/
theorem LowerStartAt.handoff_steps {site : OnStartSite start} (handoff : LowerStartAt site) :
    Steps profile ready (specDispatch ready impl) start (List.replicate handoff.steps .tau) handoff.reading :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.lowerStart handoff

theorem LowerStartAt.started_record {site : OnStartSite start} (handoff : LowerStartAt site) :
    handoff.reading.store.subtask? handoff.subtask = some handoff.startedRecord :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.lowerStartRecord handoff

/-- The reached start request uses only the arena-backed canonical caller program. -/
theorem LowerStartAt.linked_handoff {site : OnStartSite start} (handoff : LowerStartAt site)
    (bindings : List (Binding sig)) (callees : List (Callee sig)) :
    Steps profile ready (Dispatch.coreOnly ready bindings) start (List.replicate handoff.steps .tau) handoff.reading ∧
      Steps profile ready (Dispatch.linked ready bindings callees) start (List.replicate handoff.steps .tau) handoff.reading :=
  ⟨handoff.handoff_steps, handoff.handoff_steps⟩

/-- Registration frames the live lower caller and subtask on the selected K1
path. `onStart` replaces the pending slot only when the live subtask is indexed. -/
theorem K1LiftStart.linked_lower_handoff {atGate atHost : State grow sig} {thread : ThreadId} {task : TaskId}
    {entry : K1GateEntry atGate thread task} {resume : K1Resume entry.wait atHost ready profile}
    (handoff : K1LiftStart resume) (notPending : handoff.record.state ≠ .pendingCancel)
    {subtask context flat pos fnType maxParams maxResults subtaskRecord}
    (caller : ArenaField.callers.get? atHost.store handoff.record.caller =
      some (.lower subtask context flat pos fnType maxParams maxResults))
    (live : atHost.store.subtask? subtask = some subtaskRecord)
    (bindings : List (Binding sig)) (callees : List (Callee sig)) :
    ∃ cursor : LowerStartAt handoff.startCursor,
      let labels := ((resume.labels ++ [.tau, .tau]) ++ handoff.labels) ++ List.replicate cursor.steps .tau
      cursor.subtask = subtask ∧ cursor.record = subtaskRecord ∧ cursor.flat = flat ∧ cursor.pos = pos ∧
      cursor.fnType = fnType ∧ cursor.maxParams = maxParams ∧
        Steps profile ready (Dispatch.coreOnly ready bindings) atHost labels cursor.reading ∧
        Steps profile ready (Dispatch.linked ready bindings callees) atHost labels cursor.reading ∧
        cursor.reading.store.subtask? subtask = some cursor.startedRecord :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.k1LowerHandoff
    handoff notPending caller live bindings callees

/-- The closed argument handoff reads the caller width, lifts and commits
exactly the selected words, and enters the real callee on the original activation. -/
theorem LowerStartAt.direct_callee {site : OnStartSite start} (handoff : LowerStartAt site)
    (task : TaskId) (callee : (core3 grow).FuncAddr) (record : Task (core3 grow))
    (body : site.next = liftArgumentsBody .spec .none task callee record) (args : List DirectArgument)
    (callerSchema : handoff.types = args.map DirectArgument.type) (calleeSchema : paramTypes record.ft = args.map DirectArgument.type)
    (callerFits : args.length ≤ handoff.maxParams) (calleeFits : args.length ≤ ABI.maxFlatParams)
    (suffix : List FlatValue) (words : handoff.flat.drop handoff.pos = args.map DirectArgument.flat ++ suffix) :
    ∃ (returned : LowerArgumentReturn handoff handoff.selectedRead), ∃ next,
      returned.cursor.pos = handoff.pos + args.length ∧
      (record.opts.async_ = true → record.opts.callback = none → next = stackfulTail task) ∧
      ∀ impl, Run profile ready impl handoff.reading
        [.lowerReadWidth site.caller, .lowerArgsReturn site.caller, .coreEnter site.thread]
        [.tau, .tau, .tau, .tau, .tau] (site.entered returned.resumed callee (args.map DirectArgument.flat) next) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.runLowerDirect
    handoff task callee record body args callerSchema calleeSchema callerFits calleeFits suffix words

/-- Both dispatchers install the same closed realloc request after the live
cursor update, with the actual spill continuation above the older frames. -/
theorem CalleeArguments.linked_spill_request {site : OnStartSite start} {handoff : LowerStartAt site}
    {reached : State grow sig} {returned : LowerArgumentReturn handoff reached} (args : CalleeArguments returned)
    (spill : ABI.maxFlatParams < (ABI.flattenTypes args.width args.types).length)
    (bindings : List (Binding sig)) (callees : List (Callee sig)) :
    let installed := args.installed (Dispatch.coreOnly ready bindings)
    Steps profile ready (Dispatch.coreOnly ready bindings) reached [.tau, .tau, .tau, .tau] installed ∧
    Steps profile ready (Dispatch.linked ready bindings callees) reached [.tau, .tau, .tau, .tau] installed :=
  ⟨(Run.next (.lowerArgsReturn returned) (.next (.calleeAllocate args spill) (.stop _))).steps,
    (Run.next (.lowerArgsReturn returned) (.next (.calleeAllocate args spill) (.stop _))).steps⟩

/-- A finite closed allocator path need not return. The linked execution
reaches the same configuration and retains the same live or saved occurrence. -/
theorem CalleeArguments.linked_spill_prefix {site : OnStartSite start} {handoff : LowerStartAt site}
    {reached state : State grow sig} {returned : LowerArgumentReturn handoff reached} {args : CalleeArguments returned}
    {bindings : List (Binding sig)} {callees : List (Callee sig)} {labels mark}
    (path : ReturnFrame.Occurrence.Prefix profile ready (Dispatch.coreOnly ready bindings)
      (args.installed (Dispatch.coreOnly ready bindings)) (.active 0 0) labels state mark)
    (closed : Dispatch.ClosedThrough profile ready bindings (args.installed (Dispatch.coreOnly ready bindings)) labels state) :
    ReturnFrame.Occurrence.Prefix profile ready (Dispatch.linked ready bindings callees)
      (args.installed (Dispatch.linked ready bindings callees)) (.active 0 0) labels state mark :=
  Dispatch.occurrence_of_closed path closed

/-- Recognize the return to the original spill occurrence, even if it was
parked and resumed with a different scheduler tail. -/
theorem CalleeSpillReturn.of_occurrence {site : OnStartSite start} {handoff : LowerStartAt site}
    {reached state : State grow sig} {returned : LowerArgumentReturn handoff reached} {args : CalleeArguments returned}
    {labels pointer next segments rest}
    (path : ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready impl)
      (args.installed (specDispatch ready impl)) (.active 0 0) labels state (.active 0 0))
    (focused : state.ctl = ⟨some site.thread, .prog (.pure (.nat pointer)), .prog next :: segments⟩ :: rest) :
    ∃ result : CalleeSpillReturn args state, result.pointer = pointer :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.calleeReachedReturn path focused

/-- A spilled scalar tuple is loaded in ABI field order from the reached memory.
It consumes one caller word before using the same direct callee entry as flat arguments. -/
theorem LowerStartAt.spilled_scalar_callee {site : OnStartSite start} (handoff : LowerStartAt site)
    (task : TaskId) (callee : (core3 grow).FuncAddr) (record : Task (core3 grow))
    (body : site.next = liftArgumentsBody .spec .none task callee record) (args : List DirectArgument)
    (callerSchema : handoff.types = args.map DirectArgument.type) (calleeSchema : paramTypes record.ft = args.map DirectArgument.type)
    (callerSpills : handoff.maxParams < args.length) (calleeFits : args.length ≤ ABI.maxFlatParams)
    {pointer : FlatValue} {memory : (core3 grow).MemAddr} {size : Nat}
    (found : handoff.flat[handoff.pos]? = some pointer)
    (aligned : flatNat pointer = ABI.alignTo (flatNat pointer) (handoff.spillLayout handoff.readWidth).alignment)
    (selected : handoff.context.opts.memory = some memory)
    (sized : (core3 grow).memSize? handoff.selectedRead.store.core memory = some size)
    (fits : flatNat pointer + (handoff.spillLayout handoff.readWidth).size ≤ size)
    (fields : ScalarSpill handoff.selectedRead.store memory handoff.readWidth args (flatNat pointer)) :
    ∃ (returned : LowerArgumentReturn handoff (handoff.spillLoaded (args.map DirectArgument.value))), ∃ next,
      returned.cursor.pos = handoff.pos + 1 ∧
      (record.opts.async_ = true → record.opts.callback = none → next = stackfulTail task) ∧
      ∀ impl, Run profile ready impl handoff.reading
        [.lowerReadWidth site.caller, .lowerSpill site.caller, .lowerLoadScalars site.caller, .lowerArgsReturn site.caller,
          .coreEnter site.thread]
        ([.tau, .tau] ++ (List.replicate args.length .tau ++ [.tau, .tau, .tau, .tau]))
        (site.entered returned.resumed callee (args.map DirectArgument.flat) next) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.runLowerSpilledScalars
    handoff task callee record body args callerSchema calleeSchema callerSpills calleeFits found aligned selected sized fits fields

/-- A selected K1 worker reaches its direct callee under both dispatchers.
Unlike the initially admitted path, the retained tail is the reached tick's tail. -/
theorem K1LiftStart.linked_direct_callee {atGate atHost : State grow sig} {thread : ThreadId} {task : TaskId}
    {entry : K1GateEntry atGate thread task} {resume : K1Resume entry.wait atHost ready profile}
    (handoff : K1LiftStart resume) (notPending : handoff.record.state ≠ .pendingCancel)
    {subtask context flat pos fnType maxParams maxResults subtaskRecord}
    (caller : ArenaField.callers.get? atHost.store handoff.record.caller =
      some (.lower subtask context flat pos fnType maxParams maxResults))
    (live : atHost.store.subtask? subtask = some subtaskRecord)
    (args : List DirectArgument) (callerSchema : paramTypes fnType = args.map DirectArgument.type)
    (calleeSchema : paramTypes handoff.registered.ft = args.map DirectArgument.type)
    (callerFits : args.length ≤ maxParams) (calleeFits : args.length ≤ ABI.maxFlatParams)
    (suffix : List FlatValue) (words : flat.drop pos = args.map DirectArgument.flat ++ suffix)
    (bindings : List (Binding sig)) (callees : List (Callee sig)) :
    ∃ (cursor : LowerStartAt handoff.startCursor) (returned : LowerArgumentReturn cursor cursor.selectedRead), ∃ next,
      let labels := (((resume.labels ++ [.tau, .tau]) ++ handoff.labels) ++ List.replicate cursor.steps .tau) ++
        [.tau, .tau, .tau, .tau, .tau]
      let entered := handoff.startCursor.entered returned.resumed handoff.callee (args.map DirectArgument.flat) next
      returned.cursor.pos = pos + args.length ∧
        (handoff.registered.opts.async_ = true → handoff.registered.opts.callback = none → next = stackfulTail task) ∧
        Steps profile ready (Dispatch.coreOnly ready bindings) atHost labels entered ∧
        Steps profile ready (Dispatch.linked ready bindings callees) atHost labels entered :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.k1LowerDirect
    handoff notPending caller live args callerSchema calleeSchema callerFits calleeFits suffix words bindings callees

/-- Stackful completion does not itself consume or replace the event reached
at Core return, or change that store's caller cursor. -/
theorem StackfulExit.live_records {reached : State grow sig} {site : StackfulReturn reached} (exit : StackfulExit site) :
    exit.finished.store.subtasks = reached.store.subtasks ∧ exit.finished.store.callers = reached.store.callers :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.stackfulFrames exit

/-- Append the closed return, live unregistration and actual worker exit
after any classified finite interleaving that reaches the callee return. -/
theorem Run.finish_stackful {reached : State grow sig} {site : StackfulReturn reached} {actions labels}
    (run : Run profile ready impl start actions labels reached) (exit : StackfulExit site) (empty : site.segments = []) :
    Run profile ready impl start (actions ++ [.stackfulComplete site.taskId, .workerExit site.thread])
      (labels ++ (exit.labels ++ [.tau])) exit.finished := by
  simpa only [List.append_nil] using run.append (.next (.stackfulComplete exit) (.next (.stackfulExit exit empty) (.stop _)))

/-- No independent live-caller or progress-record premise is needed on the
fresh, directly admitted lifted path: lift launch and registration leave both arenas alone. -/
theorem LowerRequest.fresh_start {site : CoreCallSite start} (request : LowerRequest site) {core fnType opts inst} :
    ∃ handoff : LowerStart (request.lifted core fnType opts inst),
      handoff.subtask = request.storeAndSubtask.2 ∧ handoff.record = { inst := request.inst } ∧ handoff.pos = 0 ∧
        handoff.flat = site.args :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.lowerFresh request

theorem Run.start_lowered {site : OnStartSite middle} {actions labels}
    (run : Run profile ready impl start actions labels middle) (handoff : LowerStartAt site) :
    Run profile ready impl start (actions ++ [.lowerStart handoff.subtask handoff.record.index.isSome])
      (labels ++ List.replicate handoff.steps .tau) handoff.reading := by
  simpa only [List.append_nil] using run.append (.next (.lowerStart handoff) (.stop _))

/-- A reached empty parameter list still uses the canonical width read, cursor
update and value return. The subtask update stays in the state entering Core. -/
theorem Run.enter_empty_lowered_core {site : LiftSite grow sig} {actions labels}
    (run : Run profile ready impl start actions labels site.onStart) (handoff : LowerStart site)
    (emptyLower : handoff.fnType.params = []) (emptyLift : paramTypes site.registeredTask.ft = []) :
    ∃ next, Run profile ready impl start (actions ++ [.lowerStart handoff.subtask handoff.record.index.isSome,
      .lowerEmptyArgs site.registeredTask.caller, .coreEnter site.storeAndThread.2])
      (labels ++ (List.replicate handoff.steps .tau ++ [.tau, .tau, .tau, .tau, .tau]))
      (site.coreEnteredAt (site.withLowerValues handoff.reading [] handoff.pos) [] next) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.runLowerEmptyCore run handoff emptyLower emptyLift

/-- The two dispatchers enter the same Core activation from the actual
arena-backed start request. The post-handoff store, not the lift's entry snapshot, is used. -/
theorem LowerStart.linked_empty_core {site : LiftSite grow sig} (handoff : LowerStart site)
    (bindings : List (Binding sig)) (callees : List (Callee sig))
    (emptyLower : handoff.fnType.params = []) (emptyLift : paramTypes site.registeredTask.ft = []) :
    let returned := site.withLowerValues handoff.reading [] handoff.pos
    let labels := List.replicate handoff.steps (.tau : Label (core3 grow) (HostState sig)) ++ [.tau, .tau, .tau, .tau, .tau]
    ∃ next, Steps profile ready (Dispatch.coreOnly ready bindings) site.onStart labels (site.coreEnteredAt returned [] next) ∧
      Steps profile ready (Dispatch.linked ready bindings callees) site.onStart labels (site.coreEnteredAt returned [] next) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.lowerEmptyPair handoff bindings callees emptyLower emptyLift

/-- Actual backpressure makes the launched worker park at K1, even after
incrementing the entry count. The async parent returns the cancellation
handle while that worker is still saved; this is not result delivery. -/
theorem LiftSite.invoke_backpressure {call func args core fnType opts inst instance_}
    (live : start.store.inst? inst = some instance_) (asyncMode : fnType.async_ = true)
    (pressure : instance_.hasBackpressure (liftTaskData (grow := grow) fnType opts inst (invokeCaller start)).needsExclusive = true) :
    let site := LiftSite.ofInvoke start call func args core fnType opts inst
    ∃ (entry : K1GateEntry site.launched site.storeAndThread.2 site.storeAndTask.2) (after : State grow sig),
      Steps profile ready (specDispatch ready impl) site.launched (List.replicate 9 .tau) entry.wait.blocked ∧
      Transition profile ready impl entry.wait.blocked (.invokeReturn (.task site.storeAndTask.2)) [.tau, .tau, .tau] after ∧
      after.cont? site.storeAndThread.2 = some entry.wait.saved :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.invokeBackpressure live asyncMode pressure

/-- The exact record frame is a property only of the classified closed path. -/
theorem Transition.closed_record {target labels}
    (edge : Transition profile ready impl start (.closedCallback target) labels finish) :
    finish.store.subtask? target = start.store.subtask? target :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.closedRecord edge

/-- The state-changing K3 branch is also an edge. It consumes the event and
releases the lenders before it enters the callback; there is no outer reply. -/
theorem Transition.callback_taken {target event labels}
    (edge : Transition profile ready impl start (.callbackTake target event) labels finish) :
    ∃ record, start.store.subtask? target = some record ∧
      finish.store.subtask? target = some { record with common := { record.common with pending := none }, lenders := none } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.takenRecord edge

/-- Add the actual public give guards to a session. A refusal replies on
the checked side; a placement trap keeps its reached locked-down store. -/
theorem Transition.give_root {route : GiveEffectRoute} {bindings : List (Binding sig)}
    (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings) {body : Prop}
    (cut : PayloadRoot.Cut site profile ready bindings body impl) :
    ∃ phase labels finish, Transition profile ready impl site.start (.give route phase) labels finish ∧
      (phase = .entered → finish = site.checked ∧ body) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.giveRoot site linked cut

/-- On a common returning recursive path, add the give to the same linked
session as component delivery. Only the reached body requests need the
dispatcher contract. The original caller pops are independent of the overlay. -/
theorem Transition.give_returned {route : GiveEffectRoute} {bindings : List (Binding sig)} {callees : List (Callee sig)}
    (site : PayloadRoot.Site grow sig route) (value : route.output.Result) {reached reference : State grow sig}
    (comparison : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference)
    (agreement : GiveBodyAgreement profile ready bindings callees site reached reference) :
    ∃ checkLabels canonLabels left right,
      Transition profile ready (hostWithComponent bindings callees) site.checked (.give route .returned)
        (checkLabels ++ [.tau, .tau, .tau]) left ∧
      Steps profile ready (Dispatch.linked ready bindings callees) (site.reference site.referenceReply) (canonLabels ++ [.tau]) right ∧
      PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
      LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference left right :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.giveReturned site value comparison agreement

theorem GiveBodyAgreement.of_closed {route : GiveEffectRoute} {bindings : List (Binding sig)} {callees : List (Callee sig)}
    {site : PayloadRoot.Site grow sig route} {reached reference : State grow sig}
    (closed : ∀ checkLabels canonLabels,
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready (Dispatch.coreOnly ready bindings) site.checked checkLabels reached →
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready (Dispatch.coreOnly ready bindings)
        (site.reference site.referenceReply) canonLabels reference →
      Dispatch.ClosedThrough profile ready bindings site.checked checkLabels reached ∧
      Dispatch.ClosedThrough profile ready bindings (site.reference site.referenceReply) canonLabels reference) :
    GiveBodyAgreement profile ready bindings callees site reached reference := by
  intro checkLabels canonLabels checked canonical
  obtain ⟨check, canon⟩ := closed checkLabels canonLabels checked canonical
  exact ⟨.of_closed (ReturnFrame.Occurrence.prefix_survives (checked 0)).1 check,
    .of_closed (ReturnFrame.Occurrence.prefix_survives (canonical 0)).1 canon⟩

/-- The memory give's public admission and compiler-derived recursive body
are available inside the linked session without any body-dispatch premise
on the admission edge. -/
theorem linked_memory_root {pointer : FlatValue} {bindings : List (Binding sig)} (callees : List (Callee sig))
    (site : PayloadRoot.Site grow sig (.memory pointer)) (linked : site.Linked bindings) :
    ∃ depth phase labels finish,
      Transition profile ready (hostWithComponent bindings callees) site.start (.give (.memory pointer) phase) labels finish ∧
      (phase = .entered → finish = site.checked ∧ LinkedCallback.MemorySequence.ParkedRejoinedMemory site depth profile ready bindings) := by
  obtain ⟨depth, cut⟩ := LinkedCallback.MemorySequence.parked_memory_rejoined (profile := profile) (ready := ready)
    site linked (hostWithComponent bindings callees)
  exact ⟨depth, Transition.give_root site linked cut⟩

/-- The flat give enters the same linked dispatcher; the compiler-derived
flat/body comparison on the entered branch includes indirect entries. -/
theorem linked_flat_root {schema : Stored.TypeOf} {bindings : List (Binding sig)} (callees : List (Callee sig))
    (site : PayloadRoot.Site grow sig (.flat schema)) (linked : site.Linked bindings) :
    ∃ flatDepth entryDepth phase labels finish,
      Transition profile ready (hostWithComponent bindings callees) site.start (.give (.flat schema) phase) labels finish ∧
      (phase = .entered → finish = site.checked ∧
        LinkedCallback.MemorySequence.ParkedRejoinedFlat site flatDepth entryDepth profile ready bindings) := by
  obtain ⟨flatDepth, entryDepth, cut⟩ := LinkedCallback.MemorySequence.parked_flat_rejoined (profile := profile) (ready := ready)
    site linked (hostWithComponent bindings callees)
  exact ⟨flatDepth, entryDepth, Transition.give_root site linked cut⟩

/-- Start an actual synchronous cancel, park its Core caller, allow a finite
classified interleaving, and deliver after the scheduler chooses that saved
occurrence. The returned event need only be pending at the reached tick. -/
theorem Run.started_cancel_delivery {initial atHost : State grow sig} {target : SubtaskId} {index : Nat}
    {cancel : ParkedCancel initial target} (request : StartedCancel cancel) (synchronous : cancel.async_ = false)
    {actions labels} (interleaving : Run profile ready impl (request.syncWait synchronous).blocked actions labels atHost)
    (occurrence : ReturnFrame.Occurrence.ParkedPrefix profile ready (specDispatch ready impl) cancel.thread
      (request.syncWait synchronous).blocked labels atHost)
    (tick : SelectedTick cancel.thread atHost ready profile) (pending : PendingAt atHost.store target index) :
    let resume := SyncCancelResume.afterTick tick tick.waiting
    Run profile ready impl initial
      (.cancelCallbackDone target :: .cancelPark target :: (actions ++ [.tick cancel.thread, .cancelResume target, .cancel target .returned]))
      (List.replicate 20 .tau ++ (List.replicate 5 .tau ++ (labels ++
        (tick.selectionLabels ++ (List.replicate 3 .tau ++ List.replicate 6 .tau))))) resume.delivered :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.startedCancelDelivery
    request synchronous interleaving occurrence tick pending

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
