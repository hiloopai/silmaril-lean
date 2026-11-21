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

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start middle finish : State grow sig}

theorem Transition.steps {action labels} (edge : Transition profile ready impl start action labels finish) :
    Steps profile ready (specDispatch ready impl) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.transitionSteps edge

/-- Soundness for finite classified sessions, including those stopping at a
park or a trap. Neither a scheduler choice nor eventual delivery is promised. -/
theorem Run.steps {actions labels} (path : Run profile ready impl start actions labels finish) :
    Steps profile ready (specDispatch ready impl) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.runSteps path

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
