module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.StringPlan.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open ComponentCall.Delivery.FiniteSession
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind} {ready : HostReady (HostState sig)}
  {bindings : List (Binding sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {start finish incoming : Config (core3 grow) (HostState sig)} {labels : Trace grow sig}
  {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}

theorem NestedPlan.source (plan : NestedPlan bindings profile ready base start labels finish) :
    Steps profile ready (specDispatch ready base) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.source plan

/-- Decompose an actual prefix at its reached foci. Local steps replay fully;
nonlocal steps still go through the live request/read/return classifier. -/
theorem NestedPlan.of_steps (run : Steps profile ready (specDispatch ready base) start labels finish) :
    NestedPlan bindings profile ready base start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.planOfSteps run

/-- Derive a closed reentry edge at the reached caller and binding under the
same component dispatcher used by the worker. No checked body, padding,
or older-frame equality is supplied by the caller of the theorem. -/
theorem linked_closed_give_plan {callees : List (ComponentCall.Callee sig)} (callout : LinkedCallback.ClosedGive bindings start) :
    ∃ count, NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) start
      (List.replicate count .tau) callout.resume :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.closedGivePlan callout rfl

/-- Reuse the allocator's finite callback classification rather than
flattening closed reentries and classified readiness reads into raw steps.
The endpoint may still be parked. Unclassified steps retain the ordinary
live replay boundaries. -/
theorem NestedPlan.of_callback_prefix {protectedReturn}
    (path : LinkedCallback.PrefixFor profile ready bindings protectedReturn start labels finish) :
    ∃ trace, NestedPlan bindings profile ready (Scheduled.host bindings) start trace finish ∧
      PayloadPrefix.visible trace = labels :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.callbackPlan path

/-- Lift the very trace used to track an allocator occurrence, not another
prefix with the same visible labels. The resulting plan still classifies
ordinary steps at the live dispatcher boundary. -/
theorem NestedPlan.of_callback_trace {right reference : Config (core3 grow) (HostState sig)} {referenceLabels}
    (trace : LinkedCallback.ReplayTrace profile ready bindings start labels finish right referenceLabels reference) :
    NestedPlan bindings profile ready (Scheduled.host bindings) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.callbackPlanExact trace

/-- At the reached linked memory give, use the public entry guards and the
compiled recursive body. A preflight refusal becomes a checked reply and a
stopped live canonical prefix, not a canonical error. A placement trap is
also a stopped prefix: canonical store requires valid root placement. -/
theorem linked_memory_admission {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    ∃ depth, RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedRejoinedMemory site depth profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.memoryAdmission site linked

/-- The flat ABI uses the same admission split and the recursive flat body
with its actual memory-emitting descendants. -/
theorem linked_flat_admission {schema : Stored.TypeOf} (site : PayloadRoot.Site grow sig (.flat schema))
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    ∃ flatDepth entryDepth, RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedRejoinedFlat site flatDepth entryDepth profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.flatAdmission site linked

/-- Join a recursive public give's reached checked and canonical bodies to
the actual caller replies. This constructs the replay plan from the compared
paths; it does not assume that a reached nested callout can be replayed. -/
theorem compared_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {entryLabels checkLabels canonLabels reached reference checked baseline} (value : route.output.Result)
    (entry : Transition profile ready base site.start (.give route .entered) entryLabels site.checked)
    (left : Steps profile ready (specDispatch ready base) site.checked checkLabels reached)
    (right : Steps profile ready (specDispatch ready base) (site.reference site.referenceReply) canonLabels reference)
    (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
    (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline) :
    NestedPlan bindings profile ready base site.start (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.comparedGive
    site linked value entry left right seen replies

/-- For either recursive public give that reaches its successful caller
rejoin, build the session plan on the Core binding dispatcher without a
separate child/body plan. Finite checked refusal and trap are not successful
rejoins. When run live, an intervening nested give may still cut the plan. -/
theorem rejoined_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {entryLabels reached reference} (value : route.output.Result)
    (entry : Transition profile ready (Scheduled.host bindings) site.start (.give route .entered) entryLabels site.checked)
    (compared : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference) :
    ∃ checkLabels checked baseline,
      NestedPlan bindings profile ready (Scheduled.host bindings) site.start (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked ∧
      LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.rejoinedGive site linked value entry compared

/-- Classify the successful recursive rejoin under the worker's linked
dispatcher. No agreement premise is needed at ordinary allocation, local
operations or Core callouts. An unequal direct install is exposed at its
actual common-prefix cut, not converted to a refusal or canonical trap. -/
theorem linked_rejoined_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {callees : List (ComponentCall.Callee sig)} {entryLabels reached reference} (value : route.output.Result)
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees)
      site.start (.give route .entered) entryLabels site.checked)
    (compared : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference) :
    ∃ checkLabels canonLabels checked baseline,
      LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline ∧
      (NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) site.start
          (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked ∨
        Dispatch.LookupCut profile ready bindings callees site.checked checkLabels reached ∨
        Dispatch.LookupCut profile ready bindings callees (site.reference site.referenceReply) canonLabels reference) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedRejoinedGive site linked value entry compared

/-- Classify the actual matched body prefix of a typed refusal or canonical
trap. Reaching a refusal does not pop a canonical caller or emit its checked
error there. A canonical trap is compared with its reached store, not the
entry store. Neither branch requires an unvisited callback suffix. -/
theorem linked_stopped_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {callees : List (ComponentCall.Callee sig)} {entryLabels checkLabels canonLabels reached reference check phase}
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees)
      site.start (.give route .entered) entryLabels site.checked)
    (left : Steps profile ready (Dispatch.coreOnly ready bindings) site.checked checkLabels reached)
    (right : Steps profile ready (Dispatch.coreOnly ready bindings) (site.reference site.referenceReply) canonLabels reference)
    (stop : GiveStop site check phase canonLabels reached reference) (store : reached.store = reference.store)
    (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels) :
    NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) site.start
        (entryLabels ++ checkLabels) reached ∨
      Dispatch.LookupCut profile ready bindings callees site.checked checkLabels reached ∨
      Dispatch.LookupCut profile ready bindings callees (site.reference site.referenceReply) canonLabels reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedGiveStop
    site linked entry left right stop store seen

/-- Classify the actual finite callback of a public give while its allocator
occurrence still survives. The mark can be active or saved; there is no
return premise. The observed canonical prefix and the original occurrence
are retained, even if subsequent progress is not known. -/
theorem linked_allocator_cut {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route}
    {callees : List (ComponentCall.Callee sig)} {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {beforeCheck beforeCanon left right reached reference : Config (core3 grow) (HostState sig)}
    {checkEntryLabels canonEntryLabels checkLabels canonLabels mark}
    (cut : AllocatorCut profile ready bindings older changes left right reached reference checkLabels canonLabels (some mark))
    (checkEntry : Dispatch.Compatible profile ready bindings callees site.checked checkEntryLabels beforeCheck)
    (canonEntry : Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonEntryLabels beforeCanon)
    (seenEntry : PayloadPrefix.visible checkEntryLabels = PayloadPrefix.visible canonEntryLabels)
    (checkInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCheck [.tau, .tau, .tau] left)
    (canonInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCanon [.tau, .tau] right) :
    let checkTrace := checkEntryLabels ++ [.tau, .tau, .tau] ++ checkLabels
    let canonTrace := canonEntryLabels ++ [.tau, .tau] ++ canonLabels
    (Transition profile ready (ComponentCall.hostWithComponent bindings callees) site.checked
        (.give route (.allocatorPrefix (some mark))) checkTrace reached ∧
      Steps profile ready (Dispatch.linked ready bindings callees) (site.reference site.referenceReply) canonTrace reference ∧
      PayloadPrefix.visible checkTrace = PayloadPrefix.visible canonTrace) ∨
      Dispatch.LookupCut profile ready bindings callees left checkLabels reached ∨
      Dispatch.LookupCut profile ready bindings callees right canonLabels reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedAllocatorCut
    cut checkEntry canonEntry seenEntry checkInstall canonInstall

/-- A closed local segment replays to the end, even with a different host and
older paired continuations. Each reached focus rules out a give installation,
host read, or pop of a substituted program return. -/
theorem local_segment_replay (run : PayloadPrefix.LocalSteps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ reached, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming labels reached ∧
      HostFrame.Related.Paired older finish reached :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.replayLocal run paired

/-- Descend through compared nested bodies, then continue from the actual
caller rejoin with the reached host. Only the completed case has the full
checked observable trace as a guarantee. A cut records a reached configuration
and a matching observable prefix, not execution of the unvisited suffix. -/
theorem NestedPlan.runs (plan : NestedPlan bindings profile ready base start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ trace reached, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming trace reached ∧
      PayloadPrefix.visible trace <+: PayloadPrefix.visible labels ∧
      ((PayloadPrefix.visible labels = PayloadPrefix.visible trace ∧ HostFrame.Related.Paired older finish reached) ∨
        NestedCut bindings profile ready base older reached) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.runs plan paired

/-- Join actual argument lowering and Core entry to a classified body,
worker completion and delivery under one linked dispatcher. The body may
contain nested gives; it is selected only at the reached Core entry. An
argument trap or suspension instead ends the finite plan before entry. -/
theorem stackful_worker_plan {reached first : Config (core3 grow) (HostState sig)} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} {callees : List (ComponentCall.Callee sig)}
    (args : CalleeArguments returned) {Result : Type} (words : Result → List FlatValue)
    (lowered : StringPlanPair profile ready bindings callees first (fun result => args.enter (words result)))
    (asyncMode : args.record.opts.async_ = true) (callback : args.record.opts.callback = none)
    (body : ∀ (entry : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
      entry.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest →
      ∃ bodyLabels afterBody exitLabels afterExit deliveryLabels last,
        NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) entry bodyLabels afterBody ∧
        StackfulBodyEnd args.task afterBody exitLabels afterExit ∧
        (∀ (site : StackfulReturn afterBody), site.segments = []) ∧
        NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) afterExit deliveryLabels last) :
    ∃ leading entry trailing last,
      Steps profile ready (Dispatch.linked ready bindings callees) first leading entry ∧
      NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) first (leading ++ trailing) last ∧
      ((∃ (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
          entry.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest ∧
          NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) entry trailing last) ∨
        (StringPlanStopped profile ready bindings first leading entry ∧ trailing = [] ∧ last = entry)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.stackfulWorker
    args words lowered asyncMode callback body

/-- A placed public memory or flat give with a nonallocating data root has
its body comparison derived from the compiled field and linked width.
It rejoins the original Core caller on success; a canonical trap instead
keeps the common reached store and does not issue a completion reply. -/
theorem local_data_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    (data : PayloadPrefix.LocalDataType (sig.payload site.tag)) (payload : Stored.Payload (sig.payload site.tag))
    (field : site.field = .data (sig.payload site.tag) payload) {entryLabels}
    (entryPath : Steps profile ready (specDispatch ready base) site.start entryLabels site.checked)
    (silent : PayloadPrefix.visible entryLabels = [])
    (placed : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok ())
    (prepared : Stored.OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ()) :
    ∃ bodyLabels reached, NestedPlan bindings profile ready base site.start (entryLabels ++ bodyLabels) reached ∧
      ((∃ value checkedLabels atReply,
        Steps profile ready (specDispatch ready base) site.checked checkedLabels atReply ∧
        atReply.ctl = site.cursor.control (site.reply (.ok value)) ∧ bodyLabels = checkedLabels ++ [.tau, .tau, .tau] ∧
        reached.host = atReply.host.record (route.reply site.destination site.start.host.nextTicket (.ok value)).1) ∨
      (reached.ctl = [] ∧ ∃ leading reason, PayloadPrefix.visible bodyLabels = leading ++ [.trap reason])) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.localDataGive
    site linked data payload field entryPath silent placed prepared

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch
