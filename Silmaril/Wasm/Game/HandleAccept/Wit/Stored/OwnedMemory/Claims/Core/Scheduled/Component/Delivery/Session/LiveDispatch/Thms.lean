module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open PayloadRoot ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {route : GiveEffectRoute}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {bindings : List (Binding sig)}

/-- The give overlay does not replace the program installed at an on-cancel
request. The installed program can still consult the reached host later. -/
theorem LiveDispatch.cancel_dispatch (callback : CancelRef) :
    specDispatch ready base (.onCancel callback) = specDispatch ready (LiveDispatch.host bindings base) (.onCancel callback) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.dispatchUnchanged trivial

/-- Each reached call uses the same dynamic dispatcher, but selects the root from
its own live journal. The selected-site replacement and its exclusion of later
matching requests are not needed for this entry. This does not assert that the
body returns, or that a callback preserves the root's live transfer authority. -/
theorem LiveDispatch.entry (site : Site grow sig route) (linked : site.Linked bindings) (other : HostState sig)
    (selected : Stored.Endpoints.Core.childFromHistory other.writer.accepted site.handle = some site.tree) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) (HostFrame.replace site.start other)
        labels (HostFrame.replace (site.reference site.referenceReply) other) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.entry site linked other selected

/-- Enter a new give at a reached paired Core request. The live reference
caller selects its current root, and both active and blocked older frame
substitutions survive installation of the canonical body. -/
theorem LiveDispatch.entry_paired (site : Site grow sig route) (linked : site.Linked bindings)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start other)
    (selected : Stored.Endpoints.Core.childFromHistory other.host.writer.accepted site.handle = some site.tree) :
    ∃ labels entered,
      labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) other labels entered ∧
      HostFrame.Related.Paired older (site.reference site.referenceReply) entered ∧ entered.host = other.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.pairedEntry site linked paired selected

/-- A same-instance public give reached in a confined allocator callback
returns boundary refusal words without consulting the canonical host's
journal. Both active and saved older frames remain paired. -/
theorem LiveDispatch.closed_give_paired {start incoming : Config (core3 grow) (HostState sig)}
    (callout : LinkedCallback.ClosedGive bindings start) {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ labels reached, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming labels reached ∧
      HostFrame.Related.Paired older callout.resume reached ∧ reached.host = incoming.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.pairedClosedGive callout paired

/-- Compose live nested entry, a reached canonical body and its actual
caller rejoin. A divergent host read or pop of an older substituted frame
is reported at that step rather than being replayed as the remaining body. -/
theorem LiveDispatch.nested_return (site : Site grow sig route) (linked : site.Linked bindings)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other checked baseline : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start other)
    (selected : Stored.Endpoints.Core.childFromHistory other.host.writer.accepted site.handle = some site.tree)
    {value : route.output.Result} {reached reference : Config (core3 grow) (HostState sig)} {labels}
    (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline)
    (body : CoreGrowthSteps profile ready (specDispatch ready base) (site.reference site.referenceReply) labels baseline)
    (closed : LiveDispatch.UnchangedThrough bindings profile ready base (site.reference site.referenceReply) labels baseline) :
    let dispatch := specDispatch ready (LiveDispatch.host bindings base)
    ∃ installed entered, installed.all (· matches .tau) = true ∧ Steps profile ready dispatch other installed entered ∧
      LiveDispatch.NestedReplay profile ready dispatch older (site.reference site.referenceReply) entered labels checked :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.nestedReturn
    site linked paired selected replies body closed

variable {start finish : Config (core3 grow) (HostState sig)}

/-- Classify the reached scheduler step before installing its next program.
Only direct calls and Core callouts can install an overlaid give. -/
theorem LiveDispatch.classify_step {label} (step : Step profile ready (specDispatch ready base) start label finish) :
    Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) start label finish ∨
      LiveDispatch.GiveInstall bindings (specDispatch ready base) start label finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.classifyStep step

/-- Discover the actual nested installation in a finite run.
No blanket exclusion of nested gives is needed. The live replay stops before
dispatching the give, or at an earlier divergent read or substituted return.
Growth certificates are needed for the allocator's memory invariants, not
for classifying an already reached scheduler step. -/
theorem LiveDispatch.paired_replay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {incoming : Config (core3 grow) (HostState sig)} {labels}
    (paired : HostFrame.Related.Paired older start incoming)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    LiveDispatch.PairedReplay bindings profile ready base older start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.pairedReplay paired run

theorem LiveDispatch.GiveInstall.step {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))} {label}
    (install : LiveDispatch.GiveInstall bindings dispatch start label finish) :
    Step profile ready dispatch start label finish := by
  cases install with
  | direct focused _ => exact .call focused
  | core focused calling _ => exact .coreCallout focused calling

/-- Recover the exact nominal binding, arguments, and frames at the reached
installation. A direct program call is not disguised as a Core caller. -/
theorem LiveDispatch.GiveInstall.request {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))} {label}
    (install : LiveDispatch.GiveInstall bindings dispatch start label finish) :
    Nonempty (LiveDispatch.CoreGiveRequest bindings start) ∨ LiveDispatch.DirectGiveAt bindings start :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.classifyGiveRequest install

/-- Invert successful memory admission at the actual reached request. -/
theorem LiveDispatch.CoreGiveRequest.memory_selection (request : LiveDispatch.CoreGiveRequest bindings start)
    (memory : request.schema = none) {tree : Stored.OwnedMemory.Tree sig} {address : Nat}
    (evaluation : Plain.runBody (LiveDispatch.admit request.inst (selectMemoryDestination request.destination request.args))
      start.store start.host (some request.thread) = (start.store, start.host, .ok (.ok (tree, address)))) :
    ∃ (pointer : FlatValue) (selection : request.Selected (.memory pointer)), selection.tree = tree ∧ flatNat pointer = address :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.memorySelection request memory evaluation

/-- Invert successful flat admission at the actual reached request. -/
theorem LiveDispatch.CoreGiveRequest.flat_selection (request : LiveDispatch.CoreGiveRequest bindings start)
    {schema : Stored.TypeOf} (flat : request.schema = some schema) {tree : Stored.OwnedMemory.Tree sig}
    (evaluation : Plain.runBody (LiveDispatch.admit request.inst
      (selectFlatDestination request.destination schema request.args)) start.store start.host (some request.thread) =
      (start.store, start.host, .ok (.ok tree))) :
    ∃ selection : request.Selected (.flat schema), selection.tree = tree :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.flatSelection request flat evaluation

/-- Turn the actual selected root and successful compiler result into a
linked recursive site. No emitter readiness or live claim validity is assumed. -/
theorem LiveDispatch.CoreGiveRequest.Selected.linked_site {request : LiveDispatch.CoreGiveRequest bindings start}
    (selection : request.Selected route) {tag : sig.Tag} {payload : Stored.OwnedMemory.Payload (sig.payload tag)}
    {arity : Nat} {children : Fin arity → Stored.OwnedMemory.Tree sig} {field : Stored.Endpoints.RecordLower.Field} {plan}
    (picked : selection.tree = .tag ⟨tag, payload⟩ arity children)
    (preflight : Record.preflightValue (request.destination.context (grow := grow) request.inst) (sig.payload tag)
      payload route.output = .ok (field, plan)) :
    (selection.site tag payload arity children field).Linked bindings :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.selectionLinked selection picked preflight

/-- Recover the exact tagged root and recursive site when the compiler check
succeeds. The selected tag and its payload are not caller-supplied. -/
theorem LiveDispatch.CoreGiveRequest.Selected.compiler_success {request : LiveDispatch.CoreGiveRequest bindings start}
    (selection : request.Selected route) {field : Stored.Endpoints.RecordLower.Field} {plan}
    (compiled : selection.preflight = .ok (field, plan)) :
    ∃ (tag : sig.Tag) (payload : Stored.OwnedMemory.Payload (sig.payload tag)) (arity : Nat)
      (children : Fin arity → Stored.OwnedMemory.Tree sig),
      selection.tree = .tag ⟨tag, payload⟩ arity children ∧
      (selection.site tag payload arity children field).Linked bindings :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.compilerSuccess selection compiled

/-- A failed compiler check reaches the actual checked status reply without
entering the emitter. This does not run the canonical body or synthesize a
canonical error. The parked caller resumes against the original store. -/
theorem LiveDispatch.CoreGiveRequest.Selected.compiler_refusal {request : LiveDispatch.CoreGiveRequest bindings start}
    (selection : request.Selected route) {issue : Stored.Endpoints.RecordLower.Issue}
    (refused : selection.preflight = .error issue)
    (impl : HostImpl (core3 grow) (HostState sig) := Core.Scheduled.host bindings)
    (embedder : impl.embedder = (Core.Scheduled.host (grow := grow) bindings).embedder := by rfl) :
    ∃ count, Steps profile ready (specDispatch ready impl) start (List.replicate count .tau) (selection.compilerRefused issue) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.compilerRefusal selection refused impl embedder

/-- At the actual paired Core request, the guarded selectors agree when the
single reached lookup agrees. This includes boundary refusals and the case
where no lookup takes place. Both evaluators leave their own host and store
unchanged; there is no equality premise on journals, authority or older frames. -/
theorem LiveDispatch.CoreGiveRequest.paired_selection (request : LiveDispatch.CoreGiveRequest bindings start)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other)
    (reads : ∀ handle, request.lookupDemand = some handle →
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory other.host.writer.accepted handle) :
    ∃ otherFrames otherRest verdict,
      other.ctl = ⟨request.thread, .core request.core request.next, otherFrames⟩ :: otherRest ∧
      (core3 grow).status other.store.core request.core = .callout (.embedder request.name request.kind) request.args ∧
      Plain.runBody request.selectionProgram start.store start.host (some request.thread) = (start.store, start.host, verdict) ∧
      Plain.runBody request.selectionProgram other.store other.host (some request.thread) = (other.store, other.host, verdict) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.pairedSelectionObservations request paired reads

/-- Compare the actual paired caller's selector or expose the differing live
lookup. A lookup difference is not yet a different verdict: for example,
both flat selections can reject the schema of different roots. -/
theorem LiveDispatch.CoreGiveRequest.paired_selection_or_lookup_difference (request : LiveDispatch.CoreGiveRequest bindings start)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) :
    (∃ otherFrames otherRest verdict,
      other.ctl = ⟨request.thread, .core request.core request.next, otherFrames⟩ :: otherRest ∧
      (core3 grow).status other.store.core request.core = .callout (.embedder request.name request.kind) request.args ∧
      Plain.runBody request.selectionProgram start.store start.host (some request.thread) = (start.store, start.host, verdict) ∧
      Plain.runBody request.selectionProgram other.store other.host (some request.thread) = (other.store, other.host, verdict)) ∨
    ∃ handle, request.lookupDemand = some handle ∧
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle ≠
        Stored.Endpoints.Core.childFromHistory other.host.writer.accepted handle :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.classifyPairedSelection request paired

/-- A typed boundary refusal takes the actual scheduler entry, including the
confinement choice, and rejoins both parked callers with the same ABI words.
Only the checked side journals its entry and refusal. No emitter runs. -/
theorem LiveDispatch.CoreGiveRequest.paired_admission_refusal (request : LiveDispatch.CoreGiveRequest bindings start)
    (impl : HostImpl (core3 grow) (HostState sig))
    (embedder : impl.embedder = (Core.Scheduled.host (grow := grow) bindings).embedder)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) {issue : Issue}
    (refused : Plain.runBody request.selectionProgram start.store start.host (some request.thread) =
      (start.store, start.host, .ok (.error issue)))
    (reads : ∀ handle, request.lookupDemand = some handle →
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory other.host.writer.accepted handle) :
    ∃ leftCount rightCount checked canonical,
      Steps profile ready (specDispatch ready impl) start (List.replicate leftCount .tau) checked ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) other (List.replicate rightCount .tau) canonical ∧
      HostFrame.Related.Paired older checked canonical ∧
      checked.host = (start.host.enter request.name request.kind request.args).record (request.admissionReply issue).1 ∧
      canonical.host = other.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.pairedAdmissionRefusal
    request impl embedder paired refused reads

/-- A failed arena lookup while resolving the caller is a canonical trap,
not a refusal or journal lookup. Both sides lock down the reached store;
the checked entry remains journaled, and neither caller receives a reply. -/
theorem LiveDispatch.CoreGiveRequest.paired_admission_trap (request : LiveDispatch.CoreGiveRequest bindings start)
    (impl : HostImpl (core3 grow) (HostState sig))
    (embedder : impl.embedder = (Core.Scheduled.host (grow := grow) bindings).embedder)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) {reason : TrapReason}
    (trapped : Plain.callerInstance start.store request.thread = .error (.trapped reason)) :
    ∃ leftCount rightCount,
      Steps profile ready (specDispatch ready impl) start (List.replicate leftCount .tau ++ [.trap reason])
        (StepDefs.trapCfg { start with host := start.host.enter request.name request.kind request.args }) ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) other
        (List.replicate rightCount .tau ++ [.trap reason]) (StepDefs.trapCfg other) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.pairedAdmissionTrap
    request impl embedder paired trapped

/-- At a successfully selected public give, the handle is the actual
read demanded by the selector. It does not confer transfer permission. -/
theorem LiveDispatch.CoreGiveRequest.Selected.lookup_demand {request : LiveDispatch.CoreGiveRequest bindings start}
    (selection : request.Selected route) : request.lookupDemand = some selection.handle :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.selectedDemand selection

/-- Install the next real canonical program after successful selection,
without running any of its emitter operations. The same cut exists if the
checked compiler rejects the payload; it is not a reference refusal. -/
theorem LiveDispatch.CoreGiveRequest.Selected.paired_canonical_pending_host {request : LiveDispatch.CoreGiveRequest bindings start}
    (selection : request.Selected route)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other)
    (reads : ∀ handle, request.lookupDemand = some handle →
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory other.host.writer.accepted handle) :
    ∃ labels entered, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) other labels entered ∧
      entered.host = other.host ∧ HostFrame.Related.Paired older selection.canonicalPending entered :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.pendingPaired
    (profile := profile) (ready := ready) (base := base) selection paired reads

theorem LiveDispatch.CoreGiveRequest.Selected.paired_canonical_pending {request : LiveDispatch.CoreGiveRequest bindings start}
    (selection : request.Selected route)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other)
    (reads : ∀ handle, request.lookupDemand = some handle →
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory other.host.writer.accepted handle) :
    ∃ labels entered, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) other labels entered ∧
      HostFrame.Related.Paired older selection.canonicalPending entered :=
  (LiveDispatch.CoreGiveRequest.Selected.paired_canonical_pending_host
    (profile := profile) (ready := ready) (base := base) selection paired reads).imp fun _ result =>
      result.imp fun _ ⟨silent, path, _, aligned⟩ => ⟨silent, path, aligned⟩

/-- Successful compilation's recursive comparison starts at the same
canonical program identified by live selection. No synthetic reply or
entry at a different memory pointer is needed to start the comparison. -/
theorem LiveDispatch.CoreGiveRequest.Selected.pending_reference {request : LiveDispatch.CoreGiveRequest bindings start}
    (selection : request.Selected route) {tag : sig.Tag} {payload : Stored.OwnedMemory.Payload (sig.payload tag)}
    {arity : Nat} {children : Fin arity → Stored.OwnedMemory.Tree sig} (field : Stored.Endpoints.RecordLower.Field)
    (picked : selection.tree = .tag ⟨tag, payload⟩ arity children) :
    selection.canonicalPending = (selection.site tag payload arity children field).reference
      (selection.site tag payload arity children field).referenceReply :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.pendingReference selection field picked

/-- Enter on the live root and compare the reached prefix of the nested body,
even if it has not returned or executes another public give. Further requests
are exposed at their real caller and with all older frames still paired. -/
theorem LiveDispatch.nested_prefix (site : Site grow sig route) (linked : site.Linked bindings)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {incoming : Config (core3 grow) (HostState sig)} {labels}
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (body : Steps profile ready (specDispatch ready base) (site.reference site.referenceReply) labels finish) :
    ∃ installed entered, installed.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming installed entered ∧
      LiveDispatch.PairedReplay bindings profile ready base older (site.reference site.referenceReply) entered labels finish := by
  obtain ⟨installed, entered, silent, entry, aligned, _⟩ := LiveDispatch.entry_paired (base := base) site linked paired selected
  exact ⟨installed, entered, silent, entry, LiveDispatch.paired_replay aligned body⟩

/-- Closed steps preserve their actual configurations under the reference overlay.
An open handler is unchanged when installed, but later requests it issues are classified separately. -/
theorem LiveDispatch.replay {labels} (run : Steps profile ready (specDispatch ready base) start labels finish)
    (closed : LiveDispatch.UnchangedThrough bindings profile ready base start labels finish) :
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.replay run closed

/-- A classified interleaving runs under the live give overlay with the
same steps against its reached store and journal. -/
theorem LiveDispatch.interleaving_steps {actions labels incoming outgoing}
    (between : JournalInterleaving profile ready base start incoming actions labels finish outgoing) :
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base))
      (HostFrame.replace start incoming) labels (HostFrame.replace finish outgoing) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.interleavingSteps between

/-- The classified Core, delivery, publication and tick transitions do not install
an embedder body. Their dispatcher compatibility follows from their constructors,
not a premise that the two finished runs agree. The reached readiness and root
selection witnesses are still required where these transitions read the host. -/
theorem LiveDispatch.entry_after_interleaving (site : Site grow sig route) (linked : site.Linked bindings)
    {incoming outgoing : HostState sig}
    (selected : Stored.Endpoints.Core.childFromHistory outgoing.writer.accepted site.handle = some site.tree)
    {leading middleLabels actions}
    (prior : Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start leading
      (HostFrame.replace finish incoming))
    (between : JournalInterleaving profile ready base finish incoming actions middleLabels site.start outgoing) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start
        (leading ++ middleLabels ++ labels) (HostFrame.replace (site.reference site.referenceReply) outgoing) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.afterInterleaving
    site linked selected prior between

/-- The same starting observations give the same selected root after a classified
interleaving. Each commit registers on the live journal; no equality or retention
of held claims, lenders, event slots, or guest bytes is needed. -/
theorem LiveDispatch.entry_after_equal_roots (site : Site grow sig route) (linked : site.Linked bindings)
    {incoming outgoing : HostState sig} (roots : incoming.writer.accepted = finish.host.writer.accepted)
    {leading middleLabels actions}
    (prior : Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start leading
      (HostFrame.replace finish incoming))
    (between : JournalInterleaving profile ready base finish incoming actions middleLabels site.start outgoing) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start
        (leading ++ middleLabels ++ labels) (HostFrame.replace (site.reference site.referenceReply) outgoing) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.afterSameRoots
    site linked roots prior between

/-- A closed delivery interleaving derives the live selection from the starting
observations. Installing the selected canonical body is read-only; it does not
retain any claims or event records that the interleaving may have changed. -/
theorem LiveDispatch.CoreGiveRequest.Selected.pending_after_interleaving {request : LiveDispatch.CoreGiveRequest bindings finish}
    (selection : request.Selected route) {actions labels incoming outgoing}
    (between : JournalInterleaving profile ready base start incoming actions labels finish outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted) :
    ∃ leading entered, leading.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) (HostFrame.replace start incoming)
        (labels ++ leading) entered ∧
      HostFrame.Related.Paired (fun _ _ => False) selection.canonicalPending entered ∧
      entered.host.writer.accepted = finish.host.writer.accepted :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.pendingAfterInterleaving selection between roots

/-- Closed delivery interleavings derive lookup agreement from their
starting accepted observations, including when an intervening commit
publishes a new root. Carry that invariant past a reached public refusal
without assuming equal journals or live authority. -/
theorem LiveDispatch.CoreGiveRequest.refusal_after_interleaving (request : LiveDispatch.CoreGiveRequest bindings finish)
    (embedder : base.embedder = (Core.Scheduled.host (grow := grow) bindings).embedder)
    {actions labels incoming outgoing} (between : JournalInterleaving profile ready base start incoming actions labels finish outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted) {issue : Issue}
    (refused : Plain.runBody request.selectionProgram finish.store finish.host (some request.thread) =
      (finish.store, finish.host, .ok (.error issue))) :
    ∃ leftCount rightCount checked canonical,
      Steps profile ready (specDispatch ready base) start (labels ++ List.replicate leftCount .tau) checked ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) (HostFrame.replace start incoming)
        (labels ++ List.replicate rightCount .tau) canonical ∧
      HostFrame.Related.Paired (fun _ _ => False) checked canonical ∧
      canonical.host.writer.accepted = checked.host.writer.accepted :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.afterRefusal
    request embedder between roots refused

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
