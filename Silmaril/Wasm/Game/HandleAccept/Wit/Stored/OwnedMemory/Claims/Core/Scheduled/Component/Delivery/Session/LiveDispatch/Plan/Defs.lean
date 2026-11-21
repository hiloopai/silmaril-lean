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

/-- Compare an actual residual string program under the fixed live give
dispatcher. Each local segment may trap; each entered allocator can expose
any finite classified prefix. Only a pop of its marked occurrence enters a
smaller program. The terminal consumer can compare the real descriptor. -/
def LiveStringReplay (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (cx : LiftLowerContext (core3 grow))
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (finish : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop)
    (length : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open PayloadPrefix ReturnFrame.Occurrence in
  let checkDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason (StringFront length)) (labels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest
      (fun front : StringFront length => front.remaining cx >>= checkNext) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest
      (fun front : StringFront length => front.remaining cx >>= canonNext) result
    LocalLeafLabels result labels ∧ CoreGrowthSteps profile ready checkDispatch left labels lhs ∧
    CoreGrowthSteps profile ready canonDispatch right labels rhs ∧
    ∀ front, result = .ok front →
      RetainsActiveSlots profile ready checkDispatch left labels lhs ∧
      RetainsActiveSlots profile ready canonDispatch right labels rhs ∧
      match front with
      | .done pointer => finish pointer lhs rhs check canon
      | .call pointer oldSize alignment size rest _ =>
        let first := stringPlanResume cx rest checkNext
        let second := stringPlanResume cx rest canonNext
        let firstEntry := LinkedCallback.stringReallocEntry ready bindings cx pointer oldSize alignment size rest checkNext lhs check
        let secondEntry := stringAllocatorEntry canonDispatch cx pointer oldSize alignment size rhs canon second
        ∀ {seen reached}, ClosedCallbackPrefix bindings profile ready base
          (fun resume => (∃ peer, older resume peer) ∨ resume = first) firstEntry seen reached →
          ∃ checkLabels canonLabels reference mark,
            Steps profile ready checkDispatch lhs (.tau :: checkLabels) reached ∧
            Steps profile ready canonDispatch rhs (.tau :: canonLabels) reference ∧
            visible checkLabels = seen ∧ visible canonLabels = seen ∧
            HostFrame.Related.Paired (ReturnFrame.Extend older first second) reached reference ∧
            Core3.Grows lhs.store.core reached.store.core ∧
            reached.host.writer.accepted = lhs.host.writer.accepted ∧
            reference.host.writer.accepted = rhs.host.writer.accepted ∧
            AllocatorMark profile ready base bindings older firstEntry secondEntry checkLabels canonLabels reached reference mark ∧
            ∀ (value : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)), mark = some (.active 0 0) →
              reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat value)) →
              ∃ peer : Cursor (E := core3 grow) (HostState sig),
                let after := { reached with ctl := cursor.control (first (.nat value)) }
                let referenceAfter := { reference with ctl := peer.control (second (.nat value)) }
                RetainsActiveSlots profile ready checkDispatch lhs (.tau :: checkLabels ++ [.tau]) after ∧
                RetainsActiveSlots profile ready canonDispatch rhs (.tau :: canonLabels ++ [.tau]) referenceAfter ∧
                LiveStringReplay profile ready base bindings older cx checkNext canonNext finish rest.length after referenceAfter cursor peer
termination_by length

/-- Two finite paths, compared at their reached stores and visible labels. -/
def ComparedPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checkLabels canonLabels,
    Steps profile ready (specDispatch ready base) leftStart checkLabels left ∧
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) rightStart canonLabels right ∧
    PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧ left.store = right.store

/-- A compared prefix with occurrence trails for active slots. The starting
offset accounts for older slots below an allocator frame that is popped. -/
def ComparedSlots (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) (offset : Nat := 0) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checkLabels canonLabels,
    (∀ depth, Prefix profile ready (specDispatch ready base) leftStart (.active 0 (depth + offset)) checkLabels left (.active 0 depth)) ∧
    (∀ depth, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      rightStart (.active 0 (depth + offset)) canonLabels right (.active 0 depth)) ∧
    PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen

/-- A cumulative view of the actual string plan. Compare a finite stopped
allocator prefix at its reached state; to continue, it must pop the marked
occurrence. Only a finished plan reaches the consumer. -/
def LiveStringPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (cx : LiftLowerContext (core3 grow))
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (leftStart rightStart : Config (core3 grow) (HostState sig))
    (finish : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) →
      Trace grow sig → Prop)
    (length : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (seen : Trace grow sig) (offset : Nat := 0) : Prop :=
  open PayloadPrefix ReturnFrame.Occurrence in
  let checkDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason (StringFront length)) (labels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest
      (fun front : StringFront length => front.remaining cx >>= checkNext) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest
      (fun front : StringFront length => front.remaining cx >>= canonNext) result
    LocalLeafLabels result labels ∧ Steps profile ready checkDispatch left labels lhs ∧ Steps profile ready canonDispatch right labels rhs ∧
    match result with
    | .error reason => lhs.ctl = [] ∧ rhs.ctl = [] ∧
      ComparedPaths profile ready base bindings leftStart rightStart (seen ++ [.trap reason]) lhs rhs
    | .ok (.done pointer) => ComparedSlots profile ready base bindings leftStart rightStart seen lhs rhs offset ∧
      finish pointer lhs rhs check canon seen
    | .ok (.call pointer oldSize alignment size rest _) =>
      let first := stringPlanResume cx rest checkNext
      let second := stringPlanResume cx rest canonNext
      let firstEntry := LinkedCallback.stringReallocEntry ready bindings cx pointer oldSize alignment size rest checkNext lhs check
      let secondEntry := stringAllocatorEntry canonDispatch cx pointer oldSize alignment size rhs canon second
      ∀ {observed reached}, ClosedCallbackPrefix bindings profile ready base
        (fun resume => (∃ peer, older resume peer) ∨ resume = first) firstEntry observed reached →
        ∃ checkLabels canonLabels reference mark,
          AllocatorMark profile ready base bindings older firstEntry secondEntry checkLabels canonLabels reached reference mark ∧
          HostFrame.Related.Paired (ReturnFrame.Extend older first second) reached reference ∧
          ComparedPaths profile ready base bindings leftStart rightStart (seen ++ observed) reached reference ∧
          ∀ (value : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)), mark = some (.active 0 0) →
            reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat value)) →
            ∃ peer : Cursor (E := core3 grow) (HostState sig),
              let after := { reached with ctl := cursor.control (first (.nat value)) }
              let referenceAfter := { reference with ctl := peer.control (second (.nat value)) }
              LiveStringPaths profile ready base bindings older cx checkNext canonNext leftStart rightStart finish
                rest.length after referenceAfter cursor peer (seen ++ observed) offset
termination_by length

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

/-- Entry into the exact recursive bodies of a nested collection after its
marked allocator returns, range checks pass and a fresh reservation succeeds.
The frame and cumulative trails are for the reached state, not the state
before the allocator. Memory-map placement keeps its allocation-time mode. -/
def LiveCollectionChildren (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (start incoming : Config (core3 grow) (HostState sig)) (pointer bytes : Nat)
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (observed : Trace grow sig)
    (visit : LinkedCallback.MemorySequence.Finish grow sig := fun _ _ _ _ => True) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  let area := layout destination.width element
  let mode := CanonicalTree.EntryMode.forOutput destination.width type output
  ∃ left right canon,
    ComparedSlots profile ready base bindings start incoming observed left right ∧
    LinkedCallback.ChildFrameOver older left right check canon ∧
    (core3 grow).memAddrType? left.store.core destination.memory = some destination.width ∧
    (core3 grow).memSize? left.store.core destination.memory = some bytes ∧
    pointer = alignTo pointer area.alignment ∧ pointer + entries.length * area.size ≤ bytes ∧
    Core3.Grows start.store.core left.store.core ∧
    left.ctl = check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) ∧
    right.ctl = canon.control (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) ∧
    visit left right check canon

/-- Finite callback paths for an actual dynamic child. A live mark at the
natural-pointer return is required to inspect the range. Failed range checks
trap, and a failed fresh reservation does not enter the children. -/
def LiveCollectionPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (start incoming : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (visit : Nat → Nat → LinkedCallback.MemorySequence.Finish grow sig := fun _ _ _ _ _ _ => True) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  let area := layout destination.width element
  let mode := CanonicalTree.EntryMode.forOutput destination.width type output
  let first := checkedCollectionResume destination inst entries area index output checkNext
  let second := canonicalCollectionResume destination inst entries area output canonNext mode
  let leftEntry := collectionEntry destination inst area entries.length (specDispatch ready base) start check first
  let rightEntry := collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
    incoming canon second
  ∀ {seen finish}, ClosedCallbackPrefix bindings profile ready base
      (fun resume => (∃ peer, older resume peer) ∨ resume = first) leftEntry seen finish →
    ∃ checkLabels canonLabels reached mark,
      AllocatorMark profile ready base bindings older leftEntry rightEntry checkLabels canonLabels finish reached mark ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older first second) finish reached ∧
      ComparedPaths profile ready base bindings start incoming seen finish reached ∧
      ∀ pointer cursor, mark = some (.active 0 0) →
        finish.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) →
        CollectionRangeCut profile ready base bindings older finish reached cursor destination area entries.length pointer
          (Stored.Endpoints.RecordLower.Field.listObjects entries)
          (fun addr verdict => checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext)
          (fun addr => canonicalCollectionTail destination inst entries area output addr mode >>= canonNext) ∧
        ∀ bytes, (core3 grow).memSize? finish.store.core destination.memory = some bytes →
          pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
          OwnedMemory.Claims.Record.prepare finish.store finish.host.writer (Field.listObjects entries) = .ok () →
          LiveCollectionChildren profile ready base bindings older destination inst type element entries index output checkNext
            canonNext start incoming pointer bytes cursor seen (visit pointer bytes)

/-- The live dry run before a nested allocation either reaches the typed
checked continuation alone or admits the finite allocator comparison. The
refusal leaves canonical at its original program, before any width read. -/
def LiveCollectionEntry (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (start incoming : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (visit : Nat → Nat → LinkedCallback.MemorySequence.Finish grow sig := fun _ _ _ _ _ _ => True) : Prop :=
  open Stored.Endpoints.RecordLower in
  match OwnedMemory.Claims.Record.prepare start.store start.host.writer (Field.listObjects entries) with
  | .error issue =>
    let refusal := match issue with
      | .preflight reason => Issue.field index (.beforeAllocation reason)
      | reason => Issue.nested index reason
    ComparedSlots profile ready base bindings start incoming []
      { start with ctl := check.control (checkNext (.error refusal)) } incoming
  | .ok () => (core3 grow).memAddrType? incoming.store.core destination.memory = some destination.width →
    LiveCollectionPaths profile ready base bindings older destination inst type element entries index output checkNext canonNext
      start incoming check canon visit

/-- A reached collection segment. The slot offset counts removed frames.
On checked refusal, the canonical program is the actual unexecuted suffix
at the reached stop, not necessarily the initial child-entry program. -/
def CollectionSegmentThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) {Result : Type}
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (offset : Nat)
    (stopsAt : Session grow sig (Ret (core3 grow)) → Prop)
    (next : Result → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop) : Prop :=
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
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready checkedDispatch checked (.active 0 (depth + offset))
          checkLabels left (.active 0 depth)) ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready canonDispatch canonical (.active 0 (depth + offset))
          canonLabels right (.active 0 depth)) ∧ next value left right canon
    | .refused issue => ∃ stop, stopsAt stop ∧
        left.ctl = check.control (checkNext (.error issue)) ∧ right.ctl = canon.control stop ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready checkedDispatch checked (.active 0 (depth + offset))
          checkLabels left (.active 0 depth)) ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready canonDispatch canonical (.active 0 (depth + offset))
          canonLabels right (.active 0 depth))

abbrev CollectionSegment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) {Result : Type}
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (offset : Nat)
    (stopsAt : Session grow sig (Ret (core3 grow)) → Prop) (keep : CStore (core3 grow) → Prop := fun _ => True) : Prop :=
  CollectionSegmentThen profile ready base bindings older checked canonical check checkNext canonNext offset stopsAt
    (fun _ left _ _ => keep left.store)

/-- The specialization in which a failed fresh preparation stops before
any child executes. -/
abbrev CollectionReturn (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) {Result : Type}
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (childEntry : Session grow sig (Ret (core3 grow))) : Prop :=
  CollectionSegment profile ready base bindings older checked canonical check checkNext canonNext 1 (· = childEntry)

/-- The unexecuted canonical list suffix at a reached nominal guard. The
address advances by the actual element stride, not by the number of writes. -/
def ElementStop (destination : RecordDestination) (inst : InstId) (entries : List Stored.Endpoints.RecordLower.Field)
    (stride ptr : Nat) (finish : Unit → Session grow sig (Ret (core3 grow))) (stop : Session grow sig (Ret (core3 grow))) : Prop :=
  ∃ leading remaining, entries = leading ++ remaining ∧ remaining ≠ [] ∧
    stop = (Stored.Endpoints.RecordLower.CanonicalTree.elements Limits.spec Quirks.none (destination.context inst)
      destination.width remaining .value stride (ptr + leading.length * stride) >>= finish)

/-- The nominal leaf schemas currently compared by the local collection rule. -/
inductive NominalElement : Stored.TypeOf → Prop where
  | own (resource : RtId) : NominalElement (.own resource)
  | future (element : Async.Element) : NominalElement (.future element)
  | stream (element : Async.Element) : NominalElement (.stream element)
  | context : NominalElement .errorContext

/-- The list depth is a property of the declared type, including empty
lists. It is independent of scheduler or allocator fuel. -/
inductive NominalListType : Nat → Stored.TypeOf → Prop where
  | leaf {type} : NominalElement type → NominalListType 0 type
  | list {depth element} : NominalListType depth element → NominalListType (depth + 1) (.list element)

/-- Visit an allocated list's actual element programs in order. The
continuation for a child admits the next sibling only on common success. -/
def liveElements (destination : RecordDestination) (inst : InstId) (stride : Nat)
    (child : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) :
    List Stored.Endpoints.RecordLower.Field → Nat → Nat → LinkedCallback.MemorySequence.Finish grow sig
  | [], _, _, left, right, check, canon => finish left right check canon
  | item :: rest, index, pointer, left, right, check, canon =>
    open LinkedCallback.MemorySequence in
    child item index pointer left right check canon
      (checkTail (.elements stride) destination inst rest (index + 1) (pointer + stride) checkNext)
      (canonTail (.elements stride) destination inst rest (pointer + stride) canonNext)
      (liveElements destination inst stride child checkNext canonNext finish rest (index + 1) (pointer + stride))

/-- The real descriptor program executes only after every element returns.
The two paths share the descriptor result or canonical trap, not an assumed
rollback of either descriptor write. -/
def LiveListPublish (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (finish : output.Result → LinkedCallback.MemorySequence.Finish grow sig) : LinkedCallback.MemorySequence.Finish grow sig :=
  fun left right check canon =>
  open PayloadPrefix in
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason output.Result) (labels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest (fun value => checkNext (.ok value)) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result
    LocalLeafLabels result labels ∧
    CoreGrowthSteps profile ready (specDispatch ready base) left labels lhs ∧
    CoreGrowthSteps profile ready (specDispatch ready (LiveDispatch.host bindings base)) right labels rhs ∧
    ∀ value, result = .ok value →
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready base) left labels lhs ∧
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (LiveDispatch.host bindings base)) right labels rhs ∧
      finish value lhs rhs check canon

def liveListTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (index : Nat) (output : Stored.Lower.Output) (compare : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (finish : LinkedCallback.MemorySequence.ValueFinish grow sig output) : Nat → Nat → LinkedCallback.MemorySequence.Finish grow sig :=
  open ABI LinkedCallback.MemorySequence in
  fun pointer _ => liveElements destination inst (layout destination.width element).size compare
    (publishChecked destination inst pointer entries.length index output checkNext)
    (publishCanonical destination inst pointer entries.length output canonNext)
    (LiveListPublish profile ready base bindings output checkNext canonNext finish) entries 0 pointer

/-- A decreasing comparison for nested list elements under the two live
dispatchers. Each allocation uses its own occurrence trail and rechecks
the actual reached writer before taking the child branch. -/
def liveNominalList (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    Nat → LinkedCallback.MemorySequence.FieldComparison grow sig
  | 0 => fun item index address left right check canon checkNext canonNext finish =>
    LinkedCallback.HandleFieldThenBetween profile ready (specDispatch ready base)
      (specDispatch ready (LiveDispatch.host bindings base)) item index (.memory address) left right check canon
      checkNext canonNext (fun () => finish)
  | depth + 1 => fun item index address left right check canon checkNext canonNext finish =>
    open Stored.Endpoints.RecordLower in
    ∃ element entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.list element) element entries index
        (.memory address) checkNext canonNext left right check canon
        (liveListTail profile ready base bindings destination inst element entries index (.memory address)
          (liveNominalList profile ready base bindings older destination inst depth) checkNext canonNext (fun () => finish))

/-- Enter both actual public give bodies and compare their nested lists
under the live overlay, up to the reached reply programs. A callback may
remain parked and a typed late refusal never starts its canonical suffix. -/
def LinkedNominalListBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (depth : Nat) (element : Stored.TypeOf)
    (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ entries leading entered peer,
    site.field = .dynamic (.list element) element entries ∧ PayloadPrefix.visible leading = [] ∧
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming leading entered ∧
    entered.host = incoming.host ∧
    LiveCollectionPaths profile ready base bindings older site.destination site.inst (.list element) element entries 0
      route.output site.reply site.referenceReply site.checked entered site.cursor peer
      (liveListTail profile ready base bindings site.destination site.inst element entries 0 route.output
        (liveNominalList profile ready base bindings older site.destination site.inst depth)
        site.reply site.referenceReply (fun _ _ _ _ _ => True))

/-- Stop at fresh preparation or at a reached element; neither executes the
remaining canonical elements or publishes a descriptor. -/
def ListReturnStop (destination : RecordDestination) (inst : InstId) (entries : List Stored.Endpoints.RecordLower.Field)
    (area : ABI.Layout) (output : Stored.Lower.Output) (ptr : Nat)
    (finish : output.Result → Session grow sig (Ret (core3 grow))) (stop : Session grow sig (Ret (core3 grow))) : Prop :=
  stop = (PayloadPrefix.canonicalCollectionTail destination inst entries area output ptr >>= finish) ∨
  ElementStop destination inst entries area.size ptr
    (fun _ => Stored.Endpoints.ListLower.publish (destination.context inst) destination.width ptr entries.length output >>= finish) stop

def mapFieldPlacement (cx : LiftLowerContext (core3 grow))
    (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
    (next : AddrType → Session grow sig (Ret (core3 grow))) : Session grow sig (Ret (core3 grow)) :=
  match mode with
  | .value => ptrType cx >>= next
  | .memoryMap width _ _ => next width

def mapValueProgram (destination : RecordDestination) (inst : InstId)
    (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
    (value : Stored.Endpoints.RecordLower.Field) (afterKey : Nat)
    (finish : Unit → Session grow sig (Ret (core3 grow))) : Session grow sig (Ret (core3 grow)) :=
  open Stored.Endpoints.RecordLower ABI in
  let cx := destination.context inst
  mapFieldPlacement cx mode fun width =>
    CanonicalTree.field Limits.spec Quirks.none cx destination.width value
      (.memory (alignTo afterKey (layout width value.type).alignment)) >>= finish

/-- A reached map key under the live dispatchers, from field placement
through the recursive string plan. Only completed plans reach the supplied
descriptor continuation. -/
def StringKeyThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId)
    (key : LinkedCallback.StringField) (address : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (finish : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop) : Prop :=
  let cx := destination.context inst
  let plan := storePlanFor Quirks.none destination.encoding destination.width key.value
  let checked := fun pointer => PayloadPrefix.stringPlanTail cx destination.width (.memory address) plan pointer >>=
    fun result => checkNext (.ok result)
  let canonical := fun pointer => PayloadPrefix.stringPlanTail cx destination.width (.memory address) plan pointer >>= canonNext
  let checkBody := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checked) }
  let canonBody := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonical) }
  ∃ checkLabels canonLabels,
    PayloadPrefix.visible checkLabels = [] ∧ PayloadPrefix.visible canonLabels = [] ∧
    ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready base) left checkLabels checkBody ∧
    ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (LiveDispatch.host bindings base))
      right canonLabels canonBody ∧
    LinkedCallback.ChildFrameOver older checkBody canonBody check canon ∧
    LiveStringReplay profile ready base bindings older cx checked canonical finish plan.steps.length checkBody canonBody check canon

abbrev StringKeyReplay (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin : CStore (core3 grow)) (destination : RecordDestination) (inst : InstId)
    (key : LinkedCallback.StringField) (address : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow))) : Prop :=
  StringKeyThen profile ready base bindings older destination inst key address left right check canon checkNext canonNext
    (fun _ lhs rhs cursor peer =>
      LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧ Core3.Grows origin.core lhs.store.core ∧
      PayloadPrefix.StringLocalCutBetween profile ready (specDispatch ready base)
        (specDispatch ready (LiveDispatch.host bindings base)) lhs rhs cursor peer
        (fun result => checkNext (.ok result)) canonNext)

/-- Compare the descriptor and reached nominal value at the end of a
string-key replay. Late refusal leaves the value program unexecuted, even
when its first instruction is a flat-map width read. -/
def StringKeyNominalValue (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin : CStore (core3 grow)) (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (key : LinkedCallback.StringField) (value : Stored.Endpoints.RecordLower.Field)
    (address issueIndex : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow))) : Prop :=
  open Stored.Endpoints.RecordLower ABI in
  let afterKey := address + (layout destination.width key.field.type).size
  let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
  let pending := mapValueProgram destination inst mode value afterKey canonNext
  let place := alignTo afterKey (layout destination.width value.type).alignment
  let report := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => checkNext (verdict.mapError (.nested issueIndex))
  let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
    | .error issue => pure (.error issue)
    | .ok () => OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width value 1 (.memory place)) >>= report
  StringKeyReplay profile ready base bindings older origin destination inst key address left right check canon checked (fun _ => pending) →
  StringKeyThen profile ready base bindings older destination inst key address left right check canon checked (fun _ => pending)
    (fun _ lhs rhs cursor _ => CollectionSegment profile ready base bindings older lhs rhs cursor checkNext canonNext 0
      (· = pending) (fun reached => Core3.Grows origin.core reached.core))

/-- Cut the actual map traversal at its selected entry and preserve its exact
remainder. Both the successful continuation and the stopped suffix retain the
original traversal finish, which can publish the descriptor and reply. -/
def LinkedStringMapEntry (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (index : Fin entries.length) (origin : CStore (core3 grow)) (basePtr : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (next : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop :=
        fun lhs _ _ _ => Core3.Grows origin.core lhs.store.core) : Prop :=
  open Stored.Endpoints.RecordLower ABI in
  let destination := site.destination
  let cx := destination.context site.inst
  let type : Stored.TypeOf := .record (mapEntryFields .string element)
  let stride := (layout destination.width type).size
  let ptr := basePtr + index.val * stride
  let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) route.output
  let item := entries[index.val]
  let rest := entries.drop (index.val + 1)
  let checkTail := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
    | .error issue => pure (.error issue)
    | .ok () => OwnedMemory.Claims.Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width
        rest stride (ptr + stride) (index.val + 1)) >>= checkNext
  let canonTail := fun (_ : Unit) => CanonicalTree.elements Limits.spec Quirks.none cx destination.width
    rest mode stride (ptr + stride) >>= canonNext
  left.ctl = check.control (OwnedMemory.Claims.Record.Effects.elements recordClaims Limits.spec Quirks.none cx
    destination.width (entries.drop index.val) stride ptr index.val >>= checkNext) →
  right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none cx destination.width
    (entries.drop index.val) mode stride ptr >>= canonNext) →
  ∃ (key : LinkedCallback.StringField) (value : Field), item = .aggregate type [key.field, value] ∧
    let keyArea := layout destination.width key.field.type
    let keyPtr := alignTo ptr keyArea.alignment
    let afterKey := keyPtr + keyArea.size
    let pending := mapValueProgram destination site.inst mode value afterKey canonTail
    let valuePtr := alignTo afterKey (layout destination.width value.type).alignment
    let report := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => checkTail (verdict.mapError (.nested index.val))
    let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
      | .error issue => pure (.error issue)
      | .ok () => OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
          value 1 (.memory valuePtr)) >>= report
    StringKeyThen profile ready base bindings older destination site.inst key keyPtr left right check canon checked (fun _ => pending)
      (fun _ lhs rhs cursor _ => CollectionSegmentThen profile ready base bindings older lhs rhs cursor checkTail canonTail 0
        (· = pending) (fun _ reached peer nextCheck => next reached peer cursor nextCheck))

/-- Exact controls for a reached suffix, including the original finish. -/
def LinkedStringMapAt {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index basePtr : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow))) : Prop :=
  open Stored.Endpoints.RecordLower ABI in
  let stride := (layout site.destination.width (.record (mapEntryFields .string element))).size
  let address := basePtr + index * stride
  let cx := site.destination.context site.inst
  let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) route.output
  left.ctl = check.control (OwnedMemory.Claims.Record.Effects.elements recordClaims Limits.spec Quirks.none cx
    site.destination.width (entries.drop index) stride address index >>= checkNext) ∧
  right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none cx site.destination.width
    (entries.drop index) mode stride address >>= canonNext)

/-- Compare a suffix of the actual map traversal. Only a returned key and
value enter the next suffix; a suspended allocator, refusal or trap does not.
Each link retains its visible trace and the trails of older occurrences. -/
def LinkedStringMapTraversal (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (index : Nat) (origin : CStore (core3 grow)) (basePtr : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (finish : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop :=
        fun _ _ _ _ => True) : Prop :=
  LinkedStringMapAt site element entries index basePtr left right check canon checkNext canonNext ∧
    if present : index < entries.length then
      LinkedStringMapEntry profile ready base bindings older site element entries ⟨index, present⟩ origin basePtr
        left right check canon checkNext canonNext (fun lhs rhs cursor peer =>
          LinkedStringMapTraversal profile ready base bindings older site element entries (index + 1) origin basePtr
            lhs rhs cursor peer checkNext canonNext finish)
    else
      LinkedCallback.ChildFrameOver older left right check canon ∧
        left.ctl = check.control (checkNext (.ok ())) ∧ right.ctl = canon.control (canonNext ()) ∧
        Core3.Grows origin.core left.store.core ∧ finish left right check canon
termination_by entries.length - index

/-- The actual post-prepare map body for either public give. Only a complete
entry traversal executes the outer descriptor, which can itself trap. -/
def LinkedStringMapBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (basePtr : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (index : Nat := 0) (origin : CStore (core3 grow) := left.store) : Prop :=
  let publish : Session grow sig route.output.Result := Stored.Endpoints.ListLower.publish
    (site.destination.context site.inst) site.destination.width basePtr entries.length route.output
  let checkTail := PayloadPrefix.checkedSequenceNext (.nested 0) (fun (_ : Unit) => publish >>= fun value => pure (.ok value)) site.reply
  let canonTail := fun (_ : Unit) => publish >>= site.referenceReply
  LinkedStringMapTraversal profile ready base bindings older site element entries index origin basePtr left right check canon
    checkTail canonTail (fun lhs rhs cursor _ =>
      CollectionSegment profile ready base bindings older lhs rhs cursor site.reply site.referenceReply 0 (fun _ => False))

def mapValueSuffix (destination : RecordDestination) (inst : InstId)
    (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
    (keyField value : Stored.Endpoints.RecordLower.Field) (rest : List Stored.Endpoints.RecordLower.Field) (stride address : Nat)
    (finish : Unit → Session grow sig (Ret (core3 grow))) : Session grow sig (Ret (core3 grow)) :=
  open Stored.Endpoints.RecordLower ABI in
  let keyArea := layout destination.width keyField.type
  let keyPtr := alignTo address keyArea.alignment
  let cx := destination.context inst
  mapFieldPlacement cx mode fun reached =>
    let valPtr := alignTo (keyPtr + keyArea.size) (layout reached value.type).alignment
    CanonicalTree.field Limits.spec Quirks.none cx destination.width value (.memory valPtr) >>= fun _ =>
      CanonicalTree.elements Limits.spec Quirks.none cx destination.width rest mode stride (address + stride) >>= finish

/-- A map value guard stops after its key has run. Flat maps still have the
reached value-width read ahead of them; memory maps use allocation-time placement. -/
def MapValueStop (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
    (entries : List Stored.Endpoints.RecordLower.Field) (stride ptr : Nat)
    (finish : Unit → Session grow sig (Ret (core3 grow))) (stop : Session grow sig (Ret (core3 grow))) : Prop :=
  ∃ leading rest keyField value,
    entries = leading ++ .aggregate (.record (ABI.mapEntryFields key element)) [keyField, value] :: rest ∧
    stop = mapValueSuffix destination inst mode keyField value rest stride (ptr + leading.length * stride) finish

/-- A reached map can stop before entries at fresh preparation, or
after the key of the value currently being visited. -/
def MapReturnStop (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (output : Stored.Lower.Output) (ptr : Nat)
    (finish : output.Result → Session grow sig (Ret (core3 grow))) (stop : Session grow sig (Ret (core3 grow))) : Prop :=
  open Stored.Endpoints.RecordLower ABI in
  let area := layout destination.width (.record (mapEntryFields key element))
  let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
  stop = (PayloadPrefix.canonicalCollectionTail destination inst entries area output ptr mode >>= finish) ∨
  MapValueStop destination inst key element mode entries area.size ptr
    (fun _ => Stored.Endpoints.ListLower.publish (destination.context inst) destination.width ptr entries.length output >>= finish) stop

/-- Complete the actual public replies from a reached allocator return.
Only a returned descriptor rejoins both machines. A typed refusal records
the checked completion and rejoins its caller, leaving canonical suspended
at the actually reached program. A canonical trap executes no reply. -/
def CollectionSegmentReplies (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (checked canonical : Config (core3 grow) (HostState sig))
    (stopsAt : Session grow sig (Ret (core3 grow)) → Prop) (offset : Nat := 1) : Prop :=
  ∃ (outcome : PayloadPrefix.Outcome route.output.Result) (checkLabels canonLabels : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)),
    Steps profile ready (specDispatch ready base) checked checkLabels left ∧
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical canonLabels right ∧
    left.store = right.store ∧ PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
    match outcome with
    | .returned value => ∃ before canonBefore checkBody canonBody,
        checkLabels = checkBody ++ [.tau, .tau, .tau] ∧ canonLabels = canonBody ++ [.tau] ∧
        Steps profile ready (specDispatch ready base) checked checkBody before ∧
        Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical canonBody canonBefore ∧
        (∀ dispatch, Steps profile ready dispatch before [.tau, .tau, .tau] left) ∧
        (∀ dispatch, Steps profile ready dispatch canonBefore [.tau] right) ∧
        left.host = before.host.record (route.reply site.destination site.start.host.nextTicket (.ok value)).1 ∧
        right.host = canonBefore.host ∧ HostFrame.Related.Paired older left right
    | .refused issue => ∃ (before : Config (core3 grow) (HostState sig)) (checkBody : Trace grow sig)
        (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
        (stop : Session grow sig (Ret (core3 grow))), stopsAt stop ∧
        checkLabels = checkBody ++ [.tau, .tau, .tau] ∧
        Steps profile ready (specDispatch ready base) checked checkBody before ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
          canonical (.active 0 (depth + offset)) canonLabels right (.active 0 depth)) ∧
        left.host = before.host.record (route.reply site.destination site.start.host.nextTicket (.error issue)).1 ∧
        (∀ dispatch, Steps profile ready dispatch before [.tau, .tau, .tau] left) ∧ right.ctl = canon.control stop
    | .trapped reason => left.ctl = [] ∧ right.ctl = [] ∧ ∃ leading, PayloadPrefix.visible canonLabels = leading ++ [.trap reason]

/-- A marked string-key map return either traps or refuses before any entry,
or reaches the recursive body with the original checked caller still tracked. -/
def LinkedStringMapReturn (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (pointer : Nat) (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  let checkedDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  CollectionSegmentReplies profile ready base bindings older site checked canonical
    (MapReturnStop site.destination site.inst .string element entries route.output pointer site.referenceReply) ∨
  ∃ (left right : Config (core3 grow) (HostState sig)) (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkLabels canonLabels callerLabels : Trace grow sig),
    RetainsBelowTop profile ready checkedDispatch checked checkLabels left ∧
    RetainsBelowTop profile ready canonDispatch canonical canonLabels right ∧
    PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
    Prefix profile ready checkedDispatch site.checked (.active 0 0) callerLabels left (.active 0 0) ∧
    LinkedStringMapBody profile ready base bindings older site element entries pointer left right check canon

/-- A traversal rooted at the prepared public body. Every reached allocator
prefix has a cumulative comparison. A completed entry advances to the actual
next suffix; a terminal segment carries the original caller result. -/
def LinkedStringMapPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (index basePtr : Nat) (leftStart rightStart left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (seen : Trace grow sig) (offset : Nat := 0) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix ReturnFrame.Occurrence in
  let destination := site.destination
  let cx := destination.context site.inst
  let type : Stored.TypeOf := .record (mapEntryFields .string element)
  let stride := (layout destination.width type).size
  let publish : Session grow sig route.output.Result := Stored.Endpoints.ListLower.publish cx destination.width basePtr entries.length route.output
  let checkNext := checkedSequenceNext (.nested 0) (fun (_ : Unit) => publish >>= fun value => pure (.ok value)) site.reply
  let canonNext := fun (_ : Unit) => publish >>= site.referenceReply
  let terminal := CollectionSegmentReplies profile ready base bindings older site leftStart rightStart
    (MapReturnStop destination site.inst .string element entries route.output basePtr site.referenceReply) offset
  if present : index < entries.length then
    let ptr := basePtr + index * stride
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) route.output
    let rest := entries.drop (index + 1)
    let checkTail := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
      | .error issue => pure (.error issue)
      | .ok () => OwnedMemory.Claims.Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width
          rest stride (ptr + stride) (index + 1)) >>= checkNext
    let canonTail := fun (_ : Unit) => CanonicalTree.elements Limits.spec Quirks.none cx destination.width
      rest mode stride (ptr + stride) >>= canonNext
    ∃ (key : LinkedCallback.StringField) (value : Field), entries[index] = .aggregate type [key.field, value] ∧
      let keyArea := layout destination.width key.field.type
      let keyPtr := alignTo ptr keyArea.alignment
      let afterKey := keyPtr + keyArea.size
      let pending := mapValueProgram destination site.inst mode value afterKey canonTail
      let valuePtr := alignTo afterKey (layout destination.width value.type).alignment
      let report := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => checkTail (verdict.mapError (.nested index))
      let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
        | .error issue => pure (.error issue)
        | .ok () => OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
            value 1 (.memory valuePtr)) >>= report
      let plan := storePlanFor Quirks.none destination.encoding destination.width key.value
      let checkString := fun addr => stringPlanTail cx destination.width (.memory keyPtr) plan addr >>= fun result => checked (.ok result)
      let canonString := fun addr => stringPlanTail cx destination.width (.memory keyPtr) plan addr >>= fun _ => pending
      let checkBody := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checkString) }
      let canonBody := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonString) }
      ComparedSlots profile ready base bindings left right [] checkBody canonBody ∧
      LiveStringPaths profile ready base bindings older cx checkString canonString leftStart rightStart
        (fun _ lhs rhs cursor _ observations => terminal ∨
          ∃ nextLeft nextRight nextCanon suffix,
            ComparedSlots profile ready base bindings lhs rhs suffix nextLeft nextRight ∧
            LinkedStringMapPaths profile ready base bindings older site element entries (index + 1) basePtr
              leftStart rightStart nextLeft nextRight cursor nextCanon (observations ++ suffix) offset)
        plan.steps.length checkBody canonBody check canon seen offset
  else terminal
termination_by entries.length - index

/-- The actual paths after a marked outer allocator return, for either public give.
Before entry, refusal retains the outer frame offset. After entry, each finite
allocator prefix is tracked from the return state and terminal replies use the
original caller. -/
def LinkedStringMapReturnPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (pointer : Nat) (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  CollectionSegmentReplies profile ready base bindings older site checked canonical
    (MapReturnStop site.destination site.inst .string element entries route.output pointer site.referenceReply) ∨
  ∃ left right canon seen, ComparedSlots profile ready base bindings checked canonical seen left right 1 ∧
    LinkedStringMapPaths profile ready base bindings older site element entries 0 pointer checked canonical left right
      check canon seen 1

/-- From the real linked call on the canonical side, compare every classified
outer allocator prefix after checked admission. A natural-pointer return
of the installed occurrence feeds the original replies proof. -/
def LinkedStringMapDispatch (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  let area := layout site.destination.width (.record (mapEntryFields .string element))
  let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) route.output
  let first := checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
  let second := canonicalCollectionResume site.destination site.inst entries area route.output site.referenceReply mode
  let leftEntry := collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first
  let canonical := specDispatch ready (LiveDispatch.host bindings base)
  ∃ leading entered peer, visible leading = [] ∧ Steps profile ready canonical incoming leading entered ∧
    entered.host = incoming.host ∧
    let rightEntry := collectionEntry site.destination site.inst area entries.length canonical entered peer second
    ∀ {seen checked}, ClosedCallbackPrefix bindings profile ready base
        (fun resume => (∃ paired, older resume paired) ∨ resume = first) leftEntry seen checked →
      ∃ checkLabels canonLabels reached mark,
        AllocatorMark profile ready base bindings older leftEntry rightEntry checkLabels canonLabels checked reached mark ∧
        HostFrame.Related.Paired (ReturnFrame.Extend older first second) checked reached ∧
        ComparedPaths profile ready base bindings site.checked incoming seen checked reached ∧
        ∀ pointer check, mark = some (.active 0 0) →
          checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
          LinkedStringMapReturnPaths profile ready base bindings older site element entries pointer checked reached check

abbrev CollectionReplies (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (checked canonical : Config (core3 grow) (HostState sig))
    (childEntry : Session grow sig (Ret (core3 grow))) : Prop :=
  CollectionSegmentReplies profile ready base bindings older site checked canonical (· = childEntry)

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
