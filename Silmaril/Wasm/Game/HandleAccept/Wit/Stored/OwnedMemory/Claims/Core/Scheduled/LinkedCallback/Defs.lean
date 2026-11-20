module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Allocation.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Lift.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open PayloadPrefix
open Stored.Endpoints.RecordLower (Object Field)

abbrev State (grow : SingleThreaded.GrowOracle) (sig : Signature) := Config (core3 grow) (HostState sig)

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

/-- In addition to matching visible labels, replay preserves the older
relation off the selected occurrence. If a mark survives, both actual runs
carry it from the same original coordinate; a dropped mark cannot reappear. -/
def MarkedReplay (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right last : State grow sig) (mark : Option ReturnFrame.Occurrence.Location)
    (seen : List (Label (core3 grow) (HostState sig))) : Prop :=
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  ∃ leftLabels rightLabels other reached,
    CoreGrowthSteps profile ready dispatch left leftLabels last ∧
    CoreGrowthSteps profile ready dispatch right rightLabels other ∧
    HostFrame.Related.Paired changes last other ∧
    visible leftLabels = seen ∧ visible rightLabels = seen ∧
    ReturnFrame.Occurrence.Outside older (ReturnFrame.Occurrence.segmentStorage last)
      (ReturnFrame.Occurrence.segmentStorage other) reached ∧
    ReturnFrame.Occurrence.Trail profile ready dispatch left mark leftLabels last reached ∧
    ReturnFrame.Occurrence.Trail profile ready dispatch right mark rightLabels other reached

/-- Evidence for a give import actually reached within a closed instance.
It includes the reached caller and binding, not agreement of the two writers. -/
structure ClosedGive (bindings : List (Binding sig)) (start : State grow sig) where
  name : String
  type : V1.FuncType
  args : List FlatValue
  inst : InstId
  destination : RecordDestination
  schema : Option TypeOf
  thread : Option ThreadId
  core : (core3 grow).Thread (CanonHost (core3 grow))
  next : List FlatValue → Session grow sig (Ret (core3 grow))
  frames : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  entry : InstState
  parked : start.ctl = ⟨thread, .core core next, frames⟩ :: rest
  calling : (core3 grow).status start.store.core core = .callout (.embedder name type) args
  linked : resolveBinding bindings name type = .ok ⟨name, inst,
    schema.elim (.givePayload destination) (.giveFlat destination)⟩
  caller : Plain.callerInstance start.store thread = .ok (some inst)
  live : start.store.inst? inst = some entry
  closed : entry.mayLeave = false

/-- The checked path records its own ticketed refusal and resumes the actual
Core activation. The allocator's original saved continuation stays parked. -/
def ClosedGive.resume {bindings : List (Binding sig)} {start : State grow sig}
    (callout : ClosedGive bindings start) : State grow sig :=
  let reply := callout.schema.elim (completion start.host.nextTicket (.error .wrongContext))
    (fun payload => flatCompletion start.host.nextTicket (ABI.flatten callout.destination.width payload)
      (.error .wrongContext))
  { start with
    host := (start.host.enter callout.name callout.type callout.args).record reply.1
    ctl := ⟨callout.thread,
      .core ((core3 grow).resume start.store.core callout.core (.values reply.2)) callout.next,
      callout.frames⟩ :: callout.rest }

/-- Only host predicates consulted when filtering this reached instance's
blocked threads must be independent of the writer. Host-independent readiness
policies satisfy this without any invariant on claim, ticket, or journal data. -/
def ReadyAgreement (ready : HostReady (HostState sig)) (start : State grow sig) (inst : InstId) : Prop :=
  ∀ entry, start.store.inst? inst = some entry → ∀ thread ∈ entry.threads.elements,
    ∀ suspended, start.store.thread? thread = some suspended → suspended.blocked = true →
      ∀ query, suspended.readyCond = some (.host query) → ∀ other, ready start.host query = ready other query

/-- A finite checked callback prefix described by reached scheduler steps and
classified linked reentries. It is indexed by visible labels, not a shared
count of internal steps. Unclassified reads are not replayed by this relation. -/
inductive PrefixFor (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop) :
    State grow sig → List (Label (core3 grow) (HostState sig)) → State grow sig → Prop where
  | done (cfg : State grow sig) : PrefixFor profile ready bindings protectedReturn cfg [] cfg
  | step {start next last : State grow sig} {label labels} :
      HostFrame.InteriorFor protectedReturn start → CoreUpdateGrows start →
      Step profile ready (specDispatch ready (host (grow := grow) bindings)) start label next →
      PrefixFor profile ready bindings protectedReturn next labels last →
      PrefixFor profile ready bindings protectedReturn start (PayloadPrefix.visible [label] ++ labels) last
  | closedGive {start last : State grow sig} {labels} (callout : ClosedGive bindings start) :
      PrefixFor profile ready bindings protectedReturn callout.resume labels last →
      PrefixFor profile ready bindings protectedReturn start labels last
  | syncReady {start last : State grow sig} {labels task inst thread frames rest}
      (focused : start.ctl = ⟨thread, .prog (.op .hostGet (fun current =>
        syncLiftCandidates task (start.store.instCandidates (ready current) inst))), frames⟩ :: rest)
      (agrees : ReadyAgreement ready start inst) :
      PrefixFor profile ready bindings protectedReturn { start with ctl := ⟨thread,
        .prog (syncLiftCandidates task (start.store.instCandidates (ready start.host) inst)), frames⟩ :: rest }
        labels last →
      PrefixFor profile ready bindings protectedReturn start labels last

abbrev Prefix (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig)) :=
  PrefixFor profile ready bindings (· = resume)

/-- Continue a designated allocator return using its measured width and size.
The tail rule receives the alignment, bounds, and live-plan facts only after
the corresponding checks actually accept. -/
def ReachedCollectionTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (destination : RecordDestination) (inst : InstId)
    (entries : List Stored.Endpoints.RecordLower.Field) (area : Layout) (output : Stored.Lower.Output)
    (index pointer : Nat) (checked : State grow sig) : Prop :=
  ∀ (reference : State grow sig) (bytes : Nat),
    ptrTypeIn checked.store (destination.context inst) = destination.width →
    (core3 grow).memSize? checked.store.core destination.memory = some bytes →
    PayloadPrefix.CollectionTailAt profile ready (specDispatch ready (host bindings)) destination inst entries area
      output index pointer bytes checked reference

/-- The observed pop was of an unchanged frame and the two allocator
executions are still paired. -/
def CollectionCommonPopOver (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right afterPop : State grow sig) (seen : List (Label (core3 grow) (HostState sig))) : Prop :=
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  ∃ leftLabels rightLabels other,
    Steps profile ready dispatch left leftLabels afterPop ∧ Steps profile ready dispatch right rightLabels other ∧
    HostFrame.Related.Paired changes afterPop other ∧
    PayloadPrefix.visible leftLabels = seen ∧ PayloadPrefix.visible rightLabels = seen

abbrev CollectionCommonPop (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (first second : ReturnFrame.Continuation (core3 grow) (HostState sig)) :=
  CollectionCommonPopOver profile ready bindings (ReturnFrame.Only first second)

/-- The frame at a reached child entry. Blocked activations and the cursor
tails can still contain substituted return frames; only the store and the
pending, result, and cancellation data must be equal. -/
structure ChildFrameOver (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right : State grow sig) (check canon : Cursor (E := core3 grow) (HostState sig)) : Prop where
  store : left.store = right.store
  pending : left.pending = right.pending
  results : left.results = right.results
  cancels : left.cancels = right.cancels
  blocked : List.Forall₂ (ReturnFrame.Related.Saved changes) left.conts right.conts
  thread : check.thread = canon.thread
  frames : List.Forall₂ (ReturnFrame.Related.Segment changes) check.frames canon.frames
  rest : List.Forall₂ (ReturnFrame.Related.Active changes) check.rest canon.rest

abbrev ChildFrame (first second : ReturnFrame.Continuation (core3 grow) (HostState sig)) :=
  ChildFrameOver (ReturnFrame.Only first second)

/-- A reached pop either consumes a paired substitution (not necessarily
the newest one), or executes the unchanged continuation on both sides.
The residual cursor and blocked frames retain the installed relation. -/
inductive CallbackReturnFor (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right last : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (value : Ret (core3 grow)) (seen : List (Label (core3 grow) (HostState sig))) : Prop where
  | substituted {reference : State grow sig} {canonCursor : Cursor (E := core3 grow) (HostState sig)}
      {canonResume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
      {checkLabels canonLabels : List (Label (core3 grow) (HostState sig))}
      (edge : changes resume canonResume)
      (frame : ChildFrameOver changes last reference cursor canonCursor)
      (checked : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) left checkLabels
        { last with ctl := cursor.control (resume value) })
      (canonical : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) right canonLabels
        { reference with ctl := canonCursor.control (canonResume value) })
      (checkSeen : visible checkLabels = seen) (canonSeen : visible canonLabels = seen) :
      CallbackReturnFor profile ready bindings changes left right last cursor resume value seen
  | common {reference : State grow sig} {checkLabels canonLabels : List (Label (core3 grow) (HostState sig))}
      (checked : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) left checkLabels
        { last with ctl := cursor.control (resume value) })
      (canonical : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) right canonLabels reference)
      (paired : HostFrame.Related.Paired changes { last with ctl := cursor.control (resume value) } reference)
      (checkSeen : visible checkLabels = seen) (canonSeen : visible canonLabels = seen) :
      CallbackReturnFor profile ready bindings changes left right last cursor resume value seen

/-- A classified callback has reached a pop. Only a pop of the substituted
frame enters the two distinct continuations. No validation or tail code
has run yet, and both continuations use their reached stores. -/
inductive CallbackReturn (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (left right last : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (value : Ret (core3 grow)) (seen : List (Label (core3 grow) (HostState sig))) : Prop where
  | designated {reference : State grow sig} {canonCursor : Cursor (E := core3 grow) (HostState sig)}
      {checkLabels canonLabels : List (Label (core3 grow) (HostState sig))}
      (frame : ChildFrame first second last reference cursor canonCursor)
      (checked : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) left checkLabels
        { last with ctl := cursor.control (first value) })
      (canonical : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) right canonLabels
        { reference with ctl := canonCursor.control (second value) })
      (checkSeen : visible checkLabels = seen) (canonSeen : visible canonLabels = seen) :
      CallbackReturn profile ready bindings first second left right last cursor value seen
  | common {reference : State grow sig} {checkLabels canonLabels : List (Label (core3 grow) (HostState sig))}
      (checked : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) left checkLabels
        { last with ctl := cursor.control (first value) })
      (canonical : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) right canonLabels reference)
      (paired : HostFrame.Paired first second { last with ctl := cursor.control (first value) } reference)
      (checkSeen : visible checkLabels = seen) (canonSeen : visible canonLabels = seen) :
      CallbackReturn profile ready bindings first second left right last cursor value seen

/-- The actual activation entered by one canonical string allocation step. -/
def stringReallocEntry (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat) (alignment : Alignment) (size : Nat)
    (steps : List StoreStep) (finish : Nat → Session grow sig (Ret (core3 grow)))
    (start : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig)) : State grow sig :=
  let request := Call.reallocate cx (oldSize.elim 0 (fun _ => ptr)) (oldSize.getD 0) alignment.bytes size
  let entered := { cursor with frames := .prog (stringPlanResume cx steps finish) :: cursor.frames }
  { start with ctl := entered.control (specDispatch ready (host bindings) request) }

/-- Compare the next local phase of a string and either reach its descriptor
continuation, trap, or enter the actual allocator with the strictly shorter plan saved on
both sides. Entering the allocator does not imply a return. -/
inductive StringPlanCut (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (cx : LiftLowerContext (core3 grow))
    (length : Nat) (left right : State grow sig) (check canon : Cursor (E := core3 grow) (HostState sig))
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow))) : Prop where
  | done (localRun : StringLocalCut profile ready (specDispatch ready (host bindings)) left right check canon
      checkNext canonNext) : StringPlanCut profile ready bindings changes cx length left right check canon checkNext canonNext
  | installed (ptr : Nat) (oldSize : Option Nat) (alignment : Alignment) (size : Nat) (rest : List StoreStep)
      (shorter : rest.length < length) {store : CStore (core3 grow)} {labels : List (Label (core3 grow) (HostState sig))}
      (checked : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) left labels
        (stringReallocEntry ready bindings cx ptr oldSize alignment size rest checkNext { left with store } check))
      (canonical : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) right labels
        (stringReallocEntry ready bindings cx ptr oldSize alignment size rest canonNext { right with store } canon))
      (silent : LocalLeafLabels (.ok ()) labels)
      (tracked : ∀ depth,
        ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (host bindings)) left (.active 0 depth) labels
          (stringReallocEntry ready bindings cx ptr oldSize alignment size rest checkNext { left with store } check)
          (.active 0 (depth + 1)) ∧
        ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (host bindings)) right (.active 0 depth) labels
          (stringReallocEntry ready bindings cx ptr oldSize alignment size rest canonNext { right with store } canon)
          (.active 0 (depth + 1)))
      (paired : HostFrame.Related.Paired (ReturnFrame.Extend changes (stringPlanResume cx rest checkNext)
          (stringPlanResume cx rest canonNext))
        (stringReallocEntry ready bindings cx ptr oldSize alignment size rest checkNext { left with store } check)
        (stringReallocEntry ready bindings cx ptr oldSize alignment size rest canonNext { right with store } canon))
      (outside : ReturnFrame.Occurrence.Outside changes
        (ReturnFrame.Occurrence.segmentStorage
          (stringReallocEntry ready bindings cx ptr oldSize alignment size rest checkNext { left with store } check))
        (ReturnFrame.Occurrence.segmentStorage
          (stringReallocEntry ready bindings cx ptr oldSize alignment size rest canonNext { right with store } canon))
        (some (.active 0 0))) :
        StringPlanCut profile ready bindings changes cx length left right check canon checkNext canonNext

/-- A string can stop during any classified finite callback prefix, including
a prefix that never returns. A reached pop at the selected occurrence supplies
the same pointer to both saved suffixes; continuation of the comparison uses
the strictly shorter plan, not a fresh assumption about the child. -/
inductive StringReplayLayer (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (cx : LiftLowerContext (core3 grow))
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (finish : State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Nat → Prop) (length : Nat)
    (smaller : (remaining : Nat) → remaining < length → State grow sig → State grow sig →
      Cursor (E := core3 grow) (HostState sig) → Cursor (E := core3 grow) (HostState sig) → Prop) :
    State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Prop where
  | done {left right check canon} {store : CStore (core3 grow)} {result : Except TrapReason Nat} {labels}
      (silent : LocalLeafLabels result labels)
      (checked : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) left labels
        (localLeafEnd left left.host store check.thread check.frames check.rest checkNext result))
      (canonical : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) right labels
        (localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result))
      (tracked : ∀ pointer, result = .ok pointer → ∀ depth,
        ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (host bindings)) left (.active 0 depth) labels
          { left with store, ctl := check.control (checkNext pointer) } (.active 0 depth) ∧
        ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (host bindings)) right (.active 0 depth) labels
          { right with store, ctl := canon.control (canonNext pointer) } (.active 0 depth))
      (finished : ∀ pointer, result = .ok pointer → finish
        { left with store, ctl := check.control (checkNext pointer) }
        { right with store, ctl := canon.control (canonNext pointer) } check canon pointer) :
        StringReplayLayer profile ready bindings older cx checkNext canonNext finish length smaller left right check canon
  | allocated {left right check canon} (ptr : Nat) (oldSize : Option Nat) (alignment : Alignment) (size : Nat)
      (rest : List StoreStep) (shorter : rest.length < length) {store : CStore (core3 grow)} {labels}
      (checked : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) left labels
        (stringReallocEntry ready bindings cx ptr oldSize alignment size rest checkNext { left with store } check))
      (canonical : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) right labels
        (stringReallocEntry ready bindings cx ptr oldSize alignment size rest canonNext { right with store } canon))
      (silent : LocalLeafLabels (.ok ()) labels)
      (tracked : ∀ depth,
        ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (host bindings)) left (.active 0 depth) labels
          (stringReallocEntry ready bindings cx ptr oldSize alignment size rest checkNext { left with store } check)
          (.active 0 (depth + 1)) ∧
        ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (host bindings)) right (.active 0 depth) labels
          (stringReallocEntry ready bindings cx ptr oldSize alignment size rest canonNext { right with store } canon)
          (.active 0 (depth + 1)))
      (replay :
        let dispatch := specDispatch ready (host (grow := grow) bindings)
        let leftEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size rest checkNext { left with store } check
        let rightEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size rest canonNext { right with store } canon
        let first := stringPlanResume cx rest checkNext
        let second := stringPlanResume cx rest canonNext
        let changes := ReturnFrame.Extend older first second
        ∀ {last seen protectedReturn}, PrefixFor profile ready bindings protectedReturn leftEntry seen last →
          (∀ left right, changes left right → protectedReturn left) →
          ∃ leftLabels rightLabels other mark,
            CoreGrowthSteps profile ready dispatch leftEntry leftLabels last ∧
            CoreGrowthSteps profile ready dispatch rightEntry rightLabels other ∧
            visible leftLabels = seen ∧ visible rightLabels = seen ∧
            HostFrame.Related.Paired changes last other ∧
            ReturnFrame.Occurrence.Trail profile ready dispatch leftEntry (some (.active 0 0)) leftLabels last mark ∧
            ReturnFrame.Occurrence.Trail profile ready dispatch rightEntry (some (.active 0 0)) rightLabels other mark ∧
            (∀ value cursor, mark = some (ReturnFrame.Occurrence.Location.active 0 0) →
              last.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat value)) →
              ∃ otherCursor,
                let after := { last with ctl := cursor.control (runStoreSteps cx value rest >>= checkNext) }
                let otherAfter := { other with ctl := otherCursor.control (runStoreSteps cx value rest >>= canonNext) }
                Step profile ready dispatch last .tau after ∧ Step profile ready dispatch other .tau otherAfter ∧
                (∀ depth,
                  ReturnFrame.Occurrence.Prefix profile ready dispatch left (.active 0 depth)
                    (labels ++ (leftLabels ++ [.tau])) after (.active 0 depth) ∧
                  ReturnFrame.Occurrence.Prefix profile ready dispatch right (.active 0 depth)
                    (labels ++ (rightLabels ++ [.tau])) otherAfter (.active 0 depth)) ∧
                smaller rest.length shorter after otherAfter cursor otherCursor)) :
        StringReplayLayer profile ready bindings older cx checkNext canonNext finish length smaller left right check canon

def StringReplay (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (cx : LiftLowerContext (core3 grow))
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow))) (length : Nat)
    (left right : State grow sig) (check canon : Cursor (E := core3 grow) (HostState sig))
    (finish : State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Nat → Prop := fun _ _ _ _ _ => True) : Prop :=
  StringReplayLayer profile ready bindings older cx checkNext canonNext finish length
    (fun remaining _ lhs rhs checked canonical =>
      StringReplay profile ready bindings older cx checkNext canonNext remaining lhs rhs checked canonical finish)
    left right check canon
termination_by length

/-- Compare a shared local result segment. Successful execution tracks the
active slots into the next consumer; traps retain the reached lockdown. -/
def LocalThen {Result : Type} (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (left right : State grow sig) (check canon : Cursor (E := core3 grow) (HostState sig))
    (checkNext canonNext : Result → Session grow sig (Ret (core3 grow)))
    (next : Result → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Prop) : Prop :=
  let dispatch := specDispatch ready (host bindings)
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason Result) (labels : List (Label (core3 grow) (HostState sig))),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest checkNext
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext
    LocalLeafLabels result labels ∧ CoreGrowthSteps profile ready dispatch left labels (lhs result) ∧
    CoreGrowthSteps profile ready dispatch right labels (rhs result) ∧
    ∀ value, result = .ok value →
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch left labels (lhs (.ok value)) ∧
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch right labels (rhs (.ok value)) ∧
      next value (lhs (.ok value)) (rhs (.ok value)) check canon

/-- A string field installs the actual plan, allows suspended callback
prefixes, and starts the next comparison only after its own result succeeds. -/
def StringFieldThen (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (str : Value.StrVal) (output : Stored.Lower.Output) (left right : State grow sig)
    (check canon : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (next : output.Result → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Prop) : Prop :=
  let dispatch := specDispatch ready (host bindings)
  let cx := destination.context inst
  let plan := storePlanFor Quirks.none destination.encoding destination.width str
  let checked := fun ptr => stringPlanTail cx destination.width output plan ptr >>= fun value => checkNext (.ok value)
  let canonical := fun ptr => stringPlanTail cx destination.width output plan ptr >>= canonNext
  let lhs := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checked) }
  let rhs := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonical) }
  ∃ reads, ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch left (List.replicate reads .tau) lhs ∧
    ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch right [.tau] rhs ∧
    StringReplay profile ready bindings older cx checked canonical plan.steps.length lhs rhs check canon
      (fun lhs rhs check canon _ => LocalThen profile ready bindings lhs rhs check canon
        (fun value => checkNext (.ok value)) canonNext next)

structure StringField where
  value : Value.StrVal
  valid : value.Valid

def StringField.field (item : StringField) : Field := .data (.prim .string) ⟨.string item.value, .string item.valid⟩

/-- On refusal only the checked live guard advances, retaining the caller
slots. On success the same slots reach the next field along with the spent
writer and the reached canonical store. On trap neither side enters a success
continuation, and the reached effects are retained. -/
def HandleFieldThen (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (item : Field) (index : Nat) (output : Stored.Lower.Output) (left right : State grow sig)
    (check canon : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (next : output.Result → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Prop) : Prop :=
  let dispatch := specDispatch ready (host bindings)
  match liveLeafPlan left.store left.host.writer index item with
  | .error issue => ∃ labels, (∀ label ∈ labels, label = .tau) ∧ ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch left labels
      { left with ctl := check.control (checkNext (.error issue)) }
  | .ok plan =>
    let spent := plan.elim left.host (fun spend => { left.host with writer := spend.apply left.host.writer })
    ∃ (store : CStore (core3 grow)) (result : Except TrapReason output.Result)
      (leading checkLabels canonLabels : List (Label (core3 grow) (HostState sig))),
      (∀ label ∈ leading, label = .tau) ∧ LocalLeafLabels result checkLabels ∧ LocalLeafLabels result canonLabels ∧
      Steps profile ready dispatch left (leading ++ checkLabels)
        (localLeafEnd left spent store check.thread check.frames check.rest (fun value => checkNext (.ok value)) result) ∧
      Steps profile ready dispatch right canonLabels
        (localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result) ∧
      ∀ value, result = .ok value →
        let lhs := { left with store, host := spent, ctl := check.control (checkNext (.ok value)) }
        let rhs := { right with store, ctl := canon.control (canonNext value) }
        ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch left (leading ++ checkLabels) lhs ∧
        ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch right canonLabels rhs ∧
        next value lhs rhs check canon

def flatSequenceChecked (destination : RecordDestination) (inst : InstId) (items : List Field) (index : Nat)
    (leading : List FlatValue) (finish : Except Endpoints.RecordLower.Issue (List FlatValue) → Session grow sig (Ret (core3 grow))) :
    Session grow sig (Ret (core3 grow)) :=
  Record.Effects.flat recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
    items index >>= fun verdict => finish (verdict.map (leading ++ ·))

def flatSequenceCanonical (destination : RecordDestination) (inst : InstId) (items : List Field)
    (leading : List FlatValue) (finish : List FlatValue → Session grow sig (Ret (core3 grow))) : Session grow sig (Ret (core3 grow)) :=
  Stored.Endpoints.RecordLower.CanonicalTree.flat Limits.spec Quirks.none (destination.context inst) destination.width
    items >>= fun words => finish (leading ++ words)

abbrev FlatSequenceCheckNext (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Except Endpoints.RecordLower.Issue (List FlatValue) → Session grow sig (Ret (core3 grow))

abbrev FlatSequenceCanonNext (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  List FlatValue → Session grow sig (Ret (core3 grow))

abbrev FlatResultCut (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  List FlatValue → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
    Cursor (E := core3 grow) (HostState sig) → Prop

/-- A field comparison accepts an obligation for its common-success cut.
Other exits, including stopped prefixes, are described by the comparison. -/
abbrev FlatFieldComparison (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Field → Nat → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
    Cursor (E := core3 grow) (HostState sig) → FlatSequenceCheckNext grow sig → FlatSequenceCanonNext grow sig → FlatResultCut grow sig → Prop

def FlatFieldRule (compare : FlatFieldComparison grow sig)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (destination : RecordDestination) (inst : InstId) (item : Field) : Prop :=
  ∀ index (checkNext : FlatSequenceCheckNext grow sig) (canonNext : FlatSequenceCanonNext grow sig) left right check canon,
    ChildFrameOver older left right check canon → Core3.Grows origin.core left.store.core →
    left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index .flat >>= checkNext) →
    right.ctl = canon.control (Stored.Endpoints.RecordLower.CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width item .flat >>= canonNext) →
    ∀ next, (∀ words reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok words)) →
      reference.ctl = canon.control (canonNext words) → next words reached reference check canon) →
    compare item index left right check canon checkNext canonNext next

/-- Recursive comparison of the actual flat lowering sequence. Each
succeeding sibling starts only at its predecessor's common-success cut. -/
def FlatSequenceReplay (compare : FlatFieldComparison grow sig)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (checkNext : FlatSequenceCheckNext grow sig) (canonNext : FlatSequenceCanonNext grow sig) (finish : FlatResultCut grow sig)
    (items : List Field) (index : Nat)
    (leading : List FlatValue) (left right : State grow sig) (check canon : Cursor (E := core3 grow) (HostState sig)) : Prop :=
  match items with
  | [] => finish leading left right check canon
  | item :: rest =>
    compare item index left right check canon
      (fun verdict => match verdict with
        | .error issue => checkNext (.error issue)
        | .ok words => flatSequenceChecked destination inst rest (index + 1) (leading ++ words) checkNext)
      (fun words => flatSequenceCanonical destination inst rest (leading ++ words) canonNext)
      (fun words reached reference check canon => FlatSequenceReplay compare older destination inst
        checkNext canonNext finish rest (index + 1) (leading ++ words) reached reference check canon)
termination_by structural items

def FlatAggregateThen (compare : FlatFieldComparison grow sig)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (children : List Field) (index : Nat) (left right : State grow sig) (check canon : Cursor (E := core3 grow) (HostState sig))
    (checkNext : FlatSequenceCheckNext grow sig) (canonNext : FlatSequenceCanonNext grow sig) (finish : FlatResultCut grow sig) : Prop :=
  FlatSequenceReplay compare older destination inst (fun verdict => checkNext (verdict.mapError (.nested index)))
    canonNext finish children 0 [] left right check canon

def LocalFieldThen (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (output : Stored.Lower.Output) (left right : State grow sig) (check canon : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (finish : output.Result → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Prop) : Prop :=
  ∃ store result checkLabels canonLabels,
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest (fun value => checkNext (.ok value)) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result
    Steps profile ready (specDispatch ready (host bindings)) left checkLabels lhs ∧
    Steps profile ready (specDispatch ready (host bindings)) right canonLabels rhs ∧
    visible checkLabels = visible canonLabels ∧
    match result with
    | .ok value =>
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (host bindings)) left checkLabels lhs ∧
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (host bindings)) right canonLabels rhs ∧
      finish value lhs rhs check canon
    | .error reason => ∃ leading, visible canonLabels = leading ++ [.trap reason]

def flatSumTail (width : AddrType) (type : TypeOf) (count tag : Nat) (haves : List CoreType) (words : List FlatValue) :
    Session grow sig (List FlatValue) :=
  lowerFlatVariantWith count ((flatten width type).drop 1) tag haves (pure words)

def flatSumCheckNext (width : AddrType) (type : TypeOf) (count tag index : Nat) (haves : List CoreType)
    (next : FlatSequenceCheckNext grow sig) : FlatSequenceCheckNext grow sig
  | .error issue => next (.error (.nested index issue))
  | .ok words => flatSumTail width type count tag haves words >>= fun coerced => next (.ok coerced)

def FlatSumThen (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (compare : FlatFieldComparison grow sig) (width : AddrType) (type : TypeOf) (count tag : Nat) (selected : Option Field)
    (index : Nat) (left right : State grow sig) (check canon : Cursor (E := core3 grow) (HostState sig))
    (checkNext : FlatSequenceCheckNext grow sig) (canonNext : FlatSequenceCanonNext grow sig) (finish : FlatResultCut grow sig) : Prop :=
  let tailAt := fun haves words (reached reference : State grow sig) (check canon : Cursor (E := core3 grow) (HostState sig)) =>
    let body := flatSumTail width type count tag haves words
    reached.ctl = check.control (body >>= fun coerced => checkNext (.ok coerced)) ∧
    reference.ctl = canon.control (body >>= canonNext) ∧
    LocalFieldThen profile ready bindings .flat reached reference check canon checkNext canonNext finish
  match selected with
  | none => tailAt [] [] left right check canon
  | some child =>
    let haves := flatten width child.type
    compare child 0 left right check canon (flatSumCheckNext width type count tag index haves checkNext)
      (fun words => flatSumTail width type count tag haves words >>= canonNext) (tailAt haves)

def flatChildren : Field → Option (List Field)
  | .aggregate _ children | .fixed _ _ children => some children
  | .sum _ _ _ selected => some selected.toList
  | _ => none

/-- Depth bounds only aggregate and selected-arm descent; the caller's leaf rule handles
other fields, including their own independently justified return cuts. -/
def FlatNestedFits (leaf : Field → Prop) : Nat → Field → Prop
  | 0, field => leaf field
  | depth + 1, field => match flatChildren field with
    | none => leaf field
    | some children => ∀ child ∈ children, FlatNestedFits leaf depth child

def FlatTagBounds (field : Field) : Prop :=
  ∀ {type arms tag selected}, field.Descendant (.sum type arms tag selected) → tag < arms.length

def nestedFlatComparison (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (leaves : FlatFieldComparison grow sig)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    Nat → FlatFieldComparison grow sig
  | 0 => leaves
  | depth + 1 => fun field index left right check canon checkNext canonNext finish => match flatChildren field with
    | none => leaves field index left right check canon checkNext canonNext finish
    | some children =>
      let compare := nestedFlatComparison profile ready bindings leaves older destination inst depth
      match field with
      | .sum type arms tag selected => FlatSumThen profile ready bindings compare destination.width type arms.length tag selected
          index left right check canon checkNext canonNext finish
      | _ => FlatAggregateThen compare older destination inst children index left right check canon checkNext canonNext finish

def stringFlatComparison (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    FlatFieldComparison grow sig :=
  fun field _ left right check canon checkNext canonNext next =>
    ∃ item : StringField, item.field = field ∧
      StringFieldThen profile ready bindings older destination inst item.value .flat left right check canon checkNext canonNext next

def StringField.Fits (destination : RecordDestination) (field : Field) : Prop :=
  ∃ item : StringField, item.field = field ∧ StoreStringPre Quirks.none destination.encoding destination.width item.value

def mixedFlatComparison (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    FlatFieldComparison grow sig :=
  fun field index left right check canon checkNext canonNext next =>
    (CanonicalHandle field ∧ HandleFieldThen profile ready bindings field index .flat left right check canon checkNext canonNext next) ∨
    stringFlatComparison profile ready bindings older destination inst field index left right check canon checkNext canonNext next

/-- The actual callback prefix and its local return suffix, with exact labels
and the older active slots tracked through the pop and subsequent checks. -/
def ReturnRangeTrace (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (start reached : State grow sig) (labels : List (Label (core3 grow) (HostState sig))) (after : State grow sig)
    (mark : Option ReturnFrame.Occurrence.Location) : Prop :=
  let dispatch := specDispatch ready (host bindings)
  ∃ lead tail, labels = lead ++ tail ∧ Steps profile ready dispatch start lead reached ∧
    ReturnFrame.Occurrence.Trail profile ready dispatch start mark lead reached mark ∧
    ReturnFrame.Occurrence.RetainsBelowTop profile ready dispatch reached tail after

/-- Stop at the reached range/recheck cut without executing any children.
On a valid range the checked continuation receives the real live verdict
(which can refuse); the canonical continuation receives only the pointer.
Neither side rewinds callback effects. -/
inductive RangeCutOver (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (left right last : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (destination : RecordDestination) (area : Layout) (count pointer : Nat) (plan : List Object)
    (checkNext : Nat → Except Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow))) (seen : List (Label (core3 grow) (HostState sig)))
    (allowCommon : Prop := True) (mark : Option ReturnFrame.Occurrence.Location := none) : Prop where
  | reached {reference : State grow sig} {canonCursor : Cursor (E := core3 grow) (HostState sig)} {bytes : Nat}
      {checkLabels canonLabels : List (Label (core3 grow) (HostState sig))}
      (width : (core3 grow).memAddrType? last.store.core destination.memory = some destination.width)
      (sized : (core3 grow).memSize? last.store.core destination.memory = some bytes)
      (aligned : pointer = alignTo pointer area.alignment) (bounds : pointer + count * area.size ≤ bytes)
      (frame : ChildFrameOver changes last reference cursor canonCursor)
      (growth : Core3.Grows left.store.core last.store.core)
      (checked : ReturnRangeTrace profile ready bindings left last checkLabels
        { last with ctl := cursor.control (checkNext pointer (Record.prepare last.store last.host.writer plan)) } mark)
      (canonical : ReturnRangeTrace profile ready bindings right reference canonLabels
        { reference with ctl := canonCursor.control (canonNext pointer) } mark)
      (checkSeen : visible checkLabels = seen) (canonSeen : visible canonLabels = seen) :
      RangeCutOver profile ready bindings changes resume left right last cursor destination area count pointer plan checkNext canonNext seen allowCommon mark
  | trapped {reference : State grow sig} {reason : TrapReason}
      {checkLabels canonLabels : List (Label (core3 grow) (HostState sig))}
      (stores : last.store = reference.store)
      (checked : Steps profile ready (specDispatch ready (host bindings)) left checkLabels (StepDefs.trapCfg last))
      (canonical : Steps profile ready (specDispatch ready (host bindings)) right canonLabels (StepDefs.trapCfg reference))
      (checkSeen : visible checkLabels = seen ++ [.trap reason]) (canonSeen : visible canonLabels = seen ++ [.trap reason]) :
      RangeCutOver profile ready bindings changes resume left right last cursor destination area count pointer plan checkNext canonNext seen allowCommon mark
  | common (pop : CollectionCommonPopOver profile ready bindings changes left right
      { last with ctl := cursor.control (resume (.nat pointer)) } seen) (allowed : allowCommon) :
      RangeCutOver profile ready bindings changes resume left right last cursor destination area count pointer plan checkNext canonNext seen allowCommon mark

abbrev RangeCut (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig)) :=
  RangeCutOver profile ready bindings (ReturnFrame.Only first second) first

/-- Replay finite prefixes of a dynamic collection's actual linked allocation.
Only a natural return to the installed occurrence requires the tail property. -/
def CollectionReplayFor (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf) (entries : List Field)
    (index : Nat) (output : Stored.Lower.Output) (left right : State grow sig)
    (check canon : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (returned : State grow sig → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Nat → List (Label (core3 grow) (HostState sig)) → Prop) : Prop :=
  let dispatch := specDispatch ready (host bindings)
  let area := layout destination.width element
  let mode := Stored.Endpoints.RecordLower.CanonicalTree.EntryMode.forOutput destination.width type output
  let first := checkedCollectionResume destination inst entries area index output checkNext
  let second := canonicalCollectionResume destination inst entries area output canonNext mode
  let checked := collectionEntry destination inst area entries.length dispatch left check first
  let canonical := collectionEntry destination inst area entries.length dispatch right canon second
  let changes := ReturnFrame.Extend older first second
  (∀ depth, ReturnFrame.Occurrence.Prefix profile ready dispatch left (.active 0 depth)
    [.tau, .tau, .tau] checked (.active 0 (depth + 1))) ∧
  (∀ depth, ReturnFrame.Occurrence.Prefix profile ready dispatch right (.active 0 depth)
    [.tau, .tau] canonical (.active 0 (depth + 1))) ∧
  ∀ {last seen protectedReturn}, PrefixFor profile ready bindings protectedReturn checked seen last →
    (∀ first second, changes first second → protectedReturn first) →
    ∃ leftLabels rightLabels other mark,
      CoreGrowthSteps profile ready dispatch checked leftLabels last ∧
      CoreGrowthSteps profile ready dispatch canonical rightLabels other ∧
      visible leftLabels = seen ∧ visible rightLabels = seen ∧
      HostFrame.Related.Paired changes last other ∧
      ReturnFrame.Occurrence.Trail profile ready dispatch checked (some (.active 0 0)) leftLabels last mark ∧
      ReturnFrame.Occurrence.Trail profile ready dispatch canonical (some (.active 0 0)) rightLabels other mark ∧
      ∀ pointer cursor, mark = some (ReturnFrame.Occurrence.Location.active 0 0) →
        last.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) →
        returned checked canonical last cursor pointer seen

/-- On an actual return to the installed occurrence, expose the paired range
check and live recheck, with older frames restored. No return is required. -/
def CollectionReplay (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf) (entries : List Field)
    (index : Nat) (output : Stored.Lower.Output) (left right : State grow sig)
    (check canon : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow))) : Prop :=
  let area := layout destination.width element
  let mode := Stored.Endpoints.RecordLower.CanonicalTree.EntryMode.forOutput destination.width type output
  let first := checkedCollectionResume destination inst entries area index output checkNext
  CollectionReplayFor profile ready bindings older destination inst type element entries index output left right check canon checkNext canonNext
    fun checked canonical last cursor pointer seen =>
      RangeCutOver profile ready bindings older first checked canonical last cursor destination area entries.length pointer
        (Field.listObjects entries) (fun ptr live => checkedCollectionTail destination inst entries area index output ptr live >>= checkNext)
        (fun ptr => canonicalCollectionTail destination inst entries area output ptr mode >>= canonNext) seen False (some (.active 0 0))

/-- Allocator descent from the two actual dynamic-field programs. The cut
hands the entry interpreters back to the caller rather than requiring
that any allocating descendants return. -/
def CollectionDescent (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf) (entries : List Field)
    (output : Stored.Lower.Output) (index : Nat) (left right : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow))) : Prop :=
  let dispatch := specDispatch ready (host bindings)
  let area := layout destination.width element
  let mode := Stored.Endpoints.RecordLower.CanonicalTree.EntryMode.forOutput destination.width type output
  let first := checkedCollectionResume destination inst entries area index output checkNext
  let second := canonicalCollectionResume destination inst entries area output canonNext mode
  let installed := collectionEntry destination inst area entries.length dispatch left cursor first
  let reference := collectionEntry destination inst area entries.length dispatch right cursor second
  Steps profile ready dispatch left [.tau, .tau, .tau] installed ∧
  Steps profile ready dispatch right [.tau, .tau] reference ∧
  HostFrame.Paired first second installed reference ∧
  ∀ {last seen}, Prefix profile ready bindings first installed seen last →
    ∀ (reached : Cursor (E := core3 grow) (HostState sig)) (pointer : Nat),
      last.ctl = { reached with frames := .prog first :: reached.frames }.control (pure (.nat pointer)) →
      RangeCut profile ready bindings first second installed reference last reached destination area entries.length pointer
        (Field.listObjects entries)
        (fun ptr live => checkedCollectionTail destination inst entries area index output ptr live >>= checkNext)
        (fun ptr => canonicalCollectionTail destination inst entries area output ptr mode >>= canonNext) seen

/-- Either the collection comparison has reached its continuations (or a
refused/trapping prefix), or the observed pop was of an unchanged frame. -/
def CollectionCut {Result : Type} (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (left right afterPop : State grow sig) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (seen : List (Label (core3 grow) (HostState sig))) : Prop :=
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  (∃ canonCursor, canonCursor.thread = cursor.thread ∧
    PayloadPrefix.Reaches profile ready dispatch left right cursor canonCursor checkNext canonNext) ∨
  CollectionCommonPop profile ready bindings first second left right afterPop seen

/-- A cut that supplies a reached continuation invariant on successful
completion, without treating other cuts as completion. -/
def CollectionCutKeeping {Result : Type} (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (keep : CStore (core3 grow) → Prop)
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (left right afterPop : State grow sig) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (seen : List (Label (core3 grow) (HostState sig))) : Prop :=
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  (∃ canonCursor, canonCursor.thread = cursor.thread ∧
    PayloadPrefix.ReachesKeeping profile ready dispatch keep left right cursor canonCursor checkNext canonNext) ∨
  CollectionCommonPop profile ready bindings first second left right afterPop seen

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
