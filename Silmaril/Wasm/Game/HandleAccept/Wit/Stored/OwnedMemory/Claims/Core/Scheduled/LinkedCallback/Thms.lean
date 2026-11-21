module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Execution.Core
open Stored.Endpoints Stored.Endpoints.RecordLower
open PayloadPrefix

variable {grow : Silmaril.Wasm.SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}
  {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}

/-- Installing paired allocator continuations excludes only the newly pushed
occurrence from the older relation. The dispatched focuses need not agree for
this storage fact. -/
theorem ChildFrameOver.outside_installed {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (checkBody canonBody : Session grow sig (Ret (core3 grow))) :
    ReturnFrame.Occurrence.Outside older
      (ReturnFrame.Occurrence.segmentStorage { left with ctl := { check with frames := .prog first :: check.frames }.control checkBody })
      (ReturnFrame.Occurrence.segmentStorage { right with ctl := { canon with frames := .prog second :: canon.frames }.control canonBody })
      (some (.active 0 0)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.childFrameOutside frame checkBody first second

/-- Expose the reached pop foci and the residual pairing before running either
of the two continuations, independently of dispatch. -/
theorem marked_pop_frame {older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : State grow sig} {check : Cursor (E := core3 grow) (HostState sig)} {value : Ret (core3 grow)}
    (paired : HostFrame.Related.Paired wider left right)
    (outside : ReturnFrame.Occurrence.Outside older (ReturnFrame.Occurrence.segmentStorage left)
      (ReturnFrame.Occurrence.segmentStorage right) (some (.active 0 0)))
    (leftAt : left.ctl = { check with frames := .prog first :: check.frames }.control (.pure value))
    (rightAt : ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage right) (.active 0 0) = some (.prog second)) :
    ∃ canon : Cursor (E := core3 grow) (HostState sig),
      ChildFrameOver older left right check canon ∧
      right.ctl = { canon with frames := .prog second :: canon.frames }.control (.pure value) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.markedPopFrame paired outside leftAt rightAt

/-- Follow the original parked slot through an actual string allocator install,
its marked execution, and its designated pop. Depth zero tracks the caller
immediately beneath the allocator during that execution. -/
theorem string_return_tracks (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep) (finish : Nat → Session grow sig (Ret (core3 grow)))
    (start last : State grow sig) (cursor reached : Cursor (E := core3 grow) (HostState sig)) (value : Nat)
    (focused : start.ctl = cursor.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= finish))
    {labels} (marked : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready (host bindings))
      (stringReallocEntry ready bindings cx ptr oldSize alignment size steps finish start cursor)
      (some (.active 0 0)) labels last (some (.active 0 0)))
    (returning : last.ctl = { reached with frames := .prog (stringPlanResume cx steps finish) :: reached.frames }.control
      (.pure (.nat value))) (depth : Nat) :
    ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (host bindings)) start (.active 0 depth)
      (.tau :: labels ++ [.tau])
      { last with ctl := reached.control (stringPlanResume cx steps finish (.nat value)) } (.active 0 depth) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.stringReturnTracks
    cx ptr oldSize alignment size steps finish start last cursor reached value focused marked returning depth

/-- A readiness policy independent of the writer needs no agreement premise
at any reached synchronous read. -/
theorem ReadyAgreement.fixed (policy : Nat → Bool) (start : State grow sig) (inst : InstId) :
    ReadyAgreement (fun _ => policy) start inst := fun _ _ _ _ _ _ _ _ _ _ => rfl

/-- An unaligned reached pointer never enters the traversal. -/
theorem ReachedCollectionTail.unaligned (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat) (reached : State grow sig)
    (invalid : pointer ≠ alignTo pointer area.alignment) :
    ReachedCollectionTail profile ready bindings destination inst entries area output index pointer reached :=
  fun _ _ _ _ aligned => False.elim (invalid aligned)

/-- A failed fresh dry run does not need a rule for an unvisited child. -/
theorem ReachedCollectionTail.refused (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat) (reached : State grow sig) {issue}
    (refused : Record.prepare reached.store reached.host.writer (Field.listObjects entries) = .error issue) :
    ReachedCollectionTail profile ready bindings destination inst entries area output index pointer reached :=
  fun _ _ _ _ _ _ accepted => by rw [refused] at accepted; contradiction

/-- Replay a checked prefix through reached closed give callouts and synchronous
readiness observations. Each callout executes its own refusal and resumes its
actual Core continuation. The paired states retain growth evidence and visible labels. -/
theorem Prefix.replay {left right last : State grow sig} {visibleLabels}
    (path : Prefix profile ready bindings first left visibleLabels last)
    (paired : HostFrame.Paired first second left right) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    ∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels last ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Paired first second last other ∧
      PayloadPrefix.visible leftLabels = visibleLabels ∧ PayloadPrefix.visible rightLabels = visibleLabels :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.replay path paired

/-- Classify the actual two store reads of a live, unresolved synchronous lift
task and its readiness read. The continuation may be a choice or an empty-choice
trap: the rule does not assume the existence of a runnable thread. -/
theorem Prefix.syncLift {start last : State grow sig} {labels task thread frames rest} {entry : Task (core3 grow)}
    (focused : start.ctl = ⟨thread, .prog (syncLiftLoopBody ready task), frames⟩ :: rest)
    (found : ArenaField.tasks.get? start.store task = some entry) (waiting : entry.state ≠ .resolved)
    (agrees : ReadyAgreement ready start entry.inst)
    (path : Prefix profile ready bindings first { start with ctl := ⟨thread,
      .prog (syncLiftCandidates task (start.store.instCandidates (ready start.host) entry.inst)), frames⟩ :: rest }
      labels last) : Prefix profile ready bindings first start labels last :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.syncLift focused found waiting agrees path

/-- Replay a classified finite prefix through its observed pop. The designated
case exposes both reached continuations; an equal but unrelated frame is just
an ordinary pop. Neither branch assumes the continuation will return. -/
theorem Prefix.return_cut {left right last : State grow sig} {seen value}
    (path : Prefix profile ready bindings first left seen last) (paired : HostFrame.Paired first second left right)
    (cursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { cursor with frames := .prog first :: cursor.frames }.control (pure value)) :
    CallbackReturn profile ready bindings first second left right last cursor value seen :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.returnCut path paired cursor leftAt

/-- Replay a classified linked prefix under any set of outstanding saved
continuation pairs. The coverage premise protects just the left-hand
continuations that may diverge; closed gives and readiness reads take
their real, separately ticketed scheduler steps. -/
theorem PrefixFor.replay {left right last : State grow sig} {visibleLabels}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop}
    (path : PrefixFor profile ready bindings protectedReturn left visibleLabels last)
    (covers : ∀ first second, changes first second → protectedReturn first)
    (paired : HostFrame.Related.Paired changes left right) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    ∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels last ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Related.Paired changes last other ∧
      visible leftLabels = visibleLabels ∧ visible rightLabels = visibleLabels :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.replayFor path covers paired

/-- Execute the observed program return on both linked schedulers. The
cut gives the selected continuation pair and residual cursors, not an
assumption that the most recently installed frame returns first. -/
theorem PrefixFor.return_cut {left right last : State grow sig} {seen value}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop}
    {resume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (path : PrefixFor profile ready bindings protectedReturn left seen last)
    (covers : ∀ first second, changes first second → protectedReturn first)
    (paired : HostFrame.Related.Paired changes left right) (cursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { cursor with frames := .prog resume :: cursor.frames }.control (pure value)) :
    CallbackReturnFor profile ready bindings changes left right last cursor resume value seen :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.returnCutFor
    path covers paired cursor leftAt

/-- The reached synchronous lift readiness read is classified independently
of how many saved frames are protected. -/
theorem PrefixFor.syncLift {start last : State grow sig} {labels task thread frames rest} {entry : Task (core3 grow)}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop}
    (focused : start.ctl = ⟨thread, .prog (syncLiftLoopBody ready task), frames⟩ :: rest)
    (found : ArenaField.tasks.get? start.store task = some entry) (waiting : entry.state ≠ .resolved)
    (agrees : ReadyAgreement ready start entry.inst)
    (path : PrefixFor profile ready bindings protectedReturn { start with ctl := ⟨thread,
      .prog (syncLiftCandidates task (start.store.instCandidates (ready start.host) entry.inst)), frames⟩ :: rest }
      labels last) : PrefixFor profile ready bindings protectedReturn start labels last :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.syncLift focused found waiting agrees path

/-- The next canonical string allocation installs paired saved continuations
on a common scheduler frame. `Prefix.replay` then compares a classified
callback, even if it has not returned. -/
theorem string_realloc_pair (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (left right : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (checkAt : left.ctl = cursor.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : right.ctl = cursor.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext)) :
    let dispatch := specDispatch ready (host bindings)
    let leftEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext left cursor
    let rightEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps canonNext right cursor
    Step profile ready dispatch left .tau leftEntry ∧ Step profile ready dispatch right .tau rightEntry ∧
    HostFrame.Paired (stringPlanResume cx steps checkNext) (stringPlanResume cx steps canonNext) leftEntry rightEntry :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.stringReallocPair
    cx ptr oldSize alignment size steps checkNext canonNext left right cursor same checkAt canonAt

/-- The real allocate/resize steps can install another callback even while
older active and blocked frames still differ. The resulting relation is
replayable until an actual host-read or saved-return boundary. -/
theorem ChildFrameOver.string_realloc_pair {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (checkAt : left.ctl = check.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : right.ctl = canon.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext)) :
    let dispatch := specDispatch ready (host bindings)
    let leftEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext left check
    let rightEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps canonNext right canon
    Step profile ready dispatch left .tau leftEntry ∧ Step profile ready dispatch right .tau rightEntry ∧
    HostFrame.Related.Paired (ReturnFrame.Extend changes (stringPlanResume cx steps checkNext)
      (stringPlanResume cx steps canonNext)) leftEntry rightEntry :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.childStringRealloc
    cx ptr oldSize alignment size steps checkNext canonNext frame checkAt canonAt

/-- Take the local phase of any actual string suffix, preserving its reached
frames and growth. If the next action allocates or resizes, both machines
enter the actual allocator with a decreasing suffix. -/
theorem ChildFrameOver.string_plan_cut {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (checkAt : left.ctl = check.control (runStoreSteps cx ptr steps >>= checkNext))
    (canonAt : right.ctl = canon.control (runStoreSteps cx ptr steps >>= canonNext)) :
    StringPlanCut profile ready bindings changes cx steps.length left right check canon checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.stringPlanCut
    cx ptr steps checkNext canonNext frame checkAt canonAt

/-- Compare each successive phase of the actual canonical string plan.
Classified callback prefixes replay even when they stop or trap. The paired
pop of the installed occurrence resumes the strictly shorter suffix with
the older frame relation. This is not a termination promise for realloc. -/
theorem ChildFrameOver.string_replay {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (checkAt : left.ctl = check.control (runStoreSteps cx ptr steps >>= checkNext))
    (canonAt : right.ctl = canon.control (runStoreSteps cx ptr steps >>= canonNext)) :
    StringReplay profile ready bindings changes cx checkNext canonNext steps.length left right check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.stringReplay
    (origin := left.store) cx ptr steps checkNext canonNext frame (Core3.Grows.refl _) checkAt canonAt
    (fun _ _ _ _ _ _ _ _ _ => trivial)

/-- Compare actual checked and canonical string fields, through each reached
allocator return and the final memory descriptor or flat result. An allocator
may leave a finite callback prefix instead; a descriptor trap retains the
writes already made in the reached store. -/
theorem ChildFrameOver.string_field_replay {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (str : Value.StrVal) (valid : str.Valid)
    (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (present : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (fit : StoreStringPre Quirks.none destination.encoding destination.width str)
    (placed : rootPlacement destination left.store (.prim .string) output = .ok ())
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.data (.prim .string) ⟨.string str, .string valid⟩) index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.data (.prim .string) ⟨.string str, .string valid⟩) output >>= canonNext)) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let cx := destination.context inst
    let plan := storePlanFor Quirks.none destination.encoding destination.width str
    let checked := fun ptr => stringPlanTail cx destination.width output plan ptr >>= fun value => checkNext (.ok value)
    let canonical := fun ptr => stringPlanTail cx destination.width output plan ptr >>= canonNext
    let lhs := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checked) }
    let rhs := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonical) }
    ∃ reads, ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch left (List.replicate reads .tau) lhs ∧
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch right [.tau] rhs ∧
      StringReplay profile ready bindings changes cx checked canonical plan.steps.length lhs rhs check canon
        (fun left right check canon _ =>
          StringLocalCut profile ready dispatch left right check canon (fun value => checkNext (.ok value)) canonNext) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.stringFieldReplay
    destination inst str valid index output checkNext canonNext frame present realloc fit placed checkAt canonAt

/-- Compose the actual flat sibling programs by their field cuts. The next
field runs only on common success, using the reached cursor and flat words;
each field rule retains its own refused, suspended and trapping prefixes. -/
theorem ChildFrameOver.flat_sequence_replay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {origin : CStore (core3 grow)} (destination : RecordDestination) (inst : InstId) (items : List Field)
    (index : Nat) (leading : List FlatValue) (compare : FlatFieldComparison grow sig)
    (checkNext : FlatSequenceCheckNext grow sig) (canonNext : FlatSequenceCanonNext grow sig) (finish : FlatResultCut grow sig)
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (rules : ∀ item ∈ items, FlatFieldRule compare older origin destination inst item)
    (ends : ∀ words reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok words)) →
      reference.ctl = canon.control (canonNext words) → finish words reached reference check canon)
    (checkAt : left.ctl = check.control (flatSequenceChecked destination inst items index leading checkNext))
    (canonAt : right.ctl = canon.control (flatSequenceCanonical destination inst items leading canonNext)) :
    FlatSequenceReplay compare older destination inst checkNext canonNext finish items index leading left right check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.flatSequenceReplay
    destination inst items index leading compare checkNext canonNext finish frame growth rules ends checkAt canonAt

/-- Discharge the field rule for strings using the actual repeated allocator
plan, not an assumed equivalence of its callback or continuation. -/
theorem StringField.flat_rule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {origin : CStore (core3 grow)} (item : StringField) (destination : RecordDestination) (inst : InstId)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (fit : StoreStringPre Quirks.none destination.encoding destination.width item.value) :
    FlatFieldRule (stringFlatComparison profile ready bindings older destination inst) older origin destination inst item.field :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.stringFlatRule destination inst item present realloc fit

/-- Reuse the actual live transfer or the linked string-allocation replay at
each reached leaf. The next field receives the reached, possibly spent writer. -/
theorem mixed_flat_rule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (item : Field)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (allocator : Validation.containsPtr item.type = true → ∃ addr, destination.realloc = some addr)
    (fit : CanonicalHandle item ∨ StringField.Fits destination item) :
    FlatFieldRule (mixedFlatComparison profile ready bindings older destination inst) older origin destination inst item :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.mixedFlatRule destination inst item present allocator fit

theorem ChildFrameOver.handle_field_then {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {origin : CStore (core3 grow)} (destination : RecordDestination) (inst : InstId) (item : Field) (handle : CanonicalHandle item)
    (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width item output >>= canonNext))
    {next : output.Result → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Prop}
    (ends : ∀ value reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok value)) →
      reference.ctl = canon.control (canonNext value) → next value reached reference check canon) :
    HandleFieldThen profile ready bindings item index output left right check canon checkNext canonNext next :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.handleFieldThen
    destination inst item handle index output checkNext canonNext frame growth checkAt canonAt ends

theorem ChildFrameOver.string_field_then {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {origin : CStore (core3 grow)} (destination : RecordDestination) (inst : InstId) (item : StringField) (output : Stored.Lower.Output)
    (index : Nat) (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (fit : StoreStringPre Quirks.none destination.encoding destination.width item.value)
    (placed : rootPlacement destination left.store (.prim .string) output = .ok ())
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item.field index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width item.field output >>= canonNext))
    {next : output.Result → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Prop}
    (ends : ∀ value reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok value)) →
      reference.ctl = canon.control (canonNext value) → next value reached reference check canon) :
    StringFieldThen profile ready bindings older destination inst item.value output left right check canon checkNext canonNext next :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.stringFieldThen
    destination inst item output index checkNext canonNext frame growth present realloc fit placed checkAt canonAt ends

theorem flat_nested_refine {shapeAt fitsAt : Field → Prop} (depth : Nat) (field : Field)
    (shape : FlatNestedFits shapeAt depth field)
    (reached : ∀ leaf, Field.Descendant field leaf → shapeAt leaf → fitsAt leaf) : FlatNestedFits fitsAt depth field :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.flatNestedRefine depth field shape reached

/-- Induct through actual record/tuple, fixed-list and selected sum programs. The
branch returns its concatenated words to the enclosing continuation only
after all its visited children succeed. -/
theorem nested_flat_rule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (leaf : Field → Prop) (compare : FlatFieldComparison grow sig)
    (rules : ∀ field, leaf field → FlatFieldRule compare older origin destination inst field)
    (depth : Nat) (field : Field) (fits : FlatNestedFits leaf depth field) (tags : FlatTagBounds field) :
    FlatFieldRule (nestedFlatComparison profile ready bindings compare older destination inst depth) older origin destination inst field :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.nestedFlatRule
    destination inst leaf compare rules depth field fits tags

/-- Concrete allocating instance of the recursive flat rule. String leaves
may each allocate or resize repeatedly; neither a return from any allocator
nor a child equivalence hypothesis is required. -/
theorem nested_flat_strings {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (depth : Nat) (field : Field)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (fits : FlatNestedFits (StringField.Fits destination) depth field) (tags : FlatTagBounds field) :
    FlatFieldRule (nestedFlatComparison profile ready bindings (stringFlatComparison profile ready bindings older destination inst)
      older destination inst depth) older origin destination inst field :=
  nested_flat_rule destination inst _ _ (fun _ ⟨item, equal, fit⟩ =>
    equal ▸ item.flat_rule destination inst present realloc fit) depth field fits tags

/-- A reached allocating list or map can likewise install on distinct
residual frames, keeping the memory-map placement mode and its live recheck
in the real saved continuations. -/
theorem ChildFrameOver.collection_install_pair {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (reachedWidth : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let dispatch := specDispatch ready (host bindings)
    let area := layout destination.width element
    let first := checkedCollectionResume destination inst entries area index output checkNext
    let second := canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    let checkCall := collectionEntry destination inst area entries.length dispatch left check first
    let canonCall := collectionEntry destination inst area entries.length dispatch right canon second
    Steps profile ready dispatch left [.tau, .tau, .tau] checkCall ∧
    Steps profile ready dispatch right [.tau, .tau] canonCall ∧
    HostFrame.Related.Paired (ReturnFrame.Extend changes first second) checkCall canonCall := by
  obtain ⟨checked, canonical, paired⟩ :=
    Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.childCollectionInstall
    (profile := profile) (ready := ready) (bindings := bindings)
    destination inst type element entries output index checkNext canonNext frame reachedWidth prepared checkAt canonAt
  exact ⟨(ReturnFrame.Occurrence.prefix_survives (checked 0)).1, (ReturnFrame.Occurrence.prefix_survives (canonical 0)).1, paired⟩

/-- Replay a finite classified allocation prefix on both actual collection
programs. Only a return from the installed occurrence can continue into the
reached range and live authority checks. The entry mode stays attached to
the saved continuation, including indirect memory-map placement. -/
theorem ChildFrameOver.collection_replay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon)
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    CollectionReplay profile ready bindings older destination inst type element entries index output left right check canon checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.collectionReplay
    destination inst type element entries index output checkNext canonNext frame present sized prepared checkAt canonAt

/-- Validate the reached allocation before re-reading live authority. Any
substitution selected for this pop must implement the same range program
on the observed pointer; other saved frames remain related. -/
theorem PrefixFor.range_cut (destination : RecordDestination) (inst : InstId) (area : Layout) (count pointer : Nat)
    (plan : List Object) {left right last : State grow sig} {seen}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop}
    (path : PrefixFor profile ready bindings protectedReturn left seen last)
    (covers : ∀ first second, changes first second → protectedReturn first)
    (paired : HostFrame.Related.Paired changes left right) (cursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { cursor with frames := .prog first :: cursor.frames }.control (pure (.nat pointer)))
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Nat → Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (checkBody : first (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area count pointer
      let live ← Record.Effects.reserve recordClaims plan
      checkNext ptr live))
    (canonBody : ∀ resume, changes first resume →
      resume (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= canonNext)) :
    RangeCutOver profile ready bindings changes first left right last cursor destination area count pointer plan checkNext canonNext seen :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.rangeCutOver
    destination inst area count pointer plan path covers paired cursor leftAt present sized checkNext canonNext checkBody canonBody

/-- Replay to the actual child-entry cut, with the reached memory region,
live verdict and residual scheduler frames. A range trap or common pop
does not enter the child program. No child comparison or return guarantee
is a premise of this cut. -/
theorem Prefix.range_cut (destination : RecordDestination) (inst : InstId) (area : Layout) (count pointer : Nat)
    (plan : List Object) {left right last : State grow sig} {seen}
    (path : Prefix profile ready bindings first left seen last)
    (paired : HostFrame.Paired first second left right) (cursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { cursor with frames := .prog first :: cursor.frames }.control (pure (.nat pointer)))
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Nat → Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (checkBody : first (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area count pointer
      let live ← Record.Effects.reserve recordClaims plan
      checkNext ptr live))
    (canonBody : second (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= canonNext)) :
    RangeCut profile ready bindings first second left right last cursor destination area count pointer plan checkNext canonNext seen :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.rangeCut
    destination inst area count pointer plan path paired cursor leftAt present sized checkNext canonNext checkBody canonBody

/-- Derive entry and return cuts from the two actual dynamic-field programs.
The canonical continuation keeps the memory-map entry mode chosen at
allocation time; an allocating child can be visited next without supplying
a comparison of the entire collection suffix. -/
theorem collection_descend (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (output : Lower.Output) (index : Nat) (left right : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (present : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? right.store.core destination.memory = some bytes)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    CollectionDescent profile ready bindings destination inst type element entries output index left right cursor checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.collectionDescent
    destination inst type element entries output index left right cursor checkNext canonNext same present sized prepared checkAt canonAt

/-- Compose the classified callback from the reached allocator entry with
the natural return at its far end. Use that reached store for range checks
and that reached writer for live claim revalidation before the child rules.
A coincidentally equal unswapped frame can also just take an ordinary pop;
in that case the machines remain paired without claiming a collection return. -/
theorem Prefix.collection_return (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat)
    {left right last : State grow sig} {labels} (path : Prefix profile ready bindings first left labels last)
    (paired : HostFrame.Paired first second left right) (checkCursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { checkCursor with frames := .prog first :: checkCursor.frames }.control (pure (.nat pointer)))
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (checkBody : first (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : second (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    (compared : ReachedCollectionTail profile ready bindings destination inst entries area output index pointer last) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    (∃ canonCursor, canonCursor.thread = checkCursor.thread ∧
      Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext) ∨
    (∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels { last with ctl := checkCursor.control (first (.nat pointer)) } ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Paired first second { last with ctl := checkCursor.control (first (.nat pointer)) } other ∧
      visible leftLabels = labels ∧ visible rightLabels = labels) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.collectionReturn destination inst
    entries area output index pointer path paired checkCursor leftAt present sized checkNext canonNext
    checkBody canonBody compared

/-- Start at the two actual dynamic lowering programs. The allocator entry
and both saved continuations are derived from those programs, not supplied
as matching-callback hypotheses. The remaining path evidence classifies
only the reached checked run. Value-mode entries share the child comparisons. -/
theorem Prefix.collection (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (output : Lower.Output) (index pointer : Nat) {initial left right last : State grow sig} {before seen}
    (cursor reached : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (prefixRun : CoreGrowthSteps profile ready (specDispatch ready (host (grow := grow) bindings)) initial before right)
    (checkedDestination : destination.check initial.store = .ok ()) {bytes : Nat}
    (sized : (core3 grow).memSize? initial.store.core destination.memory = some bytes)
    (mode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
    let call := collectionEntry destination inst area entries.length dispatch left cursor checkResume
    Prefix profile ready bindings checkResume call seen last →
    last.ctl = { reached with frames := .prog checkResume :: reached.frames }.control (pure (.nat pointer)) →
    ReachedCollectionTail profile ready bindings destination inst entries area output index pointer last →
    CollectionCut profile ready bindings checkResume canonResume left right
      { last with ctl := reached.control (checkResume (.nat pointer)) } reached checkNext canonNext seen :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.collection destination inst type element entries
    output index pointer cursor reached checkNext canonNext same prefixRun checkedDestination sized mode prepared checkAt canonAt

/-- Compare an admitted dynamic value-mode child from its actual emitted
programs, through a classified allocator path and the reached live recheck.
Success carries Core growth from the enclosing prefix through the entries
and descriptor. A common-frame pop remains a suspended comparison. -/
theorem Prefix.collection_memory (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (output : Lower.Output) (index pointer : Nat) {origin : CStore (core3 grow)} {left right last : State grow sig} {seen}
    (cursor reached : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (growth : Core3.Grows origin.core right.store.core)
    (memoryWidth : (core3 grow).memAddrType? origin.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (mode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
    let call := collectionEntry destination inst area entries.length dispatch left cursor checkResume
    Prefix profile ready bindings checkResume call seen last →
    last.ctl = { reached with frames := .prog checkResume :: reached.frames }.control (pure (.nat pointer)) →
    (∀ item ∈ entries, MemoryChildRule profile ready dispatch destination inst item element) →
    CollectionCutKeeping profile ready bindings (fun store => Core3.Grows origin.core store.core)
      checkResume canonResume left right { last with ctl := reached.control (checkResume (.nat pointer)) }
      reached checkNext canonNext seen :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.collectionMemory destination inst type element entries
    output index pointer cursor reached checkNext canonNext same growth memoryWidth sized mode prepared checkAt canonAt

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
