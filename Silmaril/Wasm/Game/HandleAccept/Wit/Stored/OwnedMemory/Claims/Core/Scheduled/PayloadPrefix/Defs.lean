module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Local.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.CanonicalTree.Defs
public import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Value
open Stored.Endpoints.RecordLower (Field)
open Stored.Endpoints

inductive Outcome (Result : Type) where
  | returned (value : Result)
  | refused (issue : Stored.Endpoints.RecordLower.Issue)
  | trapped (reason : TrapReason)

structure Cursor {E : CoreEngine} (Host : Type) where
  thread : Option ThreadId
  frames : List (Seg E Host)
  rest : List (Activation E Host)

def Cursor.control {E : CoreEngine} {Host : Type} (cursor : Cursor (E := E) Host)
    (body : P E Host (Ret E)) : List (Activation E Host) :=
  ⟨cursor.thread, .prog body, cursor.frames⟩ :: cursor.rest

def visible {E : CoreEngine} {Host : Type} (labels : List (Label E Host)) : List (Label E Host) :=
  labels.filter fun label => match label with | .tau => false | _ => true

/-- Two finite prefixes compared with independently saved continuations.
Success enters both continuations. A typed refusal leaves the reference at
an actual prefix with no fictitious result. A trap records the common final
trap label and the stores after lockdown. -/
def Reaches {E : CoreEngine} {Host Result : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (left right : Config E Host) (checkCursor canonCursor : Cursor (E := E) Host)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → P E Host (Ret E))
    (canonNext : Result → P E Host (Ret E)) : Prop :=
  ∃ outcome : Outcome Result, ∃ checkLabels canonLabels checkEnd canonEnd,
    Steps profile ready dispatch left checkLabels checkEnd ∧
    Steps profile ready dispatch right canonLabels canonEnd ∧
    checkEnd.store = canonEnd.store ∧ visible checkLabels = visible canonLabels ∧
    match outcome with
    | .returned value => checkEnd.ctl = checkCursor.control (checkNext (.ok value)) ∧
        canonEnd.ctl = canonCursor.control (canonNext value)
    | .refused issue => checkEnd.ctl = checkCursor.control (checkNext (.error issue))
    | .trapped reason => checkEnd.ctl = [] ∧ canonEnd.ctl = [] ∧
        ∃ leading, visible canonLabels = leading ++ [.trap reason]

/-- A paired segment that also supplies the reached invariant needed by a
subsequent child. Refusals and traps do not enter that child. -/
def ReachesKeeping {E : CoreEngine} {Host Result : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (keep : CStore E → Prop) (left right : Config E Host)
    (checkCursor canonCursor : Cursor (E := E) Host)
    (checkNext : Except RecordLower.Issue Result → P E Host (Ret E)) (canonNext : Result → P E Host (Ret E)) : Prop :=
  ∃ outcome : Outcome Result, ∃ checkLabels canonLabels checkEnd canonEnd,
    Steps profile ready dispatch left checkLabels checkEnd ∧
    Steps profile ready dispatch right canonLabels canonEnd ∧
    checkEnd.store = canonEnd.store ∧ visible checkLabels = visible canonLabels ∧
    (match outcome with | .returned _ => keep canonEnd.store | _ => True) ∧
    match outcome with
    | .returned value => checkEnd.ctl = checkCursor.control (checkNext (.ok value)) ∧
        canonEnd.ctl = canonCursor.control (canonNext value)
    | .refused issue => checkEnd.ctl = checkCursor.control (checkNext (.error issue))
    | .trapped reason => checkEnd.ctl = [] ∧ canonEnd.ctl = [] ∧
        ∃ leading, visible canonLabels = leading ++ [.trap reason]

def CompareKeepingAt {E : CoreEngine} {Host Result : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (keep : CStore E → Prop) (left right : Config E Host)
    (checked : P E Host (Except RecordLower.Issue Result)) (canonical : P E Host Result) : Prop :=
  left.store = right.store →
    ∀ (checkCursor canonCursor : Cursor (E := E) Host), checkCursor.thread = canonCursor.thread →
      ∀ (checkNext : Except RecordLower.Issue Result → P E Host (Ret E)) (canonNext : Result → P E Host (Ret E)),
        left.ctl = checkCursor.control (checked >>= checkNext) →
        right.ctl = canonCursor.control (canonical >>= canonNext) →
        ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor checkNext canonNext

/-- Bind a checked child to its actual suffix, without executing the suffix
on refusal. The enclosing program may add its own issue index. -/
def checkedSequenceNext {E : CoreEngine} {Host Result Next : Type}
    (mapIssue : RecordLower.Issue → RecordLower.Issue) (tail : Result → P E Host (Except RecordLower.Issue Next))
    (finish : Except RecordLower.Issue Next → P E Host (Ret E)) :
    Except RecordLower.Issue Result → P E Host (Ret E) :=
  fun result => (match result with | .error issue => pure (.error (mapIssue issue)) | .ok value => tail value) >>= finish

/-- Compare the programs at a given common reached store and two saved cursors. -/
def CompareAt {E : CoreEngine} {Host Result : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (left right : Config E Host)
    (checked : P E Host (Except Stored.Endpoints.RecordLower.Issue Result)) (canonical : P E Host Result) : Prop :=
  left.store = right.store →
    ∀ (checkCursor canonCursor : Cursor (E := E) Host), checkCursor.thread = canonCursor.thread →
      ∀ (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → P E Host (Ret E)) (canonNext : Result → P E Host (Ret E)),
        left.ctl = checkCursor.control (checked >>= checkNext) →
        right.ctl = canonCursor.control (canonical >>= canonNext) →
        Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext

/-- Compare a closed segment at any common reached store. This finite rule
does not cover callbacks that can suspend or never return. -/
def Compare {E : CoreEngine} {Host Result : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (checked : P E Host (Except Stored.Endpoints.RecordLower.Issue Result))
    (canonical : P E Host Result) : Prop :=
  ∀ left right, CompareAt profile ready dispatch left right checked canonical

section

variable (tagFits : Nat → Nat → Prop)

mutual
/-- The closed flat fragment whose leaves need no allocator or host query
after the checked transfer guard. A sum's tag rule is independent of which
leaves are in the fragment; coercing slots can still emit canonical choices. -/
def HandleFieldWhere : Field → Prop
  | .aggregate _ fields | .fixed _ _ fields => HandleFieldsWhere fields
  | .sum _ arms tag selected => tagFits tag arms.length ∧ HandleArmWhere selected
  | field => CanonicalHandle field
termination_by structural field => field

def HandleFieldsWhere : List Field → Prop
  | [] => True
  | field :: rest => HandleFieldWhere field ∧ HandleFieldsWhere rest
termination_by structural fields => fields

def HandleArmWhere : Option Field → Prop
  | none => True
  | some field => HandleFieldWhere field
termination_by structural selected => selected
end

end

abbrev HandleShape := HandleFieldWhere (fun _ _ => True)

abbrev HandleField := HandleFieldWhere Nat.lt

def MemoryHandleRoot : Field → Prop
  | .sum _ _ _ none => True
  | .sum _ _ _ (some item) => CanonicalHandle item
  | item => CanonicalHandle item

def ClosedMemoryLeaf (item : Field) : Prop :=
  CanonicalHandle item ∨ ∃ primitive, primitive ≠ WIT.Primitive.string ∧
    ∃ payload : Stored.Payload (.prim primitive), item = .data (.prim primitive) payload

/-- Records and tuples to arbitrary depth, with local scalar or handle leaves. -/
inductive LocalMemory : Field → Prop where
  | leaf {item : Field} : ClosedMemoryLeaf item → LocalMemory item
  | aggregate {type : TypeOf} {fields : List Field} :
      (∀ item ∈ fields, LocalMemory item) → LocalMemory (.aggregate type fields)

/-- The existing handle fragment plus records and tuples of local leaves. -/
def ClosedMemoryRoot (item : Field) : Prop :=
  MemoryHandleRoot item ∨ ∃ type fields, item = .aggregate type fields ∧ ∀ child ∈ fields, ClosedMemoryLeaf child

def flatReply {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (destination : RecordDestination) (schema : TypeOf) (ticket : Nat)
    (verdict : Except Stored.Endpoints.RecordLower.Issue (List FlatValue)) : Session grow sig (Ret (core3 grow)) := do
  return .flat (← writeCompletion ((GiveEffectRoute.flat schema).reply destination ticket verdict))

def memoryReply {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (destination : RecordDestination) (pointer : FlatValue) (ticket : Nat)
    (verdict : Except Stored.Endpoints.RecordLower.Issue Unit) : Session grow sig (Ret (core3 grow)) := do
  return .flat (← writeCompletion ((GiveEffectRoute.memory pointer).reply destination ticket verdict))

/-- `Canon.store` treats root placement as a precondition; the public route
checks it explicitly. An invalid placement has no matching canonical step. -/
def placement {grow : SingleThreaded.GrowOracle} (destination : RecordDestination) (store : CStore (core3 grow))
    (area : Layout) (ptr : Nat) : Except TrapReason Unit := do
  if ptr % area.alignment.bytes != 0 then throw .unalignedPointer
  let some size := (core3 grow).memSize? store.core destination.memory
    | throw (.internal "dangling memory address")
  if ptr + area.size > size then throw .outOfBounds

inductive LocalDataType : TypeOf → Prop where
  | primitive {primitive : WIT.Primitive} : primitive ≠ .string → LocalDataType (.prim primitive)
  | enum {cases : List String} : Lower.checkSchema (.enum cases) = .ok () → LocalDataType (.enum cases)
  | flags {labels : List String} : Lower.checkSchema (.flags labels) = .ok () → LocalDataType (.flags labels)

def rootPlacement {grow : SingleThreaded.GrowOracle} (destination : RecordDestination)
    (store : CStore (core3 grow)) (type : TypeOf) : Lower.Output → Except TrapReason Unit
  | .flat => .ok ()
  | .memory ptr => placement destination store (layout destination.width type) ptr

/-- The canonical result program after the allocating string plan. Memory
output reads the pointer size again, before the two descriptor writes. -/
def stringPlanTail {E : CoreEngine} {Host : Type} (cx : LiftLowerContext E) (width : AddrType)
    (output : Lower.Output) (plan : StorePlan) (ptr : Nat) : P E Host output.Result :=
  match output with
  | .flat => pure [ptrFlat width ptr, ptrFlat width plan.taggedCodeUnits]
  | .memory address => do
    let size ← ptrSize cx
    writeMem cx address (strWordBytes size ptr)
    writeMem cx (address + size) (strWordBytes size plan.taggedCodeUnits)

/-- Resume the actual remaining string plan at the allocator's returned pointer. -/
def stringPlanResume {E : CoreEngine} {Host : Type} (cx : LiftLowerContext E)
    (steps : List StoreStep) (finish : Nat → P E Host (Ret E)) : ReturnFrame.Continuation E Host := fun result => do
  let ptr ← match result with
    | .nat ptr => pure ptr
    | _ => internal "late-bound call: expected Ret.nat"
  runStoreSteps cx ptr steps >>= finish

/-- Nonallocating string operations run directly against the reached store. -/
def LocalStringStep : StoreStep → Prop
  | .allocate .. | .reallocate .. => False
  | _ => True

/-- The first allocator request after the current string cursor, or the
completed plan pointer. The request retains the exact unexecuted plan. -/
inductive StringFront (length : Nat) where
  | done (ptr : Nat)
  | call (ptr : Nat) (oldSize : Option Nat) (alignment : Alignment) (size : Nat) (rest : List StoreStep)
      (shorter : rest.length < length)

def StringFront.weaken {length : Nat} : StringFront length → StringFront (length + 1)
  | .done ptr => .done ptr
  | .call ptr oldSize alignment size rest shorter => .call ptr oldSize alignment size rest (Nat.lt_succ_of_lt shorter)

def StringFront.remaining {E : CoreEngine} {Host : Type} {length : Nat} (cx : LiftLowerContext E) : StringFront length → P E Host Nat
  | .done ptr => pure ptr
  | .call ptr oldSize alignment size rest _ => runStoreSteps cx ptr
      (oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size) :: rest)

/-- Execute the canonical store steps up to, but not including, the next
allocator call. This reads and writes the reached memory, not saved bytes. -/
def stringFront {E : CoreEngine} {Host : Type} (cx : LiftLowerContext E) (ptr : Nat) :
    (steps : List StoreStep) → P E Host (StringFront steps.length)
  | [] => pure (.done ptr)
  | .allocate alignment size :: rest => pure (.call ptr none alignment size rest (Nat.lt_succ_self _))
  | .reallocate old alignment size :: rest => pure (.call ptr (some old) alignment size rest (Nat.lt_succ_self _))
  | action :: rest => runStoreStep cx ptr action >>= fun next =>
      stringFront cx next rest >>= fun front => pure front.weaken

/-- Both sides execute the same local effects up to a returned cursor or
trap. On return the original active and blocked frame tails are intact; a
trap locks down the reached store without undoing its writes. -/
def StringLocalCut {grow : SingleThreaded.GrowOracle} {Host Result : Type} (profile : ProfileKind)
    (ready : HostReady Host) (dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow)))
    (left right : Config (core3 grow) Host) (check canon : Cursor (E := core3 grow) Host)
    (checkNext canonNext : Result → P (core3 grow) Host (Ret (core3 grow))) : Prop :=
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason Result) (labels : List (Label (core3 grow) Host)),
    LocalLeafLabels result labels ∧
    CoreGrowthSteps profile ready dispatch left labels
      (localLeafEnd left left.host store check.thread check.frames check.rest checkNext result) ∧
    CoreGrowthSteps profile ready dispatch right labels
      (localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result) ∧
    ∀ value, result = .ok value → ∀ depth,
      ReturnFrame.Occurrence.Prefix profile ready dispatch left (.active 0 depth) labels
        (localLeafEnd left left.host store check.thread check.frames check.rest checkNext result) (.active 0 depth) ∧
      ReturnFrame.Occurrence.Prefix profile ready dispatch right (.active 0 depth) labels
        (localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result) (.active 0 depth)

def MemoryReaches {E : CoreEngine} {Host : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (left right : Config E Host)
    (checkCursor canonCursor : Cursor (E := E) Host) (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → P E Host (Ret E))
    (canonNext : Unit → P E Host (Ret E)) (placementVerdict : Except TrapReason Unit) : Prop :=
  Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext ∨
    ∃ reason count reached, placementVerdict = .error reason ∧
      Steps profile ready dispatch left (List.replicate count .tau ++ [.trap reason]) reached ∧
      reached.ctl = [] ∧ reached.store = StepDefs.lockdownSt left.store

/-- A local comparison with exact reached configurations. Unlike the
handle-only cut, it permits synchronized observations such as NaN choices. -/
def LocalCutKeeping {E : CoreEngine} {Host Result : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (keep : CStore E → Prop) (left right : Config E Host)
    (check canon : Cursor (E := E) Host) (checkNext canonNext : Result → P E Host (Ret E)) : Prop :=
  ∃ (store : CStore E) (result : Except TrapReason Result) (checked canonical : List (Label E Host)),
    Steps profile ready dispatch left checked
      (localLeafEnd left left.host store check.thread check.frames check.rest checkNext result) ∧
    Steps profile ready dispatch right canonical
      (localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result) ∧
    visible checked = visible canonical ∧
    match result with
    | .ok _ => keep store ∧
        ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch left checked
          (localLeafEnd left left.host store check.thread check.frames check.rest checkNext result) ∧
        ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch right canonical
          (localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result)
    | .error reason => ∃ leading, visible canonical = leading ++ [.trap reason]

def CompareLocalKeepingAt {E : CoreEngine} {Host Result : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (keep : CStore E → Prop) (left right : Config E Host)
    (checked : P E Host (Except RecordLower.Issue Result)) (canonical : P E Host Result) : Prop :=
  left.store = right.store →
    ∀ (check canon : Cursor (E := E) Host), check.thread = canon.thread →
      ∀ (checkNext : Except RecordLower.Issue Result → P E Host (Ret E)) (canonNext : Result → P E Host (Ret E)),
        left.ctl = check.control (checked >>= checkNext) → right.ctl = canon.control (canonical >>= canonNext) →
        LocalCutKeeping profile ready dispatch keep left right check canon (fun value => checkNext (.ok value)) canonNext

def sumPayloadAddress (width : AddrType) (arms : List (Option TypeOf)) (base : Nat) : Nat :=
  alignTo (base + discSize arms.length) (maxCaseAlignment (arms.map (layoutOption width)))

def sumCheckedNext {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (destination : RecordDestination) (inst : InstId) (selected : Option Field) (index address : Nat)
    (finish : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))) : Unit → Session grow sig (Ret (core3 grow)) :=
  fun () => match selected with
  | none => finish (.ok ())
  | some child => Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width child 0 (.memory address) >>= fun verdict => finish (verdict.mapError (.nested index))

def sumCanonicalNext {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (destination : RecordDestination) (inst : InstId) (selected : Option Field) (address : Nat)
    (finish : Unit → Session grow sig (Ret (core3 grow))) : Unit → Session grow sig (Ret (core3 grow)) :=
  fun () => match selected with
  | none => finish ()
  | some child => RecordLower.CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width child (.memory address) >>= finish

def checkedCollectionTail {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (destination : RecordDestination) (inst : InstId) (entries : List Field) (area : Layout)
    (index : Nat) (output : Lower.Output) (ptr : Nat) :
    Except RecordLower.Issue Unit → Session grow sig (Except RecordLower.Issue output.Result)
  | .error (.preflight issue) => pure (.error (.field index (.afterAllocation issue)))
  | .error issue => pure (.error (.nested index issue))
  | .ok () => do
    let cx := destination.context inst
    match ← Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width entries area.size ptr 0 with
    | .error issue => return .error (.nested index issue)
    | .ok () => return .ok (← ListLower.publish cx destination.width ptr entries.length output)

def canonicalCollectionTail {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (destination : RecordDestination) (inst : InstId) (entries : List Field) (area : Layout)
    (output : Lower.Output) (ptr : Nat) (mode : RecordLower.CanonicalTree.EntryMode := .value) : Session grow sig output.Result := do
  let cx := destination.context inst
  RecordLower.CanonicalTree.elements Limits.spec Quirks.none cx destination.width entries mode area.size ptr
  ListLower.publish cx destination.width ptr entries.length output

def CollectionTailUsing {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (destination : RecordDestination) (inst : InstId) (entries : List Field) (area : Layout)
    (output : Lower.Output) (index ptr bytes : Nat) (left right : Config (core3 grow) (HostState sig))
    (compare : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      Session grow sig (Except RecordLower.Issue output.Result) → Session grow sig output.Result → Prop) : Prop :=
  ptr = alignTo ptr area.alignment → ptr + entries.length * area.size ≤ bytes →
  Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok () →
  ∀ checked canonical : Config (core3 grow) (HostState sig),
    checked.store = left.store → canonical.store = right.store →
    checked.host = left.host → canonical.host = right.host →
    compare checked canonical
      (checkedCollectionTail destination inst entries area index output ptr (.ok ()))
      (canonicalCollectionTail destination inst entries area output ptr)

/-- The child traversal is required only at an admitted natural return.
It receives the reached region and live verdict, and need not compare values
at invalid addresses or predict a callback's mutations. -/
def CollectionTailAt {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (destination : RecordDestination) (inst : InstId) (entries : List Field) (area : Layout)
    (output : Lower.Output) (index ptr bytes : Nat) (left right : Config (core3 grow) (HostState sig)) : Prop :=
  CollectionTailUsing destination inst entries area output index ptr bytes left right (CompareAt profile ready dispatch)

/-- An admitted tail that also carries an invariant into the continuation
on a common return. A refusal or trap does not require that invariant. -/
def CollectionTailKeepingAt {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))) (keep : CStore (core3 grow) → Prop)
    (destination : RecordDestination) (inst : InstId) (entries : List Field) (area : Layout)
    (output : Lower.Output) (index ptr bytes : Nat) (left right : Config (core3 grow) (HostState sig)) : Prop :=
  CollectionTailUsing destination inst entries area output index ptr bytes left right (CompareKeepingAt profile ready dispatch keep)

/-- A child comparison at a placed memory cursor. Placement uses the original
validated region; growth carries those bounds to the reached store, without
requiring that callbacks preserve the bytes in that region. -/
def MemoryChildRule {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (destination : RecordDestination) (inst : InstId) (item : Field) (type : TypeOf) : Prop :=
  ∀ (origin : CStore (core3 grow)) (index address bytes : Nat),
    (core3 grow).memAddrType? origin.core destination.memory = some destination.width →
    (core3 grow).memSize? origin.core destination.memory = some bytes →
    address % (layout destination.width type).alignment.bytes = 0 →
    address + (layout destination.width type).size ≤ bytes →
    ∀ left right : Config (core3 grow) (HostState sig), Core3.Grows origin.core right.store.core →
      CompareKeepingAt profile ready dispatch (fun store => Core3.Grows origin.core store.core) left right
        (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
          item index (.memory address))
        (RecordLower.CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))

/-- The compiler's two-field map entry shape and the recursive rules for its
actual key and value programs. Either program may itself allocate. -/
def MapEntryRules {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf) (entry : Field) : Prop :=
  ∃ keyField valueField,
    entry = .aggregate (.record (mapEntryFields key element)) [keyField, valueField] ∧
    keyField.LayoutMatches (.prim key.toPrimitive) ∧ valueField.LayoutMatches element ∧
    MemoryChildRule profile ready dispatch destination inst keyField (.prim key.toPrimitive) ∧
    MemoryChildRule profile ready dispatch destination inst valueField element

def checkedCollectionResume {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (destination : RecordDestination) (inst : InstId) (entries : List Field) (area : Layout)
    (index : Nat) (output : Lower.Output)
    (finish : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow))) :
    ReturnFrame.Continuation (core3 grow) (HostState sig) :=
  listRangeResume (destination.context inst) area entries.length fun ptr => do
    let live ← OwnedMemory.Claims.Record.Effects.reserve recordClaims (Field.listObjects entries)
    checkedCollectionTail destination inst entries area index output ptr live >>= finish

def canonicalCollectionResume {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (destination : RecordDestination) (inst : InstId) (entries : List Field) (area : Layout)
    (output : Lower.Output) (finish : output.Result → Session grow sig (Ret (core3 grow)))
    (mode : RecordLower.CanonicalTree.EntryMode := .value) :
    ReturnFrame.Continuation (core3 grow) (HostState sig) :=
  listRangeResume (destination.context inst) area entries.length fun ptr =>
    canonicalCollectionTail destination inst entries area output ptr mode >>= finish

def collectionEntry {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (destination : RecordDestination) (inst : InstId) (area : Layout) (count : Nat)
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))) (start : Config (core3 grow) (HostState sig))
    (cursor : Cursor (E := core3 grow) (HostState sig)) (resume : ReturnFrame.Continuation (core3 grow) (HostState sig)) :
    Config (core3 grow) (HostState sig) :=
  let request := Call.reallocate (destination.context inst) 0 0 area.alignment.bytes (count * area.size)
  { start with ctl := { cursor with frames := .prog resume :: cursor.frames }.control (dispatch request) }

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
