module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.CollectionVisit.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Stored.Endpoints Stored.Endpoints.RecordLower PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

/-- Records and tuples align from the current cursor. Arrays advance at the
validated element stride. Indirect map pairs instead place their fields at
the width captured by allocation, with no fresh canonical width read. -/
inductive Track where
  | fields
  | placedFields
  | elements (stride : Nat)

def Track.slot (mode : Track) (width : AddrType) (item : Field) (cursor : Nat) : Nat × Nat :=
  match mode with
  | .fields | .placedFields =>
    let area := layout width item.type
    let start := alignTo cursor area.alignment
    (start, start + area.size)
  | .elements stride => (cursor, cursor + stride)

def Track.checked (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field)
    (index cursor : Nat) : Session grow sig (Except RecordLower.Issue Unit) :=
  match mode with
  | .fields | .placedFields => Record.Effects.memory recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
      items cursor index
  | .elements stride => Record.Effects.elements recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
      items stride cursor index

def canonicalPlacedFields (destination : RecordDestination) (inst : InstId) : List Field → Nat → Session grow sig Unit
  | [], _ => pure ()
  | item :: rest, cursor =>
    let (address, next) := Track.placedFields.slot destination.width item cursor
    CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address) >>=
      fun () => canonicalPlacedFields destination inst rest next

def Track.canonical (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field)
    (cursor : Nat) : Session grow sig Unit :=
  match mode with
  | .fields => CanonicalTree.memory Limits.spec Quirks.none (destination.context inst) destination.width items cursor
  | .placedFields => canonicalPlacedFields destination inst items cursor
  | .elements stride => CanonicalTree.elements Limits.spec Quirks.none (destination.context inst) destination.width items .value stride cursor

def Track.readLabels : Track → List (Label (core3 grow) (HostState sig))
  | .fields => [.tau]
  | .placedFields | .elements _ => []

abbrev CheckNext (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))

abbrev CanonNext (grow : SingleThreaded.GrowOracle) (sig : Signature) := Unit → Session grow sig (Ret (core3 grow))

abbrev Finish (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) → Cursor (E := core3 grow) (HostState sig) → Prop

abbrev FieldComparison (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Field → Nat → Nat → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
    Cursor (E := core3 grow) (HostState sig) → CheckNext grow sig → CanonNext grow sig → Finish grow sig → Prop

def FieldRule (compare : FieldComparison grow sig) (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin : CStore (core3 grow)) (destination : RecordDestination) (inst : InstId) (item : Field) (address : Nat) : Prop :=
  ∀ index (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) left right check canon,
    ChildFrameOver older left right check canon → Core3.Grows origin.core left.store.core →
    left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width item index (.memory address) >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width item (.memory address) >>= canonNext) →
    ∀ finish : Finish grow sig, (∀ reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok ())) →
      reference.ctl = canon.control (canonNext ()) → finish reached reference check canon) →
    compare item index address left right check canon checkNext canonNext finish

def Track.Slots (mode : Track) (width : AddrType) (rule : Field → Nat → Prop) : List Field → Nat → Prop
  | [], _ => True
  | item :: rest, cursor =>
    let (address, next) := mode.slot width item cursor
    rule item address ∧ mode.Slots width rule rest next

/-- A placed child interval, independent of the contents of guest memory. -/
def SlotFits (width : AddrType) (bytes : Nat) (item : Field) (address : Nat) : Prop :=
  address % (layout width item.type).alignment.bytes = 0 ∧ address + (layout width item.type).size ≤ bytes

/-- The checked aggregate guard wraps a child's typed error at the
enclosing field index, and does not turn a canonical trap into a result. -/
def aggregateNext (index : Nat) (next : CheckNext grow sig) : CheckNext grow sig :=
  fun result => next (result.mapError (.nested index))

def enterAggregate (destination : RecordDestination) (inst : InstId) (items : List Field) (index address : Nat)
    (left : State grow sig) (check : Cursor (E := core3 grow) (HostState sig)) (next : CheckNext grow sig) : State grow sig :=
  { left with ctl := check.control (Track.fields.checked destination inst items 0 address >>= aggregateNext index next) }

def checkTail (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field) (index cursor : Nat)
    (finish : CheckNext grow sig) : CheckNext grow sig
  | .error issue => finish (.error issue)
  | .ok () => mode.checked destination inst items index cursor >>= finish

def canonTail (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field) (cursor : Nat)
    (finish : CanonNext grow sig) : CanonNext grow sig := fun () => mode.canonical destination inst items cursor >>= finish

def focus (mode : Track) (destination : RecordDestination) (inst : InstId) (item : Field) (cursor : Nat)
    (right : State grow sig) (canon : Cursor (E := core3 grow) (HostState sig)) (finish : CanonNext grow sig) : State grow sig :=
  { right with ctl := canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
    item (.memory (mode.slot destination.width item cursor).1) >>= finish) }

/-- Follow the actual memory programs in field order. With each sibling, the
canonical cursor read precedes the child; only common success starts the rest. -/
def Replay (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (mode : Track) (destination : RecordDestination) (inst : InstId) (compare : FieldComparison grow sig)
    (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig) :
    List Field → Nat → Nat → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Prop
  | [], _, _, left, right, check, canon => finish left right check canon
  | item :: rest, index, cursor, left, right, check, canon =>
    let slot := mode.slot destination.width item cursor
    let nextCheck := checkTail mode destination inst rest (index + 1) slot.2 checkNext
    let nextCanon := canonTail mode destination inst rest slot.2 canonNext
    let reference := focus mode destination inst item cursor right canon nextCanon
    ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (host bindings)) right mode.readLabels reference ∧
    compare item index slot.1 left reference check canon nextCheck nextCanon
      (Replay profile ready bindings mode destination inst compare checkNext canonNext finish rest (index + 1) slot.2)

def MixedSlot (destination : RecordDestination) (bytes : Nat) (item : Field) (address : Nat) : Prop :=
  CanonicalHandle item ∨ StringField.Fits destination item ∧
    address % (layout destination.width item.type).alignment.bytes = 0 ∧ address + (layout destination.width item.type).size ≤ bytes

def mixed (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    FieldComparison grow sig := fun item index address left right check canon checkNext canonNext finish =>
  (CanonicalHandle item ∧ HandleFieldThen profile ready bindings item index (.memory address) left right check canon checkNext canonNext
    (fun () => finish)) ∨
  (∃ value : StringField, value.field = item ∧ StringFieldThen profile ready bindings older destination inst value.value (.memory address)
    left right check canon checkNext canonNext (fun () => finish))

/-- The depth bounds the certificate's structural descent, not callback
steps or the number of children in an aggregate. -/
inductive AggregateShape (stringLeaf : Field → Prop) : Nat → Field → Prop where
  | handle {depth item} : CanonicalHandle item → AggregateShape stringLeaf depth item
  | string {depth item} : stringLeaf item → AggregateShape stringLeaf depth item
  | aggregate {depth type items} : (∀ item ∈ items, AggregateShape stringLeaf depth item) →
      AggregateShape stringLeaf (depth + 1) (.aggregate type items)

def nested (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    Nat → FieldComparison grow sig
  | 0 => mixed profile ready bindings older destination inst
  | depth + 1 => fun item index address left right check canon checkNext canonNext finish =>
    mixed profile ready bindings older destination inst item index address left right check canon checkNext canonNext finish ∨
      ∃ type children, item = .aggregate type children ∧
        let entered := enterAggregate destination inst children index address left check checkNext
        ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (host bindings)) left [.tau] entered ∧
          Replay profile ready bindings .fields destination inst (nested profile ready bindings older destination inst depth)
            (aggregateNext index checkNext) canonNext finish children 0 address entered right check canon

abbrev ValueCheckNext (grow : SingleThreaded.GrowOracle) (sig : Signature) (output : Lower.Output) :=
  Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow))

abbrev ValueCanonNext (grow : SingleThreaded.GrowOracle) (sig : Signature) (output : Lower.Output) :=
  output.Result → Session grow sig (Ret (core3 grow))

abbrev ValueFinish (grow : SingleThreaded.GrowOracle) (sig : Signature) (output : Lower.Output) :=
  output.Result → Finish grow sig

def publishChecked (destination : RecordDestination) (inst : InstId) (pointer count index : Nat) (output : Lower.Output)
    (next : ValueCheckNext grow sig output) : CheckNext grow sig
  | .error issue => next (.error (.nested index issue))
  | .ok () => ListLower.publish (destination.context inst) destination.width pointer count output >>= fun value => next (.ok value)

def publishCanonical (destination : RecordDestination) (inst : InstId) (pointer count : Nat) (output : Lower.Output)
    (next : ValueCanonNext grow sig output) : CanonNext grow sig :=
  fun () => ListLower.publish (destination.context inst) destination.width pointer count output >>= next

def DescriptorThen (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (output : Lower.Output) (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (next : ValueFinish grow sig output) : Finish grow sig := fun left right check canon =>
  LocalThen profile ready bindings left right check canon (fun value => checkNext (.ok value)) canonNext next

/-- The actual admitted value-mode collection tail: strided entries followed
by the descriptor only on common success. Indirect maps do not use it. -/
def ValueEntriesReplay (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (compare : FieldComparison grow sig)
    (element : TypeOf) (entries : List Field) (index pointer : Nat) (output : Lower.Output)
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (next : ValueFinish grow sig output) : Finish grow sig :=
  Replay profile ready bindings (.elements (layout destination.width element).size) destination inst
    compare
    (publishChecked destination inst pointer entries.length index output checkNext)
    (publishCanonical destination inst pointer entries.length output canonNext)
    (DescriptorThen profile ready bindings output checkNext canonNext next) entries 0 pointer

abbrev ValueListReplay (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (element : TypeOf) (entries : List Field) (depth index pointer : Nat) (output : Lower.Output) :=
  ValueEntriesReplay profile ready bindings destination inst (nested profile ready bindings older destination inst depth)
    element entries index pointer output

def ValueListReturn (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (type element : TypeOf) (entries : List Field) (depth index : Nat) (output : Lower.Output)
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (initial reference last : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig)) (pointer : Nat)
    (seen : List (Label (core3 grow) (HostState sig))) : Prop :=
  CollectionVisit.Outcome profile ready bindings older destination inst type (layout destination.width element) entries index pointer output
    initial reference last cursor checkNext canonNext seen
    (fun _ => ValueListReplay profile ready bindings older destination inst element entries depth index pointer output checkNext canonNext
      (fun value reached canonical check canon => ChildFrameOver older reached canonical check canon ∧
        Core3.Grows initial.store.core reached.store.core ∧ reached.ctl = check.control (checkNext (.ok value)) ∧
        canonical.ctl = canon.control (canonNext value)))

def RecursiveValueReturn (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (compare : FieldComparison grow sig) (type element : TypeOf) (entries : List Field) (index : Nat) (output : Lower.Output)
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (finish : ValueFinish grow sig output)
    (initial reference last : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig)) (pointer : Nat)
    (seen : List (Label (core3 grow) (HostState sig))) : Prop :=
  CollectionVisit.Outcome profile ready bindings older destination inst type (layout destination.width element)
    entries index pointer output initial reference last cursor checkNext canonNext seen
    (fun _ => ValueEntriesReplay profile ready bindings destination inst compare element entries index pointer output
      checkNext canonNext finish)

abbrev ListReturn (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (compare : FieldComparison grow sig) (element : TypeOf) :=
  RecursiveValueReturn profile ready bindings older destination inst compare (.list element) element

def mapTail (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf)
    (entries : List Field) (cursor : Nat) : Session grow sig Unit :=
  CanonicalTree.elements Limits.spec Quirks.none (destination.context inst) destination.width entries
    (.memoryMap destination.width key element) (layout destination.width (.record (mapEntryFields key element))).size cursor

/-- Checked entries validate the compiled record footprint. The canonical
tail enters the allocation-time key/value slots directly. Its next entry
can only be visited after both actual field continuations succeed. -/
def MapEntriesReplay (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (compare : FieldComparison grow sig) (key : WIT.KeyType) (element : TypeOf)
    (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig) :
    List Field → Nat → Nat → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Prop
  | [], _, _, left, right, check, canon => finish left right check canon
  | entry :: rest, index, cursor, left, right, check, canon =>
    let type : TypeOf := .record (mapEntryFields key element)
    let stride := (layout destination.width type).size
    let nextCheck := checkTail (.elements stride) destination inst rest (index + 1) (cursor + stride) checkNext
    let nextCanon : CanonNext grow sig := fun () => mapTail destination inst key element rest (cursor + stride) >>= canonNext
    ∃ keyField valueField, entry = .aggregate type [keyField, valueField] ∧
      let entered := enterAggregate destination inst [keyField, valueField] index cursor left check nextCheck
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (host bindings)) left [.tau] entered ∧
      Replay profile ready bindings .placedFields destination inst compare (aggregateNext index nextCheck) nextCanon
        (MapEntriesReplay profile ready bindings destination inst compare key element checkNext canonNext finish rest (index + 1) (cursor + stride))
        [keyField, valueField] 0 cursor entered right check canon

def MapReturn (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (compare : FieldComparison grow sig) (key : WIT.KeyType) (element : TypeOf) (entries : List Field) (index address : Nat)
    (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig)
    (initial reference last : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig)) (pointer : Nat)
    (seen : List (Label (core3 grow) (HostState sig))) : Prop :=
  let output := Lower.Output.memory address
  CollectionVisit.Outcome profile ready bindings older destination inst (.map key element)
    (layout destination.width (.record (mapEntryFields key element))) entries index pointer output
    initial reference last cursor checkNext canonNext seen
    (fun _ => MapEntriesReplay profile ready bindings destination inst compare key element
      (publishChecked destination inst pointer entries.length index output checkNext)
      (publishCanonical destination inst pointer entries.length output canonNext)
      (DescriptorThen profile ready bindings output checkNext canonNext (fun () => finish)) entries 0 pointer)

/-- The fragment is structural; depth does not bound callback execution. -/
inductive ListTreeShape (stringLeaf : Field → Prop) : Nat → Field → Prop where
  | handle {depth item} : CanonicalHandle item → ListTreeShape stringLeaf depth item
  | string {depth item} : stringLeaf item → ListTreeShape stringLeaf depth item
  | scalar {depth type} (payload : Stored.Payload type) : LocalDataType type →
      ListTreeShape stringLeaf depth (.data type payload)
  | aggregate {depth type items} : (∀ item ∈ items, ListTreeShape stringLeaf depth item) →
      ListTreeShape stringLeaf (depth + 1) (.aggregate type items)
  | list {depth element entries} : (∀ item ∈ entries, ListTreeShape stringLeaf depth item) →
      ListTreeShape stringLeaf (depth + 1) (.dynamic (.list element) element entries)
  | map {depth key element entries} :
      (∀ entry ∈ entries, ∃ fields, entry = .aggregate (.record (mapEntryFields key element)) fields) →
      (∀ entry ∈ entries, ∀ fields, entry = .aggregate (.record (mapEntryFields key element)) fields →
        ∀ field ∈ fields, ListTreeShape stringLeaf depth field) →
      ListTreeShape stringLeaf (depth + 1) (.dynamic (.map key element) (.record (mapEntryFields key element)) entries)
  | sum {depth type arms tag selected} :
      (∀ child, selected = some child → ListTreeShape stringLeaf depth child) →
      ListTreeShape stringLeaf (depth + 1) (.sum type arms tag selected)
  | fixed {depth element length entries} : (∀ item ∈ entries, ListTreeShape stringLeaf depth item) →
      ListTreeShape stringLeaf (depth + 1) (.fixed element length entries)

def LocalData (item : Field) : Prop :=
  ∃ (type : TypeOf) (payload : Stored.Payload type), item = .data type payload ∧ LocalDataType type

def memoryLeaf (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    FieldComparison grow sig := fun item index address left right check canon checkNext canonNext finish =>
  mixed profile ready bindings older destination inst item index address left right check canon checkNext canonNext finish ∨
    LocalData item ∧
    LocalFieldThen profile ready bindings (.memory address) left right check canon checkNext canonNext (fun () => finish)

def SumThen (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (compare : FieldComparison grow sig)
    (arms : List (Option TypeOf)) (selected : Option Field) (index base : Nat) (checkNext : CheckNext grow sig)
    (canonNext : CanonNext grow sig) (finish : Finish grow sig) : Finish grow sig := fun left right check canon =>
  let address := sumPayloadAddress destination.width arms base
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason Unit)
      (checkLabels canonLabels : List (Label (core3 grow) (HostState sig))),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest
      (sumCheckedNext destination inst selected index address checkNext) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest
      (sumCanonicalNext destination inst selected address canonNext) result
    Steps profile ready (specDispatch ready (host bindings)) left checkLabels lhs ∧
    Steps profile ready (specDispatch ready (host bindings)) right canonLabels rhs ∧
    visible checkLabels = visible canonLabels ∧
    match result with
    | .error reason => ∃ leading, visible canonLabels = leading ++ [.trap reason]
    | .ok () =>
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (host bindings)) left checkLabels lhs ∧
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (host bindings)) right canonLabels rhs ∧
      match selected with
      | none => finish lhs rhs check canon
      | some item => compare item 0 address lhs rhs check canon (aggregateNext index checkNext) canonNext finish

/-- The installed allocator path can remain suspended. The child traversal
is required only at its marked return and only after the reached live check. -/
def listTree (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    Nat → FieldComparison grow sig
  | 0 => memoryLeaf profile ready bindings older destination inst
  | depth + 1 => fun item index address left right check canon checkNext canonNext finish =>
    let child := listTree profile ready bindings older destination inst depth
    memoryLeaf profile ready bindings older destination inst item index address left right check canon checkNext canonNext finish ∨
      (∃ type children, item = .aggregate type children ∧
        let entered := enterAggregate destination inst children index address left check checkNext
        ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (host bindings)) left [.tau] entered ∧
          Replay profile ready bindings .fields destination inst child (aggregateNext index checkNext) canonNext finish
            children 0 address entered right check canon) ∨
      (∃ element entries, item = .dynamic (.list element) element entries ∧
        (match Record.prepare left.store left.host.writer (Field.listObjects entries) with
        | .error _ => ReachesKeeping profile ready (specDispatch ready (host bindings)) (fun _ => True)
            left right check canon checkNext canonNext
        | .ok () => CollectionReplayFor profile ready bindings older destination inst (.list element) element entries
            index (.memory address) left right check canon checkNext canonNext
            (ListReturn profile ready bindings older destination inst child element entries index (.memory address)
              checkNext canonNext (fun () => finish)))) ∨
      (∃ key element entries, item = .dynamic (.map key element) (.record (mapEntryFields key element)) entries ∧
        (match Record.prepare left.store left.host.writer (Field.listObjects entries) with
        | .error _ => ReachesKeeping profile ready (specDispatch ready (host bindings)) (fun _ => True)
            left right check canon checkNext canonNext
        | .ok () => CollectionReplayFor profile ready bindings older destination inst (.map key element)
            (.record (mapEntryFields key element)) entries index (.memory address) left right check canon checkNext canonNext
            (MapReturn profile ready bindings older destination inst child key element entries index address checkNext canonNext finish))) ∨
      (∃ type arms tag selected, item = .sum type arms tag selected ∧
        SumThen profile ready bindings destination inst child arms selected index address checkNext canonNext finish left right check canon) ∨
      ∃ element length entries, item = .fixed element length entries ∧
        let mode := Track.elements (layout destination.width element).size
        let reference := { right with ctl := canon.control (mode.canonical destination inst entries address >>= canonNext) }
        ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (host bindings)) right [.tau] reference ∧
          Replay profile ready bindings mode destination inst child (aggregateNext index checkNext) canonNext finish
            entries 0 address left reference check canon

def FlatAllocatingLeaf (stringLeaf : Field → Prop) (entryDepth : Nat) (item : Field) : Prop :=
  (CanonicalHandle item ∨ stringLeaf item) ∨ LocalData item ∨
    ∃ type element entries, item = .dynamic type element entries ∧
      ∀ entry ∈ entries, ListTreeShape stringLeaf entryDepth entry

/-- A collection in a flat sequence enters the memory comparison at its
actual allocator return. Typed refusal stops the checked sequence before
its following siblings; only common success contributes descriptor words. -/
def flatAllocating (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (entryDepth : Nat) : FlatFieldComparison grow sig := fun item index left right check canon checkNext canonNext finish =>
  mixedFlatComparison profile ready bindings older destination inst item index left right check canon checkNext canonNext finish ∨
    (LocalData item ∧ LocalFieldThen profile ready bindings .flat left right check canon checkNext canonNext finish) ∨
    ∃ type element entries, item = .dynamic type element entries ∧
      match Record.prepare left.store left.host.writer (Field.listObjects entries) with
      | .error _ => ReachesKeeping profile ready (specDispatch ready (host bindings)) (fun _ => True)
          left right check canon checkNext canonNext
      | .ok () => CollectionReplayFor profile ready bindings older destination inst type element entries index .flat
          left right check canon checkNext canonNext
          (RecursiveValueReturn profile ready bindings older destination inst
            (listTree profile ready bindings older destination inst entryDepth) type element entries index .flat
            checkNext canonNext finish)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence
