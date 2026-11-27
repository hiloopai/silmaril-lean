module

public import Silmaril.Formats.Parquet.NestedPoint.Multi.Defs
public import Silmaril.Formats.Arrow.StructInt32.Stream.Writer.Defs

/-! Ordered checked NestedPoint row groups as typed Events and native Struct IPC. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc

open Silmaril.Relational
open Arrow.StructInt32 (Field)
open NestedPresence (Presence)

structure SourceLimits where
  snapshot : Snapshot.Limits := {}
  group : Multi.Limits := {}

structure Limits where
  parquet : SourceLimits := {}
  ipc : Arrow.ObservationLimits := {}

inductive OpenError where
  | snapshot (cause : Snapshot.Error Unit)
  | leaf (ordinal : Nat) (cause : Footer.NestedLeaf.Error)
  | profile (ordinal : Nat)
  | leafAnnotation (ordinal : Nat)
  deriving DecidableEq, Repr

inductive SourceError where
  | openFailure (cause : OpenError)
  | groupFailure (ordinal : Nat) (cause : Multi.Error)
  deriving DecidableEq, Repr

inductive Error where
  | source (cause : SourceError)
  | closed
  | writer (cause : Arrow.StructInt32.Stream.Writer.Error)
  deriving DecidableEq, Repr

structure Checked where
  private mk ::
  snapshot : Snapshot.Checked
  field : Field

def repetition : Multi.Kind → Footer.Repetition
  | .signed => .required
  | .wide => .optional

/-- Preserve both selected original leaf items. The projection to Arrow is
only defined for the two unannotated signed physical types. -/
def selectLeaf (limits : Footer.Limits) (snapshot : Snapshot.Checked) (kind : Multi.Kind) :
    Except OpenError (Footer.NestedLeaf.Selection snapshot) := do
  let leaf ← (Footer.NestedLeaf.select limits snapshot kind.column).mapError (.leaf kind.column)
  if leaf.leaf.repetition = some (repetition kind) ∧ leaf.physical = kind.physical then
    if leaf.leafItem.fields.any (fun item => item.id == 6 || item.id == 10) then
      .error (.leafAnnotation kind.column)
    else .ok leaf
  else .error (.profile kind.column)

def fieldOf {snapshot : Snapshot.Checked} (left right : Footer.NestedLeaf.Selection snapshot) : Field :=
  ⟨left.parent.name, ⟨left.leaf.name, left.leaf.repetition == some .optional⟩,
    ⟨right.leaf.name, right.leaf.repetition == some .optional⟩⟩

@[no_expose] def openFile (limits : SourceLimits) (bytes : Bytes) : Except OpenError Checked := do
  let snapshot ← (Snapshot.check (Failure := Unit) limits.snapshot bytes).mapError .snapshot
  let left ← selectLeaf limits.group.leaf.footer snapshot .signed
  let right ← selectLeaf limits.group.leaf.footer snapshot .wide
  return ⟨snapshot, fieldOf left right⟩

abbrev Cell (_ : Field) := Int32 × Option Int64

abbrev schema (field : Field) : Scan.Schema String Field :=
  ⟨1, fun _ => (field.name, field)⟩

abbrev Trace (field : Field) := Arrow.Events.Trace (schema field) Cell SourceError
abbrev SourceTrace := Arrow.Events.EventStream String Cell SourceError

def rowsFor (field : Field) (rows : List NestedPoint.Row) : Reader.RowGroup (schema field) Cell :=
  rows.map fun row _ => row

def groupSource (limits : Multi.Limits) (checked : Checked) :
    Reader.Source Nat (schema checked.field) Cell SourceError :=
  ⟨List.range checked.snapshot.groupCount,
    fun ordinal =>
      ((Multi.read limits checked.snapshot ordinal).mapError (.groupFailure ordinal)).map (rowsFor checked.field),
    fun _ => .ok ()⟩

/-- Form aligned batches from the common reader denotation, retaining exactly
the groups completed before any reached source error. -/
def trace (limits : Multi.Limits) (checked : Checked) : Trace checked.field :=
  let groups := groupSource limits checked
  let observed := Reader.denoteGroups groups.readGroup groups.groups
  ⟨observed.1.map AlignedColumns.ofRows, observed.2⟩

def readAll (limits : SourceLimits) (bytes : Bytes) : SourceTrace :=
  ((openFile limits bytes).mapError .openFailure).map fun checked => ⟨schema checked.field, trace limits.group checked⟩

abbrev NativeRow := Arrow.StructInt32.Stream.RowFor Int64

/-- The existing Parquet observation forces the first child present whenever
the parent is present. The optional wide child remains an independent slot. -/
def nativeRow (row : NestedPoint.Row) : NativeRow :=
  row.map fun (signed, wide) => (some signed, wide)

def nativeBatches {field : Field} (source : Trace field) : List (List NativeRow) :=
  source.batches.map fun batch => (batch.values 0).map nativeRow

/-- The writer only runs after source EOS. A source failure returns no wire. -/
def writeTrace (limits : Arrow.ObservationLimits) (field : Field) (source : Trace field) :
    Except Error KBytes :=
  match source.termination with
  | .readError cause | .closeError cause => .error (.source cause)
  | .closed => .error .closed
  | .eos => (Arrow.StructInt32.Stream.Writer.emitFor .int64 limits field (nativeBatches source)).mapError .writer

structure Result where
  trace : SourceTrace
  wire : Except Error KBytes

/-- Bind the footer once and retain the same completed Events trace even
when either source reading or writer admission fails. -/
def convert (limits : Limits) (bytes : Bytes) : Result :=
  match openFile limits.parquet bytes with
  | .error cause => ⟨.error (.openFailure cause), .error (.source (.openFailure cause))⟩
  | .ok checked =>
    let source := trace limits.parquet.group checked
    ⟨.ok ⟨schema checked.field, source⟩, writeTrace limits.ipc checked.field source⟩

structure LeafWire (limits : Footer.Limits) (snapshot : Snapshot.Checked) (kind : Multi.Kind)
    (leaf : Footer.NestedLeaf.Selection snapshot) : Prop where
  original : Footer.NestedLeaf.Wire limits kind.column leaf
  physical : leaf.physical = kind.physical
  repetition : leaf.leaf.repetition = some (ToIpc.repetition kind)
  unannotated : ∀ item ∈ leaf.leafItem.fields, item.id ≠ 6 ∧ item.id ≠ 10

structure OpenWire (limits : SourceLimits) (bytes : Bytes) (checked : Checked) : Prop where
  snapshot : Snapshot.check (Failure := Unit) limits.snapshot bytes = .ok checked.snapshot
  bytesExact : checked.snapshot.bytes = bytes
  leaves : ∃ left right,
    LeafWire limits.group.leaf.footer checked.snapshot .signed left ∧
    LeafWire limits.group.leaf.footer checked.snapshot .wide right ∧
    checked.field = fieldOf left right ∧
    left.parent = right.parent ∧
    left.parent.repetition = some .optional ∧
    left.leaf.repetition = some .required ∧ right.leaf.repetition = some .optional

/-- The original wide-leaf state already distinguishes all three possible
visible row shapes. The aligned required sibling supplies the signed coordinate. -/
inductive SlotWire : Presence → Option Int32 → Option Int64 → NativeRow → Prop where
  | absent : SlotWire .parentAbsent none none none
  | nullChild (left : Int32) : SlotWire .childNull (some left) none (some (some left, none))
  | value (left : Int32) (right : Int64) :
      SlotWire .value (some left) (some right) (some (some left, some right))

structure GroupWire (limits : Multi.Limits) (snapshot : Snapshot.Checked) (ordinal : Nat)
    (rows : List NestedPoint.Row) : Prop where
  count : ∃ group, snapshot.groupAt ordinal = some group ∧ rows.length = group.numRows.toNat
  aligned : ∃ left right,
    Multi.ColumnWire .signed limits snapshot ordinal left ∧
    Multi.ColumnWire .wide limits snapshot ordinal right ∧
    Multi.parentMask left.states = Multi.parentMask right.states ∧
    rows = NestedPoint.pairSlots left.slots right.slots ∧
    List.Forall₂ (fun (state, lhs, rhs) row => SlotWire state lhs rhs row)
      (right.states.zip (left.slots.zip right.slots)) (rows.map nativeRow)

structure Readback (limits : Limits) (bytes : Bytes) (wire : KBytes) : Prop where
  data : ∃ (checked : Checked) (groups : List (List NestedPoint.Row))
      (observed : Arrow.StructInt32.Stream.Observed Int64) (size : Nat),
    openFile limits.parquet bytes = .ok checked ∧ OpenWire limits.parquet bytes checked ∧
    (List.range checked.snapshot.groupCount).mapM (Multi.read limits.parquet.group checked.snapshot) = .ok groups ∧
    List.Forall₂ (GroupWire limits.parquet.group checked.snapshot) (List.range checked.snapshot.groupCount) groups ∧
    (convert limits bytes).trace = .ok ⟨schema checked.field,
      ⟨groups.map (AlignedColumns.ofRows ∘ rowsFor checked.field), .eos⟩⟩ ∧
    Arrow.StructInt32.Stream.readFor .int64 limits.ipc wire = .ok observed ∧
    Arrow.StructInt32.Stream.Writer.AgreesFor checked.field (groups.map (List.map nativeRow)) observed ∧
    wire.wf = true ∧ Arrow.readEnvelope limits.ipc.ipc wire 0 = .ok (.metadata size) ∧
    Arrow.StructInt32.readSchemaFor .int64 limits.ipc.ipc (wire.slice 8 size) = .ok checked.field ∧
    Arrow.StructInt32.Stream.BatchesWireFor .int64 limits.ipc checked.field wire
      limits.ipc.ipc.batches 0 (8 + size) observed.batches

end Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc
