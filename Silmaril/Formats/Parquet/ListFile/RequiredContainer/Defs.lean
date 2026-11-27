module

public import Silmaril.Formats.Parquet.ListFile.Defs
public import Silmaril.Formats.Arrow.ListInt32.Stream.Writer.Defs

/-! A required LIST of nullable INT32 elements, with one complete uncompressed
PLAIN V1 frame per group and a required native Arrow LIST field. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer

open ListPage (Event Row)
open Silmaril.Relational

abbrev Triple := Nat × Nat × Option Int32

/-- The required container contributes no definition level. A null container
has no representation. Definition zero is an empty list. -/
def eventWire : Event → Option Triple
  | .nullList => none
  | .emptyList => some (0, 0, none)
  | .first item => some (0, if item.isSome then 2 else 1, item)
  | .next item => some (1, if item.isSome then 2 else 1, item)

def readEvent : Triple → Except ListPage.Error Event
  | (0, 0, none) => .ok .emptyList
  | (0, 1, none) => .ok (.first none)
  | (1, 1, none) => .ok (.next none)
  | (0, 2, some item) => .ok (.first (some item))
  | (1, 2, some item) => .ok (.next (some item))
  | _ => .error .levelPair

def valueMask (definitions : List Nat) : List Bool :=
  definitions.map (· == 2)

def decodeSections (limits : ListPage.Limits) (slots : Nat) (repetition definition scalars : Bytes) :
    Except ListPage.Error (List Event) := do
  let reps ← (Hybrid.decode 1 slots limits.levels repetition).mapError .repetition
  let defs ← (Hybrid.decode 2 slots limits.levels definition).mapError .definition
  if defs.any (fun level => 2 < level) then return ← throw .levelPair
  let mask := valueMask defs
  let values ← (Plain.decodeInt32 (mask.count true) scalars).mapError .plain
  let entries ← (FlatPage.reconstruct mask values).mapError .reconstruct
  (reps.zip (defs.zip entries)).mapM readEvent

def decodeEvents (limits : ListPage.Limits) (slots : Nat) (body : Bytes) :
    Except ListPage.Error (List Event) := do
  if limits.maxBodyBytes < body.length then return ← throw .bodyLimit
  let first ← (FlatPage.splitV1Optional limits.levels.bytes body).mapError .repetitionSection
  let second ← (FlatPage.splitV1Optional limits.levels.bytes first.scalars).mapError .definitionSection
  decodeSections limits slots first.definitions second.definitions second.scalars

structure SectionsWire (slots : Nat) (repetition definition scalars : Bytes) (events : List Event) : Prop where
  count : events.length = slots
  data : ∃ (reps defs : List Nat) (values : List Int32) (entries : List (Option Int32)),
    Hybrid.Wire 1 slots repetition.toList reps ∧ Hybrid.Wire 2 slots definition.toList defs ∧
    reps.length = slots ∧ defs.length = slots ∧ entries.length = slots ∧
    Plain.decodeInt32 ((valueMask defs).count true) scalars = .ok values ∧
    entries.map Option.isSome = valueMask defs ∧ entries.filterMap id = values ∧
    events.map eventWire = (reps.zip (defs.zip entries)).map some

structure EventsWire (limits : ListPage.Limits) (slots : Nat) (body : Bytes) (events : List Event) : Prop where
  cap : body.length ≤ limits.maxBodyBytes
  data : ∃ (repLength defLength : List UInt8) (repBytes defBytes scalarBytes : Bytes),
    repLength.length = 4 ∧ defLength.length = 4 ∧
    KBytes.leVal repLength = repBytes.length ∧ KBytes.leVal defLength = defBytes.length ∧
    body.toList = repLength ++ repBytes.toList ++ defLength ++ defBytes.toList ++ scalarBytes.toList ∧
    SectionsWire slots repBytes defBytes scalarBytes events

abbrev Checked := ListFile.Checked .required

def openFile := ListFile.openFileFor .required

/-- Read the exact original frame payload and check its separate advertised
level-slot and completed row counts. -/
def readFrame (checked : Checked) (framed : FramedGroup) (frame : Page.Frame) :
    Except ListFile.ReadError (List Row) := do
  if checked.limits.page.maxBodyBytes < frame.value.compressedSize then return ← throw .bodyLimit
  let some body := checked.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) |
    throw .payloadBounds
  let info ← (ListPage.checkV1 framed.chunk.metadata.codec frame.value body).mapError .page
  if framed.chunk.metadata.numValues ≠ (info.numValues : Int) then
    return ← throw (.slotCount framed.chunk.metadata.numValues info.numValues)
  let expected := framed.group.numRows.toNat
  if checked.limits.page.maxRows < expected then return ← throw (.page .rowLimit)
  let events ← (decodeEvents checked.limits.page info.numValues body).mapError .page
  let rows ← (ListPage.reconstruct events).mapError .page
  if rows.length ≠ expected then return ← throw (.page (.rowCount expected rows.length))
  pure rows

inductive GroupError where
  | framing (cause : ListFile.ReadError)
  | frame (ordinal offset : Nat) (cause : ListFile.ReadError)
  deriving DecidableEq, Repr

def readGroup (checked : Checked) (ordinal : Nat) : Except GroupError (List Row) := do
  let framed ← (checked.frameGroup ordinal).mapError .framing
  let [frame] := framed.frames | throw (.framing .pageCount)
  (readFrame checked framed frame).mapError (.frame 0 frame.header.start)

structure FrameWire (checked : Checked) (framed : FramedGroup) (frame : Page.Frame) (rows : List Row) : Prop where
  parents : ∀ row ∈ rows, row.isSome = true
  data : ∃ body info,
    checked.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some body ∧
    ListPage.V1Wire framed.chunk.metadata.codec frame.value body info ∧
    framed.chunk.metadata.numValues = (info.numValues : Int) ∧
    framed.group.numRows.toNat ≤ checked.limits.page.maxRows ∧ rows.length = framed.group.numRows.toNat ∧
    EventsWire checked.limits.page info.numValues body (rows.flatMap ListPage.rowEvents)

structure GroupWire (checked : Checked) (ordinal : Nat) (rows : List Row) : Prop where
  data : ∃ framed frame,
    ListFile.FramedGroupWire checked ordinal framed ∧
    framed.frames = [frame] ∧ FrameWire checked framed frame rows

inductive Kind where
  | requiredListOfNullableInt32
  deriving DecidableEq, Repr

abbrev Cell (_ : Kind) := List (Option Int32)

abbrev schema (checked : Checked) : Scan.Schema String Kind :=
  ⟨1, fun _ => (checked.shape.outer.name, .requiredListOfNullableInt32)⟩

def rowsOf (checked : Checked) (slots : List Row) : Reader.RowGroup (schema checked) Cell :=
  slots.map fun slot _ => slot

inductive SourceError where
  | openFailure (cause : ListFile.OpenError)
  | groupFailure (ordinal : Nat) (cause : GroupError)
  deriving DecidableEq, Repr

def readAt (checked : Checked) (index : Nat) :
    Except SourceError (Reader.RowGroup (schema checked) Cell) :=
  ((readGroup checked index).mapError (.groupFailure index)).map (rowsOf checked)

structure Limits where
  parquet : ListFile.Limits := {}
  ipc : Arrow.ListInt32.Stream.Limits := {}

inductive Error where
  | source (cause : SourceError)
  | closed
  | writer (cause : Arrow.ListInt32.Stream.Writer.Error)
  deriving DecidableEq, Repr

structure Result where
  trace : Arrow.Events.EventStream String Cell SourceError
  wire : Except Error KBytes

def fieldOf (checked : Checked) : Arrow.ListInt32.Field :=
  ⟨checked.shape.outer.name, checked.shape.element.name⟩

def writeBatches (limits : Arrow.ListInt32.Stream.Limits) (checked : Checked)
    (batches : List (Arrow.Events.Batch (schema checked) Cell)) :
    Arrow.Events.Termination SourceError → Except Error KBytes
  | .eos => (Arrow.ListInt32.Stream.Writer.emitFor false limits (fieldOf checked)
      (batches.map (·.values (0 : Fin 1)))).mapError .writer
  | .readError cause | .closeError cause => .error (.source cause)
  | .closed => .error .closed

/-- Keep complete earlier groups on a source failure; only complete source EOS
can reach native writer admission. -/
def convert (limits : Limits) (source : Bytes) : Result :=
  match openFile limits.parquet source with
  | .error cause => ⟨.error (.openFailure cause), .error (.source (.openFailure cause))⟩
  | .ok checked =>
    let (groups, ending) := Reader.denoteGroups (readAt checked) (List.range checked.snapshot.groupCount)
    let batches := groups.map AlignedColumns.ofRows
    ⟨.ok ⟨schema checked, ⟨batches, ending⟩⟩, writeBatches limits.ipc checked batches ending⟩

structure Readback (limits : Limits) (source : Bytes) (wire : KBytes) : Prop where
  data : ∃ checked groups decoded size,
    openFile limits.parquet source = .ok checked ∧
    ListFile.OpenWire limits.parquet source checked ∧
    (List.range checked.snapshot.groupCount).mapM (readGroup checked) = .ok groups ∧
    List.Forall₂ (GroupWire checked) (List.range checked.snapshot.groupCount) groups ∧
    (convert limits source).trace = .ok ⟨schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ rowsOf checked), .eos⟩⟩ ∧
    Arrow.ListInt32.Stream.readFor false limits.ipc wire = .ok decoded ∧
    Arrow.ListInt32.Stream.Writer.Agrees (fieldOf checked) groups decoded ∧
    wire.wf = true ∧
    Arrow.readEnvelope limits.ipc.ipc wire 0 = .ok (.metadata size) ∧
    Arrow.ListInt32.readSchemaFor false limits.ipc.ipc (wire.slice 8 size) = .ok (fieldOf checked) ∧
    Arrow.ListInt32.Stream.BatchesWire limits.ipc wire limits.ipc.ipc.batches 0 0 (8 + size) decoded.batches ∧
    Arrow.ListInt32.Stream.checkParents false decoded.batches = .ok ()

end Silmaril.Formats.Parquet.ListFile.RequiredContainer
