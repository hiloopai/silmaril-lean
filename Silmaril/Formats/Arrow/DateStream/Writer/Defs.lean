module

public import Silmaril.Formats.Arrow.DateStream.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs

/-! # Checked emission of single-column Arrow Date32 IPC V5 streams -/

@[expose] public section

namespace Silmaril.Formats.Arrow.DateStream.Writer

open Silmaril.Formats.DateInterop

abbrev Column := List (Option Date32.Payload)

inductive Error where
  | writer (cause : Arrow.Error)
  | record (index : Nat) (cause : Arrow.Error)
  | readback (cause : DateStream.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

/-- The DATE reader's view of the supplied field and ordered signed slots. -/
def observation (name : String) (nullable : Bool) (batches : List Column) : DateStream.Stream :=
  ⟨⟨name, nullable, .day⟩, batches.map (List.map (Option.map Date32.toCivil))⟩

open MetadataWriter.Wire

/-- DateUnit's IDL default is MILLISECOND. The vtable entry at offset
four makes the zero-valued DAY enum explicit in the DATE table. -/
def date32FieldBytes (name : String) (nullable : Bool) : KBytes :=
  fieldFragment name nullable 8 (words [halfwords 6 8, halfwords 4 0, 8, 0, 0])

namespace Internal

def schemaMetadata (name : String) (nullable : Bool) : KBytes :=
  messagePrefix 1 56 0 ++ schemaPayloadOf [date32FieldBytes name nullable]

/-- The size depends on the UTF-8 byte length, including the field's NUL and padding. -/
def schemaSize (name : String) : Nat :=
  let fragment := 53 + name.utf8ByteSize
  72 + (fragment + Arrow.Writer.padding fragment)

def emitSchema (limits : Limits) (name : String) (nullable : Bool) : Except Error KBytes := do
  if limits.fields = 0 then .error (.writer (.limit .fields)) else do
    let size := schemaSize name
    if size ≥ 2^31 then .error (.writer (.malformed .metadataLength))
    else if size > limits.metadataBytes then .error (.writer (.limit .metadataBytes))
    else .ok (StreamWriter.envelopeBytes size ++ schemaMetadata name nullable)

def recordInput (name : String) (nullable : Bool) (slots : Column) : Arrow.Writer.BatchInput :=
  ⟨slots.length, [⟨name, nullable, .int32 slots⟩]⟩

/-- Pack a Date32 record through the checked physical Int32 writer. The enclosing
Schema supplies its logical DATE type. -/
def emitRecord (limits : ObservationLimits) (name : String) (nullable : Bool)
    (slots : Column) (index : Nat) : Except Error KBytes :=
  (StreamWriter.emitRecord limits [⟨name, nullable, .int32⟩]
    (recordInput name nullable slots)).mapError (.record index)

def serialize (limits : ObservationLimits) (name : String) (nullable : Bool)
    (batches : List Column) : Except Error KBytes := do
  if batches.length > limits.ipc.batches then .error (.writer (.limit .batches)) else do
    (Body.checkBudget limits 1 (batches.map List.length).sum).mapError .writer
    let header ← emitSchema limits.ipc name nullable
    let records ← batches.zipIdx.mapM fun (slots, index) => emitRecord limits name nullable slots index
    return header ++ records.foldr (· ++ ·) StreamWriter.eos

end Internal

/-- Return complete IPC bytes only after the checked DATE reader recovers the
exact field, ordered nullable dates and original batch boundaries. -/
def emit (limits : ObservationLimits) (name : String) (nullable : Bool)
    (batches : List Column) : Except Error KBytes := do
  let wire ← Internal.serialize limits name nullable batches
  let readback ← (DateStream.read limits.ipc wire).mapError .readback
  if readback = observation name nullable batches then .ok wire else .error .readbackMismatch

end Silmaril.Formats.Arrow.DateStream.Writer
