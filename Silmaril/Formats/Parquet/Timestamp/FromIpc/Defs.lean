module

public import Silmaril.Formats.Arrow.TimestampStream.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Defs
public import Silmaril.Formats.Parquet.FlatInt32Writer.Compact.Defs
public import Silmaril.Formats.Parquet.PlainV1Writer.Defs

/-! Native uncompressed PLAIN INT64 Parquet TIMESTAMP from one V5 IPC field. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.FromIpc

open Silmaril.Numeric.Timestamp (ConversionError Ticks)
open FlatInt32Writer
open ColumnarTimestamp.Parquet (TimeUnit)

structure Limits where
  snapshot : Snapshot.Limits := {}
  leaf : Leaf.Limits := {}
  maxInputBytes : Nat := 256 * 1024 * 1024
  maxFileBytes : Nat := 256 * 1024 * 1024
  maxGroups : Nat := 4096
  maxTotalRows : Nat := 1024 * 1024

inductive Error where
  | inputByteLimit
  | source (cause : Arrow.TimestampStream.Error)
  | seconds
  | timezone (actual : String)
  | schemaLimit
  | groupLimit
  | totalRows
  | requiredNull (group : Nat)
  | payload (group : Nat) (cause : ConversionError)
  | pageLimit (group : Nat)
  | fileLimit
  | footer (cause : Compact.Error)
  | extent
  | openReadback (cause : Leaf.Error)
  | groupReadback (group : Nat) (cause : Leaf.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

/-- Explicitly admit the original unit and exact UTC or local epoch convention. -/
def descriptor (binding : Arrow.TimestampBatch.Binding) : Except Error Timestamp.Descriptor := do
  let unit : TimeUnit ← match binding.metadata.unit with
    | .second => .error .seconds
    | .millisecond => .ok .millis
    | .microsecond => .ok .micros
    | .nanosecond => .ok .nanos
  let adjusted ← match binding.metadata.timezone with
    | none => .ok false
    | some zone => if zone = "UTC" then .ok true else .error (.timezone zone)
  return ⟨unit, adjusted⟩

structure Source where
  stream : Arrow.TimestampStream.Stream
  descriptor : Timestamp.Descriptor

/-- Refuse unsupported metadata before reading record bodies. Admitted
streams use the original batch walk through exact EOS. -/
def readSource (ipc : Arrow.Limits) (limits : Limits) (input : KBytes) : Except Error Source :=
  if limits.maxInputBytes < input.len then .error .inputByteLimit
  else if !input.wf then .error (.source .source)
  else do
    let (binding, start) ← (Arrow.TimestampStream.readSchema ipc input).mapError .source
    let annotation ← descriptor binding
    let batches ← (Arrow.TimestampStream.readBatches ipc input binding ipc.batches 0 start).mapError .source
    return ⟨⟨binding, batches⟩, annotation⟩

def totalRows (stream : Arrow.TimestampStream.Stream) : Nat := (stream.batches.map List.length).sum

namespace Internal

/-- Write the modern TIMESTAMP union. The format also specifies the
matching legacy unit tag for millis and micros under either interpretation. -/
def leaf (descriptor : Timestamp.Descriptor) (column : Compact.ColumnIndex) : Compact.Write Unit := do
  Compact.field 1 5
  Compact.integer .i32 2
  Compact.field 2 5
  Compact.integer .i32 (if column.optional then 1 else 0)
  Compact.field 1 8
  Compact.text column.name
  let (unit, converted) : Nat × Option Int := match descriptor.unit with
    | .millis => (1, some 9)
    | .micros => (2, some 10)
    | .nanos => (3, none)
  if let some legacy := converted then
    Compact.field 2 5
    Compact.integer .i32 legacy
  Compact.field (if converted.isSome then 4 else 6) 12
  Compact.field 8 12
  Compact.field 1 (if descriptor.isAdjustedToUTC then 1 else 2)
  Compact.field 1 12
  Compact.field unit 12
  -- Close the unit member, TimeUnit, TimestampType, LogicalType, and leaf.
  for _ in List.range 5 do Compact.octet 0

def checkBudget (limits : Limits) (stream : Arrow.TimestampStream.Stream) : Except Error Unit := do
  let compact := limits.snapshot.footer.compact
  if compact.maxCollectionSize < 2 || stream.binding.name.utf8ByteSize > compact.maxBinaryBytes then
    throw .schemaLimit
  if stream.batches.length > min limits.maxGroups compact.maxCollectionSize then throw .groupLimit
  let rows := totalRows stream
  if rows > limits.maxTotalRows || rows ≥ 2^63 then throw .totalRows

structure PagePlan where
  slots : List (Option Int64)
  header : Bytes
  bodySize : Nat

def PagePlan.size (page : PagePlan) : Nat := page.header.length + page.bodySize

def planPage (limits : Leaf.Limits) (binding : Arrow.TimestampBatch.Binding)
    (batch : Arrow.TimestampBatch.Column binding) (index : Nat) : Except Error PagePlan := do
  if !binding.nullable && batch.any Option.isNone then throw (.requiredNull index)
  let rows := batch.length
  let definitions := if binding.nullable then 2 * rows else 0
  let size := (if binding.nullable then 4 else 0) + definitions + 8 * batch.countP Option.isSome
  if rows > min limits.maxRows limits.page.levels.values || rows ≥ Hybrid.runLimit ||
      definitions > limits.page.levels.bytes || size ≥ 2^31 ||
      size > min limits.page.compressedBytes limits.page.uncompressedBytes ||
      limits.framing.maxPages = 0 then throw (.pageLimit index)
  let some header := PlainV1Writer.encodeHeader rows size | throw (.pageLimit index)
  if header.length > limits.framing.maxHeaderBytes then throw (.pageLimit index)
  let slots ← (batch.mapM (Option.mapM binding.metadata.encode)).mapError (.payload index)
  return ⟨slots, header, size⟩

def emitPage (nullable : Bool) (page : PagePlan) : Except Error Bytes := do
  let values := Plain.encodeInt64 (page.slots.filterMap id)
  let body := if nullable then
    let definitions := PlainV1Writer.definitionOctets page.slots
    (Bytes.ofList (KBytes.unpack 4 definitions.length ++ definitions)).append values
  else values
  if body.length ≠ page.bodySize then throw .extent
  return page.header.append body

def groupIndices (column : Compact.ColumnIndex) (start : Nat) :
    List PagePlan → List (Nat × List Compact.ColumnIndex)
  | [] => []
  | page :: rest =>
    let stop := start + page.size
    (page.slots.length, [{ column with span := ⟨start, stop⟩ }]) :: groupIndices column stop rest

/-- Measure the entire file and budget its footer before building page bodies. -/
def serialize (limits : Limits) (source : Source) : Except Error Bytes := do
  let stream := source.stream
  checkBudget limits stream
  let column : Compact.ColumnIndex := ⟨stream.binding.name, stream.binding.nullable, ⟨0, 0⟩⟩
  let pages ← stream.batches.zipIdx.mapM fun (batch, index) =>
    planPage limits.leaf stream.binding batch index
  let dataStop := 4 + (pages.map PagePlan.size).sum
  let fileLimit := min limits.maxFileBytes (2^63 - 1)
  if dataStop + 8 > fileLimit then throw .fileLimit
  let footerCap := min (min limits.snapshot.footer.maxFooterBytes (2^32 - 1)) (fileLimit - dataStop - 8)
  let footer ← (Compact.encodeGroupsFor 2 (leaf source.descriptor) footerCap [column]
    (groupIndices column 4 pages)).mapError .footer
  if footer.length > footerCap then throw .extent
  let encoded ← pages.mapM (emitPage stream.binding.nullable)
  let data := Bytes.ofList (encoded.flatMap Bytes.toList)
  let prefixBytes := (Footer.magic.append data).append footer
  return (prefixBytes.append (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic

def counts {kind : Silmaril.Numeric.Timestamp.Kind} {unit : Silmaril.Numeric.Timestamp.TickUnit}
    (slots : List (Option (Ticks kind unit))) : List (Option Int) :=
  slots.map (Option.map Ticks.ticks)

def ReadbackMatches (source : Source) (bound : Leaf.Bound) (groups : List (Leaf.Slots bound)) : Prop :=
  bound.binding.leaf.name = source.stream.binding.name ∧
    bound.binding.leaf.repetition = some (if source.stream.binding.nullable then .optional else .required) ∧
    bound.binding.descriptor.unit = source.descriptor.unit ∧
    bound.binding.descriptor.isAdjustedToUTC = source.descriptor.isAdjustedToUTC ∧
    bound.snapshot.groupCount = source.stream.batches.length ∧
    bound.snapshot.metadata.numRows = totalRows source.stream ∧
    groups.map counts = source.stream.batches.map counts

instance (source : Source) (bound : Leaf.Bound) (groups : List (Leaf.Slots bound)) :
    Decidable (ReadbackMatches source bound groups) := by
  unfold ReadbackMatches
  infer_instance

def readGroups (limits : Leaf.Limits) (bound : Leaf.Bound) : Except Error (List (Leaf.Slots bound)) :=
  (List.range bound.snapshot.groupCount).mapM fun index =>
    (Leaf.readGroup limits bound index).mapError (.groupReadback index)

/-- Check an additional property of the same retained readback binding. -/
def certifyWith (admit : Leaf.Bound → Bool) (limits : Limits) (source : Source) (wire : Bytes) :
    Except Error Unit := do
  let bound ← (Leaf.openLeaf limits.snapshot wire 1).mapError .openReadback
  let groups ← readGroups limits.leaf bound
  if admit bound = true ∧ ReadbackMatches source bound groups then return () else throw .readbackMismatch

def certify (limits : Limits) (source : Source) (wire : Bytes) : Except Error Unit :=
  certifyWith (fun _ => true) limits source wire

end Internal

/-- Return the file only after the checked Parquet reader recovers the exact
descriptor and one complete group per original record batch. -/
def convert (ipc : Arrow.Limits) (limits : Limits) (input : KBytes) : Except Error Bytes := do
  let source ← readSource ipc limits input
  let wire ← Internal.serialize limits source
  Internal.certify limits source wire
  return wire

end Silmaril.Formats.Parquet.Timestamp.FromIpc
