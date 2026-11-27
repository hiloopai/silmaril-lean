module

public import Silmaril.Formats.Arrow.FileWriter.Defs
public import Silmaril.Formats.Arrow.MixedFlat.File.Defs
public import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs

/-! Checked V5 files using the ordered mixed record writer. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.FileWriter

open OrderedWriter (BatchInput)

inductive Error where
  | ipc (cause : Arrow.Error)
  | schema (cause : OrderedWriter.Error)
  | record (index : Nat) (cause : OrderedWriter.RecordError)
  | footer (cause : Arrow.Error)
  | readback (cause : MixedFlat.File.Error)
  | indexMismatch
  | valuesMismatch
  deriving DecidableEq, Repr

def observe (batch : MixedFlat.Observed) : StreamWriter.BatchObservation :=
  (batch.rowCount, Writer.observeColumns batch.columns)

/-- The strict mixed file writer admits all four flat kinds represented
by the ordered column encoder. -/
def supported (fields : List Field) : Bool :=
  fields.all fun field =>
    match field.kind with
    | .primitive .int32 | .primitive .utf8 | .view _ => true

def emitRecord (limits : MixedFlat.Limits) (fields : List Field) (batch : BatchInput) (index : Nat) :
    Except Error Arrow.FileWriter.RecordFrame := do
  if batch.fields ≠ fields then throw (.record index .schemaMismatch)
  let record ← (OrderedWriter.emitRecordWith limits batch supported).mapError (.record index)
  let frame := record.output
  let metadataSize := frame.metadataBytes.len
  let bytes := Arrow.StreamWriter.envelopeBytes metadataSize ++ (frame.metadataBytes ++ frame.body)
  return ⟨bytes, 8 + metadataSize, frame.body.len⟩

/-- The same ordered schema fragments are used in the embedded Message
and in the File.fbs footer. Check the trailer and block word domains. -/
def emitFooter (ipc : Arrow.Limits) (footer : MixedFlat.FileFooter) : Except Arrow.Error KBytes := do
  if footer.fields.length > ipc.fields then throw (.limit .fields)
  if footer.blocks.length > ipc.batches then throw (.limit .batches)
  let size := 40 + 24 * footer.blocks.length + (OrderedWriter.Wire.schemaSize footer.fields - 48)
  if size ≥ 2^31 then throw (.malformed .metadataLength)
  if size > ipc.metadataBytes then throw (.limit .metadataBytes)
  if footer.blocks.any
      (fun block => block.offset ≥ 2^63 || block.metadataLength ≥ 2^31 || block.bodyLength ≥ 2^63) then
    throw (.malformed .batchLayout)
  let schema := MetadataWriter.Wire.schemaPayloadOf (footer.fields.map OrderedWriter.Wire.fieldBytes)
  return FooterWriter.encodeWithSchema footer.blocks schema

structure Assembly where
  bytes : KBytes
  footer : MixedFlat.FileFooter
  schemaEnd : Nat
  footerStart : Nat
  footerLength : Nat

def assemble (limits : MixedFlat.Limits) (fields : List Field) (batches : List BatchInput) :
    Except Error Assembly := do
  let ipc := limits.observation.ipc
  if batches.length > ipc.batches then throw (.ipc (.limit .batches))
  (Body.checkBudget limits.observation fields.length (batches.map (·.rowCount)).sum).mapError .ipc
  let schema ← (OrderedWriter.emitSchemaWith ipc fields supported).mapError .schema
  let records ← batches.zipIdx.mapM fun (batch, index) => emitRecord limits fields batch index
  let schemaEnd := 8 + schema.len
  let (blocks, body) := Arrow.FileWriter.packRecords schemaEnd records
  let footer : MixedFlat.FileFooter := ⟨fields, blocks⟩
  let footerBytes ← (emitFooter ipc footer).mapError .footer
  let trailer := KBytes.leaf 4 footerBytes.len ++ KBytes.leaf 6 FileReader.magic
  return ⟨KBytes.leaf 8 FileReader.magic ++ (schema ++ (body ++ (footerBytes ++ trailer))),
    footer, schemaEnd, schemaEnd + body.len, footerBytes.len⟩

/-- Read each checked original block in footer order. A failed read retains
the footer ordinal and the nested file record cause. -/
def readback (limits : MixedFlat.Limits) (wire : KBytes) (footer : MixedFlat.FileFooter) :
    Except MixedFlat.File.Error (List MixedFlat.Observed) :=
  footer.blocks.zipIdx.mapM fun (block, index) =>
    (MixedFlat.File.readRecord limits wire footer.fields block).mapError (.batch index)

/-- Emit a strict file and certify the exact footer, boundary offsets and
ordered nullable values through the existing mixed reader. -/
def emit (limits : MixedFlat.Limits) (fields : List Field) (batches : List BatchInput) :
    Except Error KBytes := do
  let plan ← assemble limits fields batches
  let index ← (MixedFlat.File.readIndex limits.observation.ipc plan.bytes).mapError .readback
  if index.footer ≠ plan.footer ∨ 16 + index.schemaSize ≠ plan.schemaEnd ∨
      index.span.start ≠ plan.footerStart ∨ index.span.length ≠ plan.footerLength then
    throw .indexMismatch
  let observed ← (readback limits plan.bytes index.footer).mapError .readback
  if observed.map observe ≠ batches.map BatchInput.observe then throw .valuesMismatch
  return plan.bytes

end Silmaril.Formats.Arrow.MixedFlat.FileWriter
