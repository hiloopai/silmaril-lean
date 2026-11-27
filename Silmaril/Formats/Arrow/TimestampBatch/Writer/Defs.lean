module

public import Silmaril.Formats.Arrow.TimestampBatch.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs

/-! Emit one TIMESTAMP record using the original exact signed payload codec. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.TimestampBatch.Writer

open Silmaril.Numeric.Timestamp (ConversionError Ticks)

inductive Error where
  | writer (reason : Arrow.Error)
  | requiredNull
  | payload (reason : ConversionError)
  deriving DecidableEq, Repr

def tickCounts {binding : Binding} (column : Column binding) : List (Option Int) :=
  column.map (Option.map Ticks.ticks)

/-- Encode one positional validity buffer and same-unit signed value buffer. -/
def encodeParts (binding : Binding) (slots : Column binding) :
    Except ConversionError (List KBytes) := do
  let values ← binding.metadata.encodeBufferLE (slots.map (·.getD ⟨0⟩))
  let payload := Arrow.Writer.emitWords 1 (values.data.toList.map UInt8.toNat)
  return [Arrow.Writer.emitBitmap slots, payload]

/-- Pack validity and same-unit Int64 values as one aligned record.
A null slot has a zero physical word and a clear validity bit. -/
def emitRecord (limits : Arrow.Limits) (binding : Binding)
    (slots : Column binding) : Except Error KBytes := do
  if limits.batches = 0 then throw (.writer (.limit .batches))
  if limits.rows < slots.length then throw (.writer (.limit .rows))
  if !binding.nullable && slots.any Option.isNone then throw .requiredNull
  let validitySize := (slots.length + 7) / 8
  if limits.bodyBytes < validitySize + Arrow.Writer.padding validitySize + 8 * slots.length then
    throw (.writer (.limit .bodyBytes))
  let pieces ← (encodeParts binding slots).mapError .payload
  let (buffers, body) := Arrow.Writer.packBuffers 0 pieces
  let node : FieldNode := ⟨slots.length, slots.countP Option.isNone⟩
  let message : Message := ⟨.recordBatch ⟨slots.length, [node], buffers⟩, body.len⟩
  (StreamWriter.emitFrame limits message body).mapError .writer

end Silmaril.Formats.Arrow.TimestampBatch.Writer
