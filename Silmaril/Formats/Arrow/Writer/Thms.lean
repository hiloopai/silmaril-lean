module

public import Silmaril.Formats.Arrow.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.Writer.Bitmap
import Silmaril.Proofs.Formats.Arrow.Writer.Buffers
import Silmaril.Proofs.Formats.Arrow.Writer.RoundTrip

@[expose] public section

namespace Silmaril.Formats.Arrow.Writer

theorem emitWords_wf (width : Nat) (words : List Nat) : (emitWords width words).wf = true :=
  Proofs.Formats.Arrow.Writer.emitWords_wf width words

theorem emitWords_length (width : Nat) (words : List Nat) :
    (emitWords width words).len = width * words.length :=
  Proofs.Formats.Arrow.Writer.emitWords_length width words

theorem readLE_emitWords (width : Nat) (words : List Nat) (index : Nat)
    (bound : index < words.length) :
    (emitWords width words).readLE (width * index) width =
      some (words[index] % 256^width) :=
  Proofs.Formats.Arrow.Writer.readLE_emitWords width words index bound

theorem emitBytes_bytes (bytes : List UInt8) :
    (emitWords 1 (bytes.map UInt8.toNat)).toList = bytes :=
  Proofs.Formats.Arrow.Writer.emitBytes_bytes bytes

theorem emitBitmap_length {α : Type} (slots : List (Option α)) :
    (emitBitmap slots).len = (slots.length + 7) / 8 :=
  Proofs.Formats.Arrow.Writer.emitBitmap_length slots

theorem emitBitmap_valid {α : Type} (slots : List (Option α)) (index : Nat)
    (bound : index < slots.length) :
    Body.validAt (emitBitmap slots) index = some slots[index].isSome :=
  Proofs.Formats.Arrow.Writer.emitBitmap_valid slots index bound

theorem padding_aligned (size : Nat) : (size + padding size) % 8 = 0 :=
  Proofs.Formats.Arrow.Writer.padding_aligned size

/-- The writer checks the declared shape, signed offset domain and budgets. -/
theorem checkInput_iff (limits : ObservationLimits) (input : BatchInput) :
    checkInput limits input = .ok () ↔ Admitted limits input :=
  Proofs.Formats.Arrow.Writer.checkInput_iff limits input

/-- Aligned packing keeps exact payload windows in descriptor order. -/
theorem packBuffers_exact (pieces : List KBytes) (wf : ∀ piece ∈ pieces, piece.wf = true) :
    PackedWire (packBuffers 0 pieces).2.toList 0 pieces (packBuffers 0 pieces).1 := by
  simpa only [List.nil_append, List.length_nil] using
    Proofs.Formats.Arrow.Writer.packBuffers_exact [] pieces wf

theorem packBuffers_length (offset : Nat) (pieces : List KBytes) :
    (packBuffers offset pieces).2.len = (pieces.map fun piece => piece.len + padding piece.len).sum :=
  Proofs.Formats.Arrow.Writer.packBuffers_length offset pieces

theorem packBuffers_aligned (offset : Nat) (pieces : List KBytes) :
    (packBuffers offset pieces).2.len % 8 = 0 :=
  Proofs.Formats.Arrow.Writer.packBuffers_aligned offset pieces

theorem packBuffers_count (offset : Nat) (pieces : List KBytes) :
    (packBuffers offset pieces).1.length = pieces.length :=
  Proofs.Formats.Arrow.Writer.packBuffers_count offset pieces

/-- Every admitted batch is writable. Reading its aligned physical buffers
gives the original ordered observation and preserves the explicit row count. -/
theorem emitBatch_of_admitted (limits : ObservationLimits) (input : BatchInput)
    (allowed : Admitted limits input) :
    ∃ frame, emitBatch limits input = .ok frame ∧ frame.metadata.rowCount = input.rowCount ∧
      frame.body.len % 8 = 0 ∧ decodeBatch limits frame = .ok input.observe :=
  Proofs.Formats.Arrow.Writer.emitBatch_of_admitted limits input allowed

theorem emitBatch_roundtrip {limits : ObservationLimits} {input : BatchInput}
    {frame : BatchFrame input.fields} (written : emitBatch limits input = .ok frame) :
    frame.metadata.rowCount = input.rowCount ∧ frame.body.len % 8 = 0 ∧
      decodeBatch limits frame = .ok input.observe :=
  Proofs.Formats.Arrow.Writer.emitBatch_roundtrip written

end Silmaril.Formats.Arrow.Writer
