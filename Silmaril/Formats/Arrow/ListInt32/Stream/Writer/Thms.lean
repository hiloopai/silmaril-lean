module

public import Silmaril.Formats.Arrow.ListInt32.Stream.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.ListInt32.Stream.Writer.Correctness

public section

namespace Silmaril.Formats.Arrow.ListInt32.Stream.Writer

/-- Preflight counts the actual padded Schema metadata, including both UTF-8 names. -/
theorem schema_size (field : ListInt32.Field) : (Wire.schema field).len = Wire.schemaSize field :=
  Proofs.Formats.Arrow.ListInt32.Stream.Writer.schema_size field

/-- The flattened physical child has the exact sum of the present list lengths. -/
theorem childSlots_length (rows : List Row) : (childSlots rows).length = childCount rows :=
  Proofs.Formats.Arrow.ListInt32.Stream.Writer.childSlots_length rows

/-- Each offset is the sum of the physical child lengths of the preceding rows. -/
theorem offsetWords_at {rows : List Row} {index : Nat} (h : index ≤ rows.length) :
    (offsetWords rows)[index]? = some (childCount (rows.take index)) :=
  Proofs.Formats.Arrow.ListInt32.Stream.Writer.offsetWords_at h

/-- The offset vector includes zero and the final child extent, even with no rows. -/
theorem offsetWords_length (rows : List Row) : (offsetWords rows).length = rows.length + 1 :=
  Proofs.Formats.Arrow.ListInt32.Stream.Writer.offsetWords_length rows

/-- The four logical buffer lengths precede all padding. -/
theorem parts_sizes (rows : List Row) :
    (parts rows).map KBytes.len = sizes rows.length (childCount rows) :=
  Proofs.Formats.Arrow.ListInt32.Stream.Writer.parts_sizes rows

/-- Aligned packing emits four ordered descriptors with exact original buffer bytes and padded size. -/
theorem pack_exact (rows : List Row) :
    let packed := Arrow.Writer.packBuffers 0 (parts rows)
    packed.1.length = 4 ∧ packed.2.len = bodySize rows.length (childCount rows) ∧
      Arrow.Writer.PackedWire packed.2.toList 0 (parts rows) packed.1 :=
  Proofs.Formats.Arrow.ListInt32.Stream.Writer.pack_exact rows

/-- Preflight enforces signed wire domains and the record limits before materialization. -/
theorem checkRecord_counts {ipc : Arrow.Limits} {rows children : Nat}
    (checked : checkRecord ipc rows children = .ok ()) :
    2 ≤ ipc.fields ∧ rows ≤ ipc.rows ∧ rows < 2^63 ∧ children < 2^31 ∧
      bodySize rows children < 2^63 ∧ bodySize rows children ≤ ipc.bodyBytes ∧ 200 ≤ ipc.metadataBytes :=
  Proofs.Formats.Arrow.ListInt32.Stream.Writer.checkRecord_counts checked

/-- The original parent and child lengths and null counts govern the record metadata. -/
theorem metadata_exact (rows : List Row) (buffers : List Buffer) :
    (metadata rows buffers).rowCount = rows.length ∧
      (metadata rows buffers).nodes = [⟨rows.length, rows.countP Option.isNone⟩,
        ⟨childCount rows, (childSlots rows).countP Option.isNone⟩] ∧
      (metadata rows buffers).buffers = buffers :=
  Proofs.Formats.Arrow.ListInt32.Stream.Writer.metadata_exact rows buffers

/-- Every offset fits the nonnegative signed-32 wire domain after preflight. -/
theorem offsetWords_signed {ipc : Arrow.Limits} {rows : List Row} {index : Nat}
    (checked : checkRecord ipc rows.length (childCount rows) = .ok ())
    (indexBound : index ≤ rows.length) :
    ∃ offset, (offsetWords rows)[index]? = some offset ∧ offset < 2^31 :=
  Proofs.Formats.Arrow.ListInt32.Stream.Writer.offsetWords_signed checked indexBound

/-- The emitted frame reads back to its exact original metadata and packed body bytes. -/
theorem emitRecord_exact {ipc : Arrow.Limits} {rows : List Row} {frame : KBytes}
    (h : emitRecord ipc rows = .ok frame) :
    let packed := Arrow.Writer.packBuffers 0 (parts rows)
    let message : Message := ⟨.recordBatch (metadata rows packed.1), packed.2.len⟩
    frame.wf = true ∧ frame.len = 8 + 200 + bodySize rows.length (childCount rows) ∧
      readEnvelope ipc frame 0 = .ok (.metadata 200) ∧
      readMessage ipc (frame.slice 8 200) = .ok message ∧
      ∃ body, readBody ipc frame (8 + 200) message.bodyLength = .ok body ∧
        body.toList = packed.2.toList ∧ Arrow.Writer.PackedWire body.toList 0 (parts rows) packed.1 :=
  Proofs.Formats.Arrow.ListInt32.Stream.Writer.emitRecord_exact h

/-- A successful stream is the Schema followed by the requested record frames and exact EOS. -/
theorem emit_wire {limits : Stream.Limits} {field : ListInt32.Field}
    {batches : List (List Row)} {wire : KBytes} (h : emit limits field batches = .ok wire) :
    ∃ schema records,
      emitSchema limits.ipc field = .ok schema ∧
      (batches.zipIdx.mapM fun (rows, index) => (emitRecord limits.ipc rows).mapError (Error.record index)) =
        .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) StreamWriter.eos :=
  Proofs.Formats.Arrow.ListInt32.Stream.Writer.emit_wire h

/-- The checked reader recovers the exact schema, ordered batches and child totals through EOS. -/
theorem emit_readback {limits : Stream.Limits} {field : ListInt32.Field}
    {batches : List (List Row)} {wire : KBytes} (h : emit limits field batches = .ok wire) :
    ∃ decoded size, Stream.read limits wire = .ok decoded ∧
      Agrees field batches decoded ∧ wire.wf = true ∧
      readEnvelope limits.ipc wire 0 = .ok (.metadata size) ∧
      ListInt32.readSchema limits.ipc (wire.slice 8 size) = .ok field ∧
      Stream.BatchesWire limits wire limits.ipc.batches 0 0 (8 + size) decoded.batches :=
  Proofs.Formats.Arrow.ListInt32.Stream.Writer.emit_readback h

/-- Checked native readback for the chosen LIST parent nullability. -/
theorem emitFor_readback {parentNullable : Bool} {limits : ListInt32.Stream.Limits} {field : ListInt32.Field}
    {batches : List (List Row)} {wire : KBytes} (h : emitFor parentNullable limits field batches = .ok wire) :
    ∃ decoded size, ListInt32.Stream.readFor parentNullable limits wire = .ok decoded ∧
      Agrees field batches decoded ∧ wire.wf = true ∧
      readEnvelope limits.ipc wire 0 = .ok (.metadata size) ∧
      ListInt32.readSchemaFor parentNullable limits.ipc (wire.slice 8 size) = .ok field ∧
      ListInt32.Stream.BatchesWire limits wire limits.ipc.batches 0 0 (8 + size) decoded.batches ∧
      ListInt32.Stream.checkParents parentNullable decoded.batches = .ok () :=
  Proofs.Formats.Arrow.ListInt32.Stream.Writer.emitFor_readback h

end Silmaril.Formats.Arrow.ListInt32.Stream.Writer
