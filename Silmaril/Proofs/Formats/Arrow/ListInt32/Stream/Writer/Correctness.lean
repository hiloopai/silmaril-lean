module

public import Silmaril.Formats.Arrow.ListInt32.Stream.Writer.Defs
import Silmaril.Formats.Arrow.ListInt32.Stream.Thms
import Silmaril.Formats.Arrow.StreamWriter.Thms
import Silmaril.Formats.Arrow.Writer.Thms
import Init.Data.List.Scan.Lemmas

public section

namespace Silmaril.Proofs.Formats.Arrow.ListInt32.Stream.Writer

open Silmaril.Formats
open Silmaril.Formats.Arrow hiding Row
open Silmaril.Formats.Arrow.ListInt32.Stream (Row)
open Silmaril.Formats.Arrow.ListInt32.Stream.Writer
open Silmaril.Formats.Arrow.MetadataWriter.Wire

private theorem append_length (a b : KBytes) : (a ++ b).len = a.len + b.len := rfl
private theorem zeros_length (n : Nat) : (KBytes.zeros n).len = n := rfl

private theorem parentFragmentFor_size (parentNullable : Bool) (name : String) :
    (ListInt32.Stream.Writer.Wire.parentFragmentFor parentNullable name).len = ListInt32.Stream.Writer.Wire.parentSize name := by
  have nameSize : name.toByteArray.data.toList.length = name.utf8ByteSize := rfl
  simp only [ListInt32.Stream.Writer.Wire.parentFragmentFor, ListInt32.Stream.Writer.Wire.parentSize, pad, words, Arrow.Writer.emitWords_length,
    append_length, zeros_length, List.length_cons, List.length_nil, List.length_map, nameSize]
  have size : 4 * 14 + (1 * name.utf8ByteSize + 1) = 57 + name.utf8ByteSize := by omega
  rw [size]

private theorem schemaFor_size (parentNullable : Bool) (field : ListInt32.Field) :
    (ListInt32.Stream.Writer.Wire.schemaFor parentNullable field).len = ListInt32.Stream.Writer.Wire.schemaSize field := by
  have nameSize : field.childName.toByteArray.data.toList.length = field.childName.utf8ByteSize := rfl
  simp only [ListInt32.Stream.Writer.Wire.schemaFor, ListInt32.Stream.Writer.Wire.schemaSize, ListInt32.Stream.Writer.Wire.childField, messagePrefix, fieldBytes, fieldFragment,
    parentFragmentFor_size, pad, words, longs, Arrow.Writer.emitWords_length, append_length, zeros_length,
    List.length_cons, List.length_nil, List.length_map, nameSize]
  have size : 4 * 7 + (4 * 5 + (4 * 1 + (1 * field.childName.utf8ByteSize + 1))) =
      53 + field.childName.utf8ByteSize := by omega
  rw [size]
  omega

public theorem schema_size (field : ListInt32.Field) :
    (ListInt32.Stream.Writer.Wire.schema field).len = ListInt32.Stream.Writer.Wire.schemaSize field :=
  schemaFor_size true field

public theorem childSlots_length (rows : List Row) : (childSlots rows).length = childCount rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [childSlots, childCount, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at *
    rw [ih]

private theorem count_fold (rows : List Row) (start : Nat) :
    rows.foldl (fun offset row => offset + (row.getD []).length) start = start + childCount rows := by
  induction rows generalizing start with
  | nil => simp [childCount]
  | cons row rest ih =>
    simp only [List.foldl_cons, ih, childCount, List.map_cons, List.sum_cons]
    omega

/-- Offset i is the total physical child length of precisely the preceding rows. -/
public theorem offsetWords_at {rows : List Row} {index : Nat} (h : index ≤ rows.length) :
    (offsetWords rows)[index]? = some (childCount (rows.take index)) := by
  simp [offsetWords, List.getElem?_scanl, h, count_fold]

public theorem offsetWords_length (rows : List Row) : (offsetWords rows).length = rows.length + 1 := by
  simp [offsetWords]

private theorem int32_parts (rows : List Row) :
    (Arrow.Writer.ColumnValues.int32 (childSlots rows)).emit =
      [Arrow.Writer.emitBitmap (childSlots rows),
        Arrow.Writer.emitWords 4 ((childSlots rows).map fun value => (value.getD 0).toUInt32.toNat)] := by
  rfl

public theorem parts_sizes (rows : List Row) :
    (parts rows).map KBytes.len = sizes rows.length (childCount rows) := by
  simp [parts, int32_parts, sizes, Arrow.Writer.emitBitmap_length, Arrow.Writer.emitWords_length,
    childSlots_length, offsetWords_length]

private theorem pieces_wf (rows : List Row) : ∀ part ∈ parts rows, part.wf = true := by
  intro part member
  simp only [parts, int32_parts, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp [Arrow.Writer.emitBitmap, Arrow.Writer.emitWords_wf]

private theorem packed_size (offset : Nat) (pieces : List KBytes) :
    (Arrow.Writer.packBuffers offset pieces).2.len =
      ((pieces.map KBytes.len).map fun size => size + Arrow.Writer.padding size).sum := by
  induction pieces generalizing offset with
  | nil => rfl
  | cons first rest ih =>
    simp only [Arrow.Writer.packBuffers, append_length, zeros_length, List.map_cons, List.sum_cons]
    rw [ih]
    omega

public theorem pack_exact (rows : List Row) :
    let packed := Arrow.Writer.packBuffers 0 (parts rows)
    packed.1.length = 4 ∧ packed.2.len = bodySize rows.length (childCount rows) ∧
      Arrow.Writer.PackedWire packed.2.toList 0 (parts rows) packed.1 := by
  refine ⟨?_, ?_, Arrow.Writer.packBuffers_exact _ (pieces_wf rows)⟩
  · simp [parts, int32_parts, Arrow.Writer.packBuffers]
  · rw [packed_size, parts_sizes, bodySize]

public theorem checkRecord_counts {ipc : Arrow.Limits} {rows children : Nat}
    (checked : checkRecord ipc rows children = .ok ()) :
    2 ≤ ipc.fields ∧ rows ≤ ipc.rows ∧ rows < 2^63 ∧ children < 2^31 ∧
      bodySize rows children < 2^63 ∧ bodySize rows children ≤ ipc.bodyBytes ∧ 200 ≤ ipc.metadataBytes := by
  unfold checkRecord at checked
  split at checked
  · contradiction
  rename_i fields
  split at checked
  · contradiction
  rename_i rowLimit
  split at checked
  · contradiction
  rename_i rowRange
  split at checked
  · contradiction
  rename_i childRange
  dsimp only at checked
  split at checked
  · contradiction
  rename_i bodyRange
  split at checked
  · contradiction
  rename_i bodyLimit
  split at checked
  · contradiction
  rename_i metadataLimit
  omega

public theorem metadata_exact (rows : List Row) (buffers : List Buffer) :
    (metadata rows buffers).rowCount = rows.length ∧
      (metadata rows buffers).nodes = [⟨rows.length, rows.countP Option.isNone⟩,
        ⟨childCount rows, (childSlots rows).countP Option.isNone⟩] ∧
      (metadata rows buffers).buffers = buffers := by
  simp [metadata, childSlots_length]

public theorem offsetWords_signed {ipc : Arrow.Limits} {rows : List Row} {index : Nat}
    (checked : checkRecord ipc rows.length (childCount rows) = .ok ())
    (indexBound : index ≤ rows.length) :
    ∃ offset, (offsetWords rows)[index]? = some offset ∧ offset < 2^31 := by
  have partition : childCount ((rows.take index) ++ rows.drop index) =
      childCount (rows.take index) + childCount (rows.drop index) := by
    simp only [childCount, List.map_append, List.sum_append]
  rw [List.take_append_drop] at partition
  have bound := (checkRecord_counts checked).2.2.2.1
  exact ⟨_, offsetWords_at indexBound, by omega⟩

private theorem record_source {ipc : Arrow.Limits} {rows : List Row} {frame : KBytes}
    (h : emitRecord ipc rows = .ok frame) :
    let packed := Arrow.Writer.packBuffers 0 (parts rows)
    checkRecord ipc rows.length (childCount rows) = .ok () ∧
      StreamWriter.emitFrame ipc ⟨.recordBatch (metadata rows packed.1), packed.2.len⟩ packed.2 = .ok frame := by
  unfold emitRecord at h
  cases checked : checkRecord ipc rows.length (childCount rows) with
  | error e => simp [checked, Bind.bind, Except.bind] at h
  | ok result =>
    cases result
    simp only [checked, Bind.bind, Except.bind] at h
    change (StreamWriter.emitFrame ipc
      ⟨.recordBatch (metadata rows (Arrow.Writer.packBuffers 0 (parts rows)).1),
        (Arrow.Writer.packBuffers 0 (parts rows)).2.len⟩ (Arrow.Writer.packBuffers 0 (parts rows)).2).mapError
          RecordError.ipc = .ok frame at h
    simp only [Except.mapError] at h
    split at h
    · contradiction
    · rename_i previous emitted
      exact ⟨rfl, (Except.ok.inj h) ▸ emitted⟩

public theorem emitRecord_exact {ipc : Arrow.Limits} {rows : List Row} {frame : KBytes}
    (h : emitRecord ipc rows = .ok frame) :
    let packed := Arrow.Writer.packBuffers 0 (parts rows)
    let message : Message := ⟨.recordBatch (metadata rows packed.1), packed.2.len⟩
    frame.wf = true ∧ frame.len = 8 + 200 + bodySize rows.length (childCount rows) ∧
      readEnvelope ipc frame 0 = .ok (.metadata 200) ∧
      readMessage ipc (frame.slice 8 200) = .ok message ∧
      ∃ body, readBody ipc frame (8 + 200) message.bodyLength = .ok body ∧
        body.toList = packed.2.toList ∧ Arrow.Writer.PackedWire body.toList 0 (parts rows) packed.1 := by
  have emitted := (record_source h).2
  obtain ⟨shape, bodyLen, pack⟩ := pack_exact rows
  have size :
      MetadataWriter.wireSize ⟨.recordBatch (metadata rows (Arrow.Writer.packBuffers 0 (parts rows)).1),
        (Arrow.Writer.packBuffers 0 (parts rows)).2.len⟩ = 200 := by
    simp [MetadataWriter.wireSize, MetadataWriter.Wire.batchSize, metadata, shape]
  have exactFrame := StreamWriter.emitFrame_exact emitted
  dsimp only at exactFrame
  rw [size] at exactFrame
  obtain ⟨wf, extent, envelope, parsed, body, slice, same⟩ := exactFrame
  refine ⟨wf, extent.trans (congrArg (208 + ·) bodyLen), envelope, parsed, body, slice, same, ?_⟩
  rwa [same]

private theorem emitFor_checked {parentNullable : Bool} {limits : ListInt32.Stream.Limits} {field : ListInt32.Field}
    {batches : List (List Row)} {wire : KBytes} (h : emitFor parentNullable limits field batches = .ok wire) :
    serializeFor parentNullable limits field batches = .ok wire ∧
      ∃ decoded, ListInt32.Stream.readFor parentNullable limits wire = .ok decoded ∧ Agrees field batches decoded := by
  unfold emitFor at h
  cases encoded : serializeFor parentNullable limits field batches with
  | error e => simp [encoded, Bind.bind, Except.bind] at h
  | ok bytes =>
    simp only [encoded, Bind.bind, Except.bind, Except.mapError] at h
    cases parsed : ListInt32.Stream.readFor parentNullable limits bytes with
    | error e => simp [parsed] at h
    | ok decoded =>
      simp only [parsed] at h
      split at h
      · rename_i agrees
        obtain rfl := Except.ok.inj h
        exact ⟨rfl, decoded, parsed, agrees⟩
      · contradiction

private theorem serialize_wire {limits : ListInt32.Stream.Limits} {field : ListInt32.Field}
    {batches : List (List Row)} {wire : KBytes} (h : serialize limits field batches = .ok wire) :
    ∃ schema records,
      emitSchema limits.ipc field = .ok schema ∧
      (batches.zipIdx.mapM fun (rows, index) => (emitRecord limits.ipc rows).mapError (ListInt32.Stream.Writer.Error.record index)) =
        .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) StreamWriter.eos := by
  unfold serialize serializeFor at h
  split at h
  · contradiction
  split at h
  · contradiction
  split at h
  · contradiction
  simp only [Bind.bind, Except.bind] at h
  cases schema : emitSchemaFor true limits.ipc field with
  | error e => simp [schema] at h
  | ok bytes =>
    simp only [schema] at h
    cases records : batches.zipIdx.mapM
        (fun (rows, index) => (emitRecord limits.ipc rows).mapError (ListInt32.Stream.Writer.Error.record index)) with
    | error e => simp [records] at h
    | ok frames =>
      simp only [records] at h
      exact ⟨bytes, frames, schema, rfl, (Except.ok.inj h).symm⟩

public theorem emit_wire {limits : ListInt32.Stream.Limits} {field : ListInt32.Field}
    {batches : List (List Row)} {wire : KBytes} (h : emit limits field batches = .ok wire) :
    ∃ schema records,
      emitSchema limits.ipc field = .ok schema ∧
      (batches.zipIdx.mapM fun (rows, index) => (emitRecord limits.ipc rows).mapError (ListInt32.Stream.Writer.Error.record index)) =
        .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) StreamWriter.eos :=
  serialize_wire (emitFor_checked h).1

public theorem emitFor_readback {parentNullable : Bool} {limits : ListInt32.Stream.Limits} {field : ListInt32.Field}
    {batches : List (List Row)} {wire : KBytes} (h : emitFor parentNullable limits field batches = .ok wire) :
    ∃ decoded size, ListInt32.Stream.readFor parentNullable limits wire = .ok decoded ∧
      Agrees field batches decoded ∧ wire.wf = true ∧
      readEnvelope limits.ipc wire 0 = .ok (.metadata size) ∧
      ListInt32.readSchemaFor parentNullable limits.ipc (wire.slice 8 size) = .ok field ∧
      ListInt32.Stream.BatchesWire limits wire limits.ipc.batches 0 0 (8 + size) decoded.batches ∧
      ListInt32.Stream.checkParents parentNullable decoded.batches = .ok () := by
  obtain ⟨decoded, parsed, agrees⟩ := (emitFor_checked h).2
  obtain ⟨wf, size, envelope, schema, records, parents⟩ := ListInt32.Stream.readFor_wire parsed
  exact ⟨decoded, size, parsed, agrees, wf, envelope, agrees.1 ▸ schema, records, parents⟩

public theorem emit_readback {limits : ListInt32.Stream.Limits} {field : ListInt32.Field}
    {batches : List (List Row)} {wire : KBytes} (h : emit limits field batches = .ok wire) :
    ∃ decoded size, ListInt32.Stream.read limits wire = .ok decoded ∧
      Agrees field batches decoded ∧ wire.wf = true ∧
      readEnvelope limits.ipc wire 0 = .ok (.metadata size) ∧
      ListInt32.readSchema limits.ipc (wire.slice 8 size) = .ok field ∧
      ListInt32.Stream.BatchesWire limits wire limits.ipc.batches 0 0 (8 + size) decoded.batches := by
  obtain ⟨decoded, size, native, agrees, wf, envelope, schema, records, _⟩ := emitFor_readback h
  exact ⟨decoded, size, native, agrees, wf, envelope, schema, records⟩

end Silmaril.Proofs.Formats.Arrow.ListInt32.Stream.Writer
