module

public import Silmaril.Formats.Arrow.MetadataWriter.Defs
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Prelude.Bytes.Thms
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.MetadataWriter

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.MetadataWriter Wire

private theorem append_length (a b : KBytes) : (a ++ b).len = a.len + b.len := rfl

private theorem zeros_length (n : Nat) : (KBytes.zeros n).len = n := rfl

private theorem pad_wf {bytes : KBytes} (wf : bytes.wf = true) : (pad bytes).wf = true :=
  KBytes.wf_append wf rfl

private theorem vectorLength (slot start : Nat) (fields : List KBytes) :
    (fieldOffsets slot start fields).length = fields.length := by
  induction fields generalizing slot start with
  | nil => rfl
  | cons field rest ih => simp [fieldOffsets, ih]

private theorem field_wf (field : Field) : (fieldBytes field).wf = true := by
  obtain ⟨name, nullable, type⟩ := field
  cases type <;> apply pad_wf <;>
    simp only [words] <;>
    repeat first | exact Writer.emitWords_wf _ _ | apply KBytes.wf_append | rfl

private theorem field_size (field : Field) :
    (fieldBytes field).len = (53 + field.name.utf8ByteSize) +
      Writer.padding (53 + field.name.utf8ByteSize) := by
  obtain ⟨name, nullable, type⟩ := field
  have size : name.toByteArray.data.toList.length = name.utf8ByteSize := rfl
  cases type <;>
    simp only [fieldBytes, fieldFragment, pad, words, Writer.emitWords_length, append_length, zeros_length,
      List.length_cons, List.length_nil, List.length_map, size]
  all_goals
    have count : 4 * 7 + (4 * 5 + (4 * 1 + (1 * name.utf8ByteSize + 1))) =
        53 + name.utf8ByteSize := by omega
    rw [count]

private theorem objects_wf (fields : List Field) :
    ((fields.map fieldBytes).foldr (· ++ ·) KBytes.empty).wf = true := by
  induction fields with
  | nil => rfl
  | cons field rest ih => exact KBytes.wf_append (field_wf field) ih

private theorem objects_size (fields : List Field) :
    ((fields.map fieldBytes).foldr (· ++ ·) KBytes.empty).len =
      (fields.map fun field => let size := 53 + field.name.utf8ByteSize
                              size + Writer.padding size).sum := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    change (fieldBytes field ++ _).len = _ + _
    rw [append_length, field_size, ih]
    rfl

private theorem pair_length {α : Type} (values : List α) (first second : α → Nat) :
    (values.flatMap (fun item => [first item, second item])).length = 2 * values.length := by
  induction values with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons, ih]
    omega

theorem schemaPayload_wf (fields : List Field) : (schemaPayload fields).wf = true :=
  KBytes.wf_append (Writer.emitWords_wf _ _) (KBytes.wf_append rfl (objects_wf fields))

private theorem schema_wf (fields : List Field) (bodyLength : Nat) :
    (schemaBytes fields bodyLength).wf = true :=
  KBytes.wf_append (KBytes.wf_append (Writer.emitWords_wf _ _) (Writer.emitWords_wf _ _))
    (schemaPayload_wf fields)

private theorem batch_wf (batch : RecordBatch) (bodyLength : Nat) :
    (batchBytes batch bodyLength).wf = true := by
  unfold batchBytes messagePrefix words longs
  repeat first | exact Writer.emitWords_wf _ _ | apply KBytes.wf_append

theorem schemaPayload_size (fields : List Field) :
    (schemaPayload fields).len = schemaPayloadSize fields := by
  simp only [schemaPayload, schemaPayloadOf, schemaPayloadSize, words, Writer.emitWords_length,
    append_length, zeros_length, List.length_cons, vectorLength, List.length_map, objects_size]
  omega

private theorem schema_size (fields : List Field) (bodyLength : Nat) :
    (schemaBytes fields bodyLength).len = wireSize ⟨.schema fields, bodyLength⟩ := by
  simp only [schemaBytes, messagePrefix, wireSize, words, longs, Writer.emitWords_length,
    append_length, List.length_cons, List.length_nil, schemaPayload_size]

private theorem batch_size (batch : RecordBatch) (bodyLength : Nat) :
    (batchBytes batch bodyLength).len = wireSize ⟨.recordBatch batch, bodyLength⟩ := by
  simp only [batchBytes, messagePrefix, wireSize, batchSize, words, longs, Writer.emitWords_length,
    append_length, List.length_cons, List.length_nil, pair_length]
  omega

theorem schemaPayload_aligned (fields : List Field) : schemaPayloadSize fields % 8 = 0 := by
  have tail : ((fields.map fun field =>
      let size := 53 + field.name.utf8ByteSize
      size + Writer.padding size).sum) % 8 = 0 := by
    induction fields with
    | nil => rfl
    | cons field rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have aligned := Writer.padding_aligned (53 + field.name.utf8ByteSize)
      rw [Nat.add_mod, aligned, ih]
  have vector := Writer.padding_aligned (20 + fields.length * 4)
  simp only [schemaPayloadSize]
  rw [Nat.add_mod, vector, tail]

theorem wireSize_aligned (message : Message) : 0 < wireSize message ∧ wireSize message % 8 = 0 := by
  obtain ⟨header, bodyLength⟩ := message
  cases header with
  | schema fields =>
    simp only [wireSize]
    have aligned := schemaPayload_aligned fields
    omega
  | recordBatch batch =>
    simp only [wireSize, batchSize]
    omega

theorem serialize_extent {limits : Limits} {message : Message} {bytes : KBytes}
    (written : serialize limits message = .ok bytes) :
    bytes.wf = true ∧ bytes.len = wireSize message ∧ bytes.len < 2^31 ∧
      bytes.len ≤ limits.metadataBytes := by
  cases checked : checkDomain limits message with
  | error error => simp [serialize, checked] at written
  | ok success =>
    cases success
    simp only [serialize, checked] at written
    split at written <;> try contradiction
    split at written <;> try contradiction
    cases written
    obtain ⟨header, bodyLength⟩ := message
    cases header with
    | schema fields =>
      simp only [encode, schema_size]
      exact ⟨schema_wf _ _, trivial, by omega, by omega⟩
    | recordBatch batch =>
      simp only [encode, batch_size]
      exact ⟨batch_wf _ _, trivial, by omega, by omega⟩

theorem emit_exact {limits : Limits} {message : Message} {bytes : KBytes}
    (written : emit limits message = .ok bytes) :
    readMessage limits (bytes.slice 0 bytes.len) = .ok message ∧ bytes.wf = true ∧
      bytes.len = wireSize message ∧ 0 < bytes.len ∧ bytes.len < 2^31 ∧
      bytes.len % 8 = 0 ∧ bytes.len ≤ limits.metadataBytes := by
  cases raw : serialize limits message with
  | error e => simp [emit, raw, bind, Except.bind] at written
  | ok data =>
    cases decoded : readMessage limits (data.slice 0 data.len) with
    | error e => simp [emit, raw, decoded, bind, Except.bind] at written
    | ok result =>
      simp [emit, raw, decoded, bind, Except.bind, pure, Except.pure] at written
      split at written <;> try contradiction
      · rename_i same
        subst result
        cases written
        obtain ⟨wf, len, signedSize, budget⟩ := serialize_extent raw
        obtain ⟨positive, aligned⟩ := wireSize_aligned message
        exact ⟨decoded, wf, len, len ▸ positive, signedSize, len ▸ aligned, budget⟩

end Silmaril.Proofs.Formats.Arrow.MetadataWriter
