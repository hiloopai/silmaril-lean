module

public import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Defs

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Timestamp

open Silmaril.Formats
open Silmaril.Formats.Arrow (Limits ObservationLimits RecordBatch readEnvelope readBody)
open Silmaril.Formats.Arrow.MixedFlat.Timestamp

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem unmap_error_ok {ε δ α : Type} {result : Except ε α} {wrap : ε → δ} {value : α}
    (accepted : result.mapError wrap = .ok value) : result = .ok value := by
  cases result <;> cases accepted
  rfl

theorem readSchema_wire {limits : Limits} {input : KBytes} {fields : List Field} {start : Nat}
    (read : readSchema limits input = .ok (fields, start)) :
    ∃ size original,
      readEnvelope limits input 0 = .ok (.metadata size) ∧
      Arrow.SchemaReader.readMessage limits (input.slice 8 size) = .ok original ∧ original.endianness = .little ∧
      (original.fields.zipIdx.mapM fun (field, position) => bindField field position) = .ok fields ∧
      start = 8 + size := by
  obtain ⟨envelope, admitted, read⟩ := bind_ok read
  cases envelope with
  | eos => contradiction
  | metadata size =>
    obtain ⟨original, normalized, read⟩ := bind_ok read
    split at read
    · contradiction
    · rename_i little
      obtain ⟨values, bound, read⟩ := bind_ok read
      cases Except.ok.inj read
      exact ⟨size, original, unmap_error_ok admitted, unmap_error_ok normalized,
        of_not_not little, bound, rfl⟩

theorem readParsed_wire {limits : ObservationLimits} {fields : List Field} {record : RecordBatch}
    {length : Nat} {body : KBytes} {batch : Batch}
    (read : readParsed limits fields record length body = .ok batch) :
    BatchWire limits fields record length body batch := by
  obtain ⟨plan, bound, read⟩ := bind_ok read
  obtain ⟨columns, decoded, read⟩ := bind_ok read
  cases Except.ok.inj read
  exact ⟨plan, unmap_error_ok bound, rfl, decoded⟩

private theorem readRecord_wire {limits : ObservationLimits} {input : KBytes} {fields : List Field}
    {rows offset size : Nat} {batch : Batch} {next : Nat}
    (read : readRecord limits input fields rows offset size = .ok (batch, next)) :
    ∃ record length body,
      Arrow.readMessage limits.ipc (input.slice (offset + 8) size) = .ok ⟨.recordBatch record, length⟩ ∧
      readBody limits.ipc input (offset + 8 + size) length = .ok body ∧
      Arrow.Body.checkBudget limits fields.length (rows + record.rowCount) = .ok () ∧
      BatchWire limits fields record length body batch ∧ next = offset + 8 + size + length := by
  obtain ⟨⟨header, length⟩, parsed, read⟩ := bind_ok read
  cases header with
  | schema => contradiction
  | recordBatch record =>
    obtain ⟨body, extent, read⟩ := bind_ok read
    obtain ⟨_, budget, read⟩ := bind_ok read
    obtain ⟨decoded, checked, read⟩ := bind_ok read
    cases Except.ok.inj read
    exact ⟨record, length, body, unmap_error_ok parsed, unmap_error_ok extent,
      unmap_error_ok budget, readParsed_wire checked, rfl⟩

theorem readBatches_wire {limits : ObservationLimits} {input : KBytes} {fields : List Field}
    {fuel index rows offset : Nat} {batches : List Batch}
    (read : readBatches limits input fields fuel index rows offset = .ok batches) :
    BatchesWire limits input fields fuel rows offset batches := by
  induction fuel generalizing index rows offset batches with
  | zero =>
    rw [readBatches] at read
    obtain ⟨envelope, planned, next⟩ := bind_ok read
    cases envelope with
    | metadata => contradiction
    | eos =>
      by_cases exactEnd : offset + 8 = input.len
      · have same : [] = batches := by simpa [exactEnd] using next
        cases same
        exact .eos (unmap_error_ok planned) exactEnd
      · simp [exactEnd] at next
  | succ fuel ih =>
    rw [readBatches] at read
    obtain ⟨envelope, planned, next⟩ := bind_ok read
    cases envelope with
    | eos =>
      by_cases exactEnd : offset + 8 = input.len
      · have same : [] = batches := by simpa [exactEnd] using next
        cases same
        exact .eos (unmap_error_ok planned) exactEnd
      · simp [exactEnd] at next
    | metadata size =>
      obtain ⟨⟨batch, stop⟩, frame, accepted⟩ := bind_ok next
      obtain ⟨tail, readTail, accepted⟩ := bind_ok accepted
      cases Except.ok.inj accepted
      obtain ⟨record, length, body, metadata, extent, budget, observed, rfl⟩ :=
        readRecord_wire (unmap_error_ok frame)
      exact .record (unmap_error_ok planned) metadata extent budget observed (ih readTail)

theorem read_wire {limits : ObservationLimits} {input : KBytes} {stream : Stream}
    (read : Arrow.MixedFlat.Timestamp.read limits input = .ok stream) :
    ∃ start, readSchema limits.ipc input = .ok (stream.fields, start) ∧
      BatchesWire limits input stream.fields limits.ipc.batches 0 start stream.batches := by
  unfold Arrow.MixedFlat.Timestamp.read at read
  split at read
  · contradiction
  obtain ⟨⟨fields, start⟩, schema, read⟩ := bind_ok read
  obtain ⟨batches, observed, read⟩ := bind_ok read
  cases Except.ok.inj read
  exact ⟨start, schema, readBatches_wire observed⟩

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Timestamp
