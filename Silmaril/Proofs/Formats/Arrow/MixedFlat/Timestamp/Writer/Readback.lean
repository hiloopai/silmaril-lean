module

public import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Writer.Defs

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Timestamp.Writer

open Silmaril.Formats
open Silmaril.Formats.Arrow (ObservationLimits RecordBatch)
open Silmaril.Formats.Arrow.MixedFlat.Timestamp
open Silmaril.Formats.Arrow.MixedFlat.Timestamp.Writer

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem unmap_error_ok {ε δ α : Type} {result : Except ε α} {wrap : ε → δ} {value : α}
    (accepted : result.mapError wrap = .ok value) : result = .ok value := by
  cases result <;> cases accepted
  rfl

theorem emitRecord_wire {limits : ObservationLimits} {fields : List Field} {batch : Batch}
    {wire : KBytes} (written : emitRecord limits fields batch = .ok wire) :
    ∃ columns,
      checkRecord limits fields batch = .ok () ∧
      ((fields.zip batch.columns).zipIdx.mapM fun ((field, column), position) =>
        compile limits batch.rowCount field column position) = .ok columns ∧
      let (buffers, body) := Arrow.Writer.packBuffers 0 (columns.flatMap Prod.snd)
      let record : RecordBatch := ⟨batch.rowCount, columns.map Prod.fst, buffers⟩
      Arrow.StreamWriter.emitFrame limits.ipc ⟨.recordBatch record, body.len⟩ body = .ok wire := by
  obtain ⟨_, checked, written⟩ := bind_ok written
  obtain ⟨columns, compiled, written⟩ := bind_ok written
  exact ⟨columns, checked, compiled, unmap_error_ok written⟩

private theorem emit_result {limits : ObservationLimits} {stream : Stream} {wire : KBytes}
    (written : emit limits stream = .ok wire) :
    serialize limits stream = .ok wire ∧ Arrow.MixedFlat.Timestamp.read limits wire = .ok stream := by
  obtain ⟨output, serialized, written⟩ := bind_ok written
  obtain ⟨observed, decoded, written⟩ := bind_ok written
  split at written
  · rename_i agrees
    cases Except.ok.inj written
    exact ⟨serialized, agrees ▸ unmap_error_ok decoded⟩
  · contradiction

theorem emit_readback {limits : ObservationLimits} {stream : Stream} {wire : KBytes}
    (written : emit limits stream = .ok wire) : Arrow.MixedFlat.Timestamp.read limits wire = .ok stream :=
  (emit_result written).2

theorem emit_wire {limits : ObservationLimits} {stream : Stream} {wire : KBytes}
    (written : emit limits stream = .ok wire) :
    ∃ schema records,
      emitSchema limits.ipc stream.fields = .ok schema ∧
      (stream.batches.zipIdx.mapM fun (batch, index) =>
        (emitRecord limits stream.fields batch).mapError (Error.record index)) = .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) Arrow.StreamWriter.eos := by
  have serialized := (emit_result written).1
  unfold serialize at serialized
  split at serialized
  · contradiction
  obtain ⟨_, _, serialized⟩ := bind_ok serialized
  obtain ⟨schema, emitted, serialized⟩ := bind_ok serialized
  obtain ⟨records, ordered, serialized⟩ := bind_ok serialized
  exact ⟨schema, records, emitted, ordered, (Except.ok.inj serialized).symm⟩

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Timestamp.Writer
