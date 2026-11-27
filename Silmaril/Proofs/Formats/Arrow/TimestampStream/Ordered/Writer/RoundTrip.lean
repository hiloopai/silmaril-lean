module

public import Silmaril.Formats.Arrow.TimestampStream.Ordered.Writer.Defs

public section

namespace Silmaril.Proofs.Formats.Arrow.TimestampStream.Ordered.Writer

open Silmaril.Formats.Arrow hiding Field
open Silmaril.Formats.Arrow.TimestampStream.Ordered hiding Error
open Silmaril.Formats.Arrow.TimestampStream.Ordered.Writer

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem emit_checked {limits : ObservationLimits} {fields : List Field} {batches : List Batch} {wire : KBytes}
    (written : emit limits fields batches = .ok wire) :
    serialize limits fields batches = .ok wire ∧ TimestampStream.Ordered.read limits.ipc wire = .ok ⟨fields, batches⟩ := by
  cases serialized : serialize limits fields batches with
  | error cause => simp [emit, serialized, Bind.bind, Except.bind] at written
  | ok bytes =>
    cases observed : TimestampStream.Ordered.read limits.ipc bytes with
    | error cause => simp [emit, serialized, observed, Except.mapError, Bind.bind, Except.bind] at written
    | ok result =>
      by_cases same : result = ⟨fields, batches⟩
      · have output : bytes = wire := by
          simpa [emit, serialized, observed, same, Except.mapError, Bind.bind, Except.bind] using written
        subst wire
        exact ⟨rfl, observed.trans (congrArg Except.ok same)⟩
      · simp [emit, serialized, observed, same, Except.mapError, Bind.bind, Except.bind] at written

theorem emit_readback {limits : ObservationLimits} {fields : List Field} {batches : List Batch} {wire : KBytes}
    (written : emit limits fields batches = .ok wire) :
    TimestampStream.Ordered.read limits.ipc wire = .ok ⟨fields, batches⟩ :=
  (emit_checked written).2

theorem emit_wire {limits : ObservationLimits} {fields : List Field} {batches : List Batch} {wire : KBytes}
    (written : emit limits fields batches = .ok wire) :
    ∃ schema records, emitSchema limits.ipc fields = .ok schema ∧
      (batches.zipIdx.mapM fun (batch, index) =>
        (emitRecord limits.ipc fields batch).mapError (TimestampStream.Ordered.Writer.Error.record index)) =
          .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) StreamWriter.eos := by
  have serialized := (emit_checked written).1
  unfold serialize at serialized
  split at serialized
  · contradiction
  · obtain ⟨_, _, serialized⟩ := bind_ok serialized
    obtain ⟨schema, header, serialized⟩ := bind_ok serialized
    obtain ⟨records, framed, serialized⟩ := bind_ok serialized
    exact ⟨schema, records, header, framed, (Except.ok.inj serialized).symm⟩

end Silmaril.Proofs.Formats.Arrow.TimestampStream.Ordered.Writer
