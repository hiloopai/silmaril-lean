module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Thms
import Silmaril.Prelude.Bytes.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Writer

open Silmaril.Formats.Arrow.RecursiveSchema (Schema)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch (Limits)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer

private theorem records_extent (frames : List KBytes) :
    let wire := frames.foldr (· ++ ·) Formats.Arrow.StreamWriter.eos
    wire.len = (frames.map KBytes.len).sum + 8 ∧
      wire.toList = frames.flatMap KBytes.toList ++ Formats.Arrow.StreamWriter.eos.toList := by
  induction frames with
  | nil => exact ⟨rfl, rfl⟩
  | cons frame rest ih =>
    obtain ⟨size, bytes⟩ := ih
    constructor
    · change frame.len + (rest.foldr (· ++ ·) Formats.Arrow.StreamWriter.eos).len =
        frame.len + (rest.map KBytes.len).sum + 8
      rw [size, Nat.add_assoc]
    · simp only [List.foldr_cons, KBytes.toList_append, bytes, List.flatMap_cons, List.append_assoc]

theorem assemble_extent (schemaFrame : KBytes) (frames : List KBytes) :
    (assemble schemaFrame frames).len = schemaFrame.len + (frames.map KBytes.len).sum + 8 ∧
      (assemble schemaFrame frames).toList =
        schemaFrame.toList ++ frames.flatMap KBytes.toList ++ Formats.Arrow.StreamWriter.eos.toList := by
  obtain ⟨size, bytes⟩ := records_extent frames
  constructor
  · change schemaFrame.len + (frames.foldr (· ++ ·) Formats.Arrow.StreamWriter.eos).len = _
    rw [size, Nat.add_assoc]
  · simp only [assemble, KBytes.toList_append, bytes, List.append_assoc]

theorem records_wire {limits : Limits} {schema : Schema} {start : Nat}
    {batches : List Observation} {frames : List KBytes}
    (written : writeRecords limits schema start batches = .ok frames) :
    RecordsWire limits schema batches frames := by
  induction batches generalizing start frames with
  | nil =>
    cases Except.ok.inj written
    exact .nil
  | cons batch rest ih =>
    cases first : Formats.Arrow.RecursiveSchema.Batch.Writer.serialize limits schema batch with
    | error cause => simp [writeRecords, first] at written
    | ok frame =>
      cases tail : writeRecords limits schema (start + 1) rest with
      | error cause => simp [writeRecords, first, tail, Except.map] at written
      | ok remaining =>
        have ordered : frame :: remaining = frames :=
          Except.ok.inj (by simpa only [writeRecords, first, tail, Except.map] using written)
        subst frames
        exact .cons first (ih tail)

theorem records_error {limits : Limits} {schema : Schema} {start ordinal : Nat}
    {batches : List Observation} {cause : Formats.Arrow.RecursiveSchema.Batch.Writer.Error}
    (failed : writeRecords limits schema start batches = .error (ordinal, cause)) :
    RecordFailure limits schema start batches ordinal cause := by
  induction batches generalizing start with
  | nil => simp [writeRecords] at failed
  | cons batch rest ih =>
    cases first : Formats.Arrow.RecursiveSchema.Batch.Writer.serialize limits schema batch with
    | error original =>
      have reached : start = ordinal ∧ original = cause := by
        simpa [writeRecords, first] using failed
      obtain ⟨rfl, rfl⟩ := reached
      exact ⟨[], batch, rest, [], rfl, by simp, .nil, first⟩
    | ok frame =>
      cases tail : writeRecords limits schema (start + 1) rest with
      | ok remaining => simp [writeRecords, first, tail, Except.map] at failed
      | error pair =>
        have reached : pair = (ordinal, cause) :=
          Except.error.inj (by simpa only [writeRecords, first, tail, Except.map] using failed)
        subst pair
        obtain ⟨earlier, invalid, later, frames, split, indexed, prior, original⟩ := (ih tail).failure
        refine ⟨batch :: earlier, invalid, later, frame :: frames, ?_, ?_, .cons first prior, original⟩
        · rw [split, List.cons_append]
        · simp only [List.length_cons]
          omega

theorem serialize_wire {limits : Limits} {schema : Schema} {batches : List Observation}
    {wire : KBytes} (written : serialize limits schema batches = .ok wire) :
    Construction limits schema batches wire := by
  unfold serialize at written
  split at written
  · contradiction
  · rename_i within
    cases header : Formats.Arrow.RecursiveSchema.Writer.serializeFrame limits.schema schema with
    | error cause => simp [header, Except.mapError, bind, Except.bind] at written
    | ok schemaFrame =>
      cases records : writeRecords limits schema 0 batches with
      | error cause => simp [header, records, Except.mapError, bind, Except.bind] at written
      | ok frames =>
        simp only [header, records, Except.mapError, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at written
        obtain ⟨budget, planned, size, signed, capped, exactHeader⟩ :=
          Formats.Arrow.RecursiveSchema.Writer.serializeFrame_extent header
        exact ⟨by omega, budget, frames, planned, size, signed, capped,
          records_wire records, written.symm.trans (congrArg (assemble · frames) exactHeader)⟩

theorem serialize_batch_error {limits : Limits} {schema : Schema} {batches : List Observation}
    {ordinal : Nat} {cause : Formats.Arrow.RecursiveSchema.Batch.Writer.Error}
    (failed : serialize limits schema batches = .error (.batch ordinal cause)) :
    RecordFailure limits schema 0 batches ordinal cause := by
  unfold serialize at failed
  split at failed
  · simp at failed
  · cases header : Formats.Arrow.RecursiveSchema.Writer.serializeFrame limits.schema schema with
    | error original => simp [header, Except.mapError, bind, Except.bind] at failed
    | ok schemaFrame =>
      cases records : writeRecords limits schema 0 batches with
      | ok frames =>
        simp [header, records, Except.mapError, bind, Except.bind, pure, Except.pure] at failed
      | error pair =>
        obtain ⟨index, original⟩ := pair
        have reached : index = ordinal ∧ original = cause := by
          simpa [header, records, Except.mapError, bind, Except.bind] using failed
        obtain ⟨rfl, rfl⟩ := reached
        exact records_error records

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Writer
