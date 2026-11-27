module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Writer.Construction

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Writer

open Silmaril.Formats.Arrow.RecursiveSchema (Schema)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch (Limits)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream (Completed Trace read read_iff readTrace_eos readTrace_wire)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer

private theorem records_exact {depth : Nat} {batches observations : List Observation}
    (same : batches.isEqv observations (Formats.Arrow.RecursiveSchema.Batch.Writer.agrees depth) = true) :
    observations = batches := by
  induction batches generalizing observations with
  | nil => cases observations <;> simp_all
  | cons batch batches ih =>
    cases observations with
    | nil => simp at same
    | cons observed rest =>
      obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp same
      exact congrArg₂ List.cons (Formats.Arrow.RecursiveSchema.Batch.Writer.agrees_exact head).symm (ih tail)

private theorem agrees_exact {depth : Nat} {schema : Schema} {batches : List Observation}
    {trace : Trace} (same : agrees depth schema batches trace = true) :
    trace.schema = schema ∧ trace.batches.map Completed.observed = batches := by
  obtain ⟨header, records⟩ := Bool.and_eq_true_iff.mp same
  exact ⟨(Formats.Arrow.RecursiveSchema.Writer.equalSchema_exact header).symm, records_exact records⟩

theorem emit_serialized {limits : Limits} {schema : Schema} {batches : List Observation}
    {wire : KBytes} (written : emit limits schema batches = .ok wire) :
    serialize limits schema batches = .ok wire ∧ Readback limits schema batches wire := by
  cases serialized : serialize limits schema batches with
  | error cause => simp [emit, serialized, bind, Except.bind] at written
  | ok bytes =>
    cases checked : read limits bytes with
    | error cause => simp [emit, serialized, checked, Except.mapError, bind, Except.bind] at written
    | ok trace =>
      simp only [emit, serialized, checked, Except.mapError, bind, Except.bind] at written
      split at written
      · rename_i accepted
        cases Except.ok.inj written
        obtain ⟨originalSchema, observations⟩ := agrees_exact accepted
        obtain ⟨opened, ordinal, offset, eos⟩ := read_iff.mp checked
        obtain ⟨index, envelope, endAt⟩ := readTrace_eos opened eos
        have count : trace.batches.length = batches.length := by
          simpa only [List.length_map] using congrArg List.length observations
        have ordinalExact : ordinal = batches.length := index.trans count
        exact ⟨rfl, trace, offset, checked, readTrace_wire opened, originalSchema,
          observations, ordinalExact ▸ eos, envelope, endAt⟩
      · contradiction

theorem emit_batch_error {limits : Limits} {schema : Schema} {batches : List Observation}
    {ordinal : Nat} {cause : Formats.Arrow.RecursiveSchema.Batch.Writer.Error}
    (failed : emit limits schema batches = .error (.batch ordinal cause)) :
    RecordFailure limits schema 0 batches ordinal cause := by
  cases serialized : serialize limits schema batches with
  | error original =>
    have same : original = .batch ordinal cause := by
      simpa [emit, serialized, bind, Except.bind] using failed
    exact serialize_batch_error (same ▸ serialized)
  | ok bytes =>
    cases checked : read limits bytes with
    | error original =>
      simp [emit, serialized, checked, Except.mapError, bind, Except.bind] at failed
    | ok trace =>
      simp only [emit, serialized, checked, Except.mapError, bind, Except.bind] at failed
      split at failed <;> simp at failed

theorem emit_construction {limits : Limits} {schema : Schema} {batches : List Observation}
    {wire : KBytes} (written : emit limits schema batches = .ok wire) :
    Construction limits schema batches wire :=
  serialize_wire (emit_serialized written).1

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Writer
