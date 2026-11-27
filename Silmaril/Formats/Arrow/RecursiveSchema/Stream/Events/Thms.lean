module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Defs
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.Agreement
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.Projection

@[expose] public section

namespace Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events

open Silmaril.Relational

/-- Both the optional name and the exact recursive declaration round trip
in their original positions. -/
theorem declarations_signature (fields : List Field) :
    declarations (signature fields) = fields.map (fun field => (fieldName field, field)) :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.declarations_signature fields

theorem eraseRow_ofRow {fields : List Field} {row : Batch.Rows.Row}
    (fits : Batch.Rows.RowFits fields row) : eraseRow (ofRow fields row fits) = row :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.eraseRow_ofRow fits

theorem eraseBatch_ofBatch (fields : List Field) (batch : Batch.Rows.Observation)
    (fits : ∀ row ∈ batch.rows, Batch.Rows.RowFits fields row)
    (count : batch.rows.length = batch.rowCount) :
    eraseBatch (ofBatch fields batch fits) = batch :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.eraseBatch_ofBatch fields batch fits count

/-- The original complete batches round trip separately, including empty
batches and positive row counts at width zero. -/
theorem eraseBatches_ofTrace {limits : Batch.Limits} {input : KBytes} (trace : Stream.Trace)
    (wire : Stream.TraceWire limits input trace) :
    (ofTrace trace wire).batches.map eraseBatch = trace.batches.map Stream.Completed.observed :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.eraseBatches_ofTrace trace wire

theorem read_open_error {limits : Batch.Limits} {input : KBytes} {cause : RecursiveSchema.Error}
    (original : Stream.readTrace limits input = .error cause) :
    read limits input = .error (.schema cause) := by
  unfold read
  split <;> simp_all

/-- Events preserve the schema, complete positional batches and terminal
outcome of the original checked stream witness. -/
theorem read_wire {limits : Batch.Limits} {input : KBytes} {events : Σ source : Signature, Trace source}
    (accepted : read limits input = .ok events) : StreamWire limits input events.1 events.2 :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.read_wire accepted

theorem read_failure {limits : Batch.Limits} {input : KBytes}
    {events : Σ source : Signature, Trace source} {ordinal offset : Nat} {cause : Stream.Cause}
    (accepted : read limits input = .ok events)
    (failed : events.2.termination = .readError (.failed ordinal offset cause)) :
    ordinal = events.2.batches.length ∧
      ∃ original unspent, Stream.readTrace limits input = .ok original ∧
        original.terminal = .failed ordinal offset cause ∧
        Stream.FailureWire limits original.schema input offset unspent cause :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.read_failure accepted failed

theorem read_eos {limits : Batch.Limits} {input : KBytes} {events : Σ source : Signature, Trace source}
    (accepted : read limits input = .ok events) (eos : events.2.termination = .eos) :
    ∃ offset, EnvelopeWire limits.schema.ipc input.toList offset .eos ∧ offset + 8 = input.len :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.read_eos accepted eos

/-- Shared Events of a successful strict stream have its original ordered
declarations, complete observations and EOS. -/
theorem read_checked_eos {limits : Batch.Limits} {input : KBytes}
    {original : Stream.Trace} {ordinal offset : Nat} {events : Σ source : Signature, Trace source}
    (checked : Stream.read limits input = .ok original)
    (ending : original.terminal = .eos ordinal offset)
    (accepted : read limits input = .ok events) :
    declarations events.1 = original.schema.fields.map (fun field => (fieldName field, field)) ∧
      events.2.batches.map eraseBatch = original.batches.map Stream.Completed.observed ∧
      events.2.termination = .eos :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.read_checked_eos checked ending accepted

/-- Projection preserves every batch count at any output width. -/
theorem projectTrace_counts {source : Signature} {Failure : Type} (projection : Scan.Projection source)
    (trace : Formats.Arrow.Events.Trace source Value Failure) :
    (projectTrace projection trace).batches.map (·.rowCount) = trace.batches.map (·.rowCount) :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.projectTrace_counts projection trace

theorem projectTrace_termination {source : Signature} {Failure : Type} (projection : Scan.Projection source)
    (trace : Formats.Arrow.Events.Trace source Value Failure) : (projectTrace projection trace).termination = trace.termination := rfl

theorem projectTrace_rows {source : Signature} {Failure : Type} (projection : Scan.Projection source)
    (trace : Formats.Arrow.Events.Trace source Value Failure) : (projectTrace projection trace).rows = projection.project trace.rows :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.projectTrace_rows projection trace

theorem projectTrace_id {source : Signature} {Failure : Type} (trace : Formats.Arrow.Events.Trace source Value Failure) :
    projectTrace (Scan.Projection.id source) trace = trace :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.projectTrace_id trace

theorem projectTrace_comp {source : Signature} {Failure : Type} (first : Scan.Projection source)
    (second : Scan.Projection first.schema) (trace : Formats.Arrow.Events.Trace source Value Failure) :
    projectTrace (first.comp second) trace = projectTrace second (projectTrace first trace) :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Events.projectTrace_comp first second trace

end Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events
