module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Writer

open Silmaril.Formats
open Parquet.RecursiveSchema.ListPath
open Parquet.RecursiveSchema.ListPath.Writer
open Parquet.RecursiveSchema.Repeated.Writer.Schema (equal_exact)
open Arrow.RecursiveSchema.Stream.Events (eraseBatch)

public theorem serialize_construction {limits : Limits} {input : Input} {output : Output}
    (built : serialize limits input = .ok output) : Construction limits input output := by
  unfold serialize at built
  cases original : build limits input with
  | error => simp [original, Except.map] at built
  | ok file =>
    have same : file.val = output := by simpa [original, Except.map] using built
    exact same ▸ file.property

public theorem certify_readback {limits : Limits} {input : Input} {output : Output}
    (accepted : certify limits input output = .ok ()) : Readback limits input output := by
  unfold certify at accepted
  cases original : Parquet.RecursiveSchema.ListPath.openFile limits.schema.snapshot output.bytes with
  | error => simp [original, Except.mapError, bind, Except.bind] at accepted
  | ok source =>
    by_cases same : agrees limits input output source = true
    · cases events : Reader.Events.readSource limits.chunk source.schema with
      | error cause => simp [original, same, events, Except.mapError, bind, Except.bind] at accepted
      | ok observed =>
        obtain ⟨signature, trace⟩ := observed
        cases terminal : trace.termination with
        | eos =>
          have batches : (trace.batches.map eraseBatch).isEqv input.groups
              (Arrow.RecursiveSchema.Batch.Writer.agrees limits.schema.snapshot.maxSchemaDepth) = true := by
            simpa [original, same, events, terminal, Except.mapError, bind, Except.bind,
              pure, Except.pure] using accepted
          obtain ⟨count, pairs⟩ := (List.isEqv_eq_true_iff_getElem _).mp batches
          have exactBatches := List.ext_getElem count fun i hi _ =>
            Arrow.RecursiveSchema.Batch.Writer.agrees_exact (pairs i hi)
          have rows := (Reader.Events.readSource_complete events).mp terminal
          rw [exactBatches] at rows
          simp only [agrees, Bool.and_eq_true, decide_eq_true_eq] at same
          have shape := equal_exact same.1
          have declarations := (Reader.Events.readSource_wire events).logical.fieldsExact
          exact ⟨source, ⟨signature, trace⟩, original, source.bytes_exact, same.2.1, same.2.2.1,
            shape, same.2.2.2, by simp [Reader.Events.read, original, events],
            shape ▸ declarations, terminal, exactBatches, rows, Reader.readAll_wire rows⟩
        | closed | readError _ | closeError _ =>
          simp [original, same, events, terminal, Except.mapError, bind, Except.bind] at accepted
    · have differs : agrees limits input output source = false := by simpa using same
      simp [original, differs, Except.mapError, bind, Except.bind] at accepted

public theorem emit_wire {limits : Limits} {input : Input} {output : Output}
    (written : emit limits input = .ok output) : Construction limits input output ∧ Readback limits input output := by
  unfold emit at written
  cases built : serialize limits input with
  | error => simp [built, bind, Except.bind] at written
  | ok file =>
    cases accepted : certify limits input file with
    | error => simp [built, accepted, bind, Except.bind] at written
    | ok confirmed =>
      cases confirmed
      have same : file = output := by simpa [built, accepted, bind, Except.bind, pure, Except.pure] using written
      exact same ▸ ⟨serialize_construction built, certify_readback accepted⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Writer
