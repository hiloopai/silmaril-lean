module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Defs
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Wire

@[expose] public section

namespace Silmaril.Formats.Arrow.RecursiveSchema.Stream

/-- Every successful step binds its original frame. A terminal step binds
the exact reached envelope, limit, layout or row outcome. -/
theorem poll_wire {limits : Batch.Limits} {schema : Schema} {input : KBytes}
    (wf : input.wf = true) (remaining ordinal offset : Nat) :
    StepWire limits schema input ordinal offset
      (poll limits schema input wf ordinal offset remaining) :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.poll_wire wf remaining ordinal offset

/-- Open the original schema and certify the exact cursor chain through the
complete prefix, including when the next frame fails. -/
theorem readTrace_wire {limits : Batch.Limits} {input : KBytes} {trace : Trace}
    (accepted : readTrace limits input = .ok trace) : TraceWire limits input trace :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.readTrace_wire accepted

/-- A completed batch advances strictly from its original offset and
ends inside the original carrier. -/
theorem RecordWire.coordinates {limits : Batch.Limits} {schema : Schema} {input : KBytes}
    {ordinal offset : Nat} {record : Completed}
    (wire : RecordWire limits schema input ordinal offset record) :
    record.ordinal = ordinal ∧ record.offset = offset ∧ offset < record.next ∧ record.next ≤ input.len :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.record_coordinates wire

theorem readTrace_open_error {limits : Batch.Limits} {input : KBytes} {error : RecursiveSchema.Error}
    (original : RecursiveSchema.readFrame limits.schema input = .error error) :
    readTrace limits input = .error error := by
  unfold readTrace
  split <;> simp_all

theorem CursorChain.end_wire {limits : Batch.Limits} {schema : Schema} {input : KBytes}
    {remaining ordinal offset : Nat} {batches : List Completed} {terminal : End}
    (chain : CursorChain limits schema input remaining ordinal offset batches terminal) :
    ∃ unspent finalOffset, unspent + batches.length = remaining ∧
      EndWire limits schema input unspent (ordinal + batches.length) finalOffset terminal :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.chain_end chain

/-- Each retained record has its original frame at its reported coordinates. -/
theorem CursorChain.record_of_mem {limits : Batch.Limits} {schema : Schema} {input : KBytes}
    {remaining ordinal offset : Nat} {batches : List Completed} {terminal : End}
    (chain : CursorChain limits schema input remaining ordinal offset batches terminal)
    {record : Completed} (member : record ∈ batches) :
    RecordWire limits schema input record.ordinal record.offset record :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.record_of_mem chain member

theorem RecordWire.rows {limits : Batch.Limits} {schema : Schema} {input : KBytes}
    {ordinal offset : Nat} {record : Completed} (wire : RecordWire limits schema input ordinal offset record) :
    record.observed.rows.length = record.observed.rowCount ∧
      ∀ row ∈ record.observed.rows, Batch.Rows.RowFits schema.fields row := by
  obtain ⟨_, _, _, _, logical, rfl⟩ := wire
  exact ⟨logical.count.trans logical.rowCount.symm, logical.typed⟩

theorem readTrace_eos {limits : Batch.Limits} {input : KBytes} {trace : Trace} {ordinal offset : Nat}
    (accepted : readTrace limits input = .ok trace) (eos : trace.terminal = .eos ordinal offset) :
    ordinal = trace.batches.length ∧ EnvelopeWire limits.schema.ipc input.toList offset .eos ∧
      offset + 8 = input.len :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.readTrace_eos accepted eos

theorem readTrace_failure {limits : Batch.Limits} {input : KBytes} {trace : Trace}
    {ordinal offset : Nat} {cause : Cause} (accepted : readTrace limits input = .ok trace)
    (failed : trace.terminal = .failed ordinal offset cause) :
    ordinal = trace.batches.length ∧ ∃ unspent, unspent + ordinal = limits.schema.ipc.batches ∧
      FailureWire limits trace.schema input offset unspent cause :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.readTrace_failure accepted failed

/-- Strict success is precisely admission with a successful terminal trace. -/
theorem read_iff {limits : Batch.Limits} {input : KBytes} {trace : Trace} :
    read limits input = .ok trace ↔
      readTrace limits input = .ok trace ∧ ∃ ordinal offset, trace.terminal = .eos ordinal offset :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.read_iff

end Silmaril.Formats.Arrow.RecursiveSchema.Stream
