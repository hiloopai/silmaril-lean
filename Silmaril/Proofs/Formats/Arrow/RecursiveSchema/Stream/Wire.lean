module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Thms
import Silmaril.Formats.Arrow.Framing.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream

open Silmaril.Formats.Arrow (EnvelopeWire readEnvelope readEnvelope_iff)
open Silmaril.Formats.Arrow.RecursiveSchema (Schema)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream

theorem poll_wire {limits : Formats.Arrow.RecursiveSchema.Batch.Limits} {schema : Schema}
    {input : KBytes} (wf : input.wf = true) (remaining ordinal offset : Nat) :
    StepWire limits schema input ordinal offset
      (poll limits schema input wf ordinal offset remaining) := by
  unfold poll
  split
  · rename_i cause envelope
    exact ⟨rfl, rfl, .envelope envelope⟩
  · rename_i envelope
    have original := (readEnvelope_iff _ _ _ _ wf).mp envelope
    split
    · rename_i exactEnd
      exact ⟨rfl, rfl, original, exactEnd⟩
    · rename_i trailing
      exact ⟨rfl, rfl, .trailingBytes original trailing⟩
  · rename_i size envelope
    have original := (readEnvelope_iff _ _ _ _ wf).mp envelope
    cases remaining with
    | zero => exact ⟨rfl, rfl, .batchLimit original⟩
    | succ fuel =>
      unfold pollRecord
      have same := Formats.Arrow.RecursiveSchema.Batch.readFrame_of_envelope (schema := schema) wf envelope
      split
      · rename_i cause batchRead
        exact ⟨rfl, rfl, .batch original (same.trans batchRead)⟩
      · rename_i frame batchRead
        split
        · rename_i cause rowRead
          exact ⟨rfl, rfl, .rows (same.trans batchRead) rowRead⟩
        · rename_i observed rowRead
          exact ⟨frame, observed, same.trans batchRead, rowRead,
            Formats.Arrow.RecursiveSchema.Batch.Rows.decode_wire rowRead, rfl⟩

private theorem drain_wire {limits : Formats.Arrow.RecursiveSchema.Batch.Limits} {schema : Schema}
    {input : KBytes} (wf : input.wf = true) (remaining ordinal offset : Nat)
    (completed : List Completed) :
    ∃ batches,
      (drain limits schema input wf remaining ordinal offset completed).1 = completed.reverse ++ batches ∧
      CursorChain limits schema input remaining ordinal offset batches
        (drain limits schema input wf remaining ordinal offset completed).2 := by
  induction remaining generalizing ordinal offset completed with
  | zero =>
    have wire := poll_wire (limits := limits) (schema := schema) wf 0 ordinal offset
    cases reply : poll limits schema input wf ordinal offset 0 with
    | stop terminal =>
      rw [reply] at wire
      exact ⟨[], by simp [drain, reply], by simpa [drain, reply] using CursorChain.stop wire⟩
  | succ remaining ih =>
    have wire := poll_wire (limits := limits) (schema := schema) wf (remaining + 1) ordinal offset
    cases reply : poll limits schema input wf ordinal offset (remaining + 1) with
    | stop terminal =>
      rw [reply] at wire
      exact ⟨[], by simp [drain, reply], by simpa [drain, reply] using CursorChain.stop wire⟩
    | yield record =>
      rw [reply] at wire
      obtain ⟨batches, order, rest⟩ := ih (ordinal + 1) record.next (record :: completed)
      refine ⟨record :: batches, ?_, ?_⟩
      · simpa [drain, reply, List.reverse_cons, List.append_assoc] using order
      · simpa [drain, reply] using CursorChain.more wire rest

theorem readTrace_wire {limits : Formats.Arrow.RecursiveSchema.Batch.Limits}
    {input : KBytes} {trace : Trace}
    (accepted : readTrace limits input = .ok trace) : TraceWire limits input trace := by
  unfold readTrace at accepted
  split at accepted
  · contradiction
  · rename_i schema offset opened
    have wf := Formats.Arrow.RecursiveSchema.readFrame_source opened
    have wire := Formats.Arrow.RecursiveSchema.readFrame_wire opened
    obtain ⟨batches, order, chain⟩ := drain_wire wf limits.schema.ipc.batches 0 offset []
      (limits := limits) (schema := schema)
    cases result : drain limits schema input wf limits.schema.ipc.batches 0 offset [] with
    | mk records terminal =>
      simp [result] at accepted order chain
      subst trace
      subst records
      exact ⟨wf, wire, chain⟩

theorem record_coordinates {limits : Formats.Arrow.RecursiveSchema.Batch.Limits}
    {schema : Schema} {input : KBytes} {ordinal offset : Nat} {record : Completed}
    (wire : RecordWire limits schema input ordinal offset record) :
    record.ordinal = ordinal ∧ record.offset = offset ∧ offset < record.next ∧ record.next ≤ input.len := by
  obtain ⟨frame, _, _, _, logical, rfl⟩ := wire
  obtain ⟨_, physical, _⟩ := logical.data
  have bound := physical.frameWire.body_bound.2
  exact ⟨rfl, rfl, by simp [Completed.ofFrame, Completed.next]; omega, bound⟩

theorem chain_end {limits : Formats.Arrow.RecursiveSchema.Batch.Limits} {schema : Schema}
    {input : KBytes} {remaining ordinal offset : Nat} {batches : List Completed} {terminal : End}
    (chain : CursorChain limits schema input remaining ordinal offset batches terminal) :
    ∃ unspent finalOffset, unspent + batches.length = remaining ∧
      EndWire limits schema input unspent (ordinal + batches.length) finalOffset terminal := by
  induction chain with
  | @stop remaining ordinal offset terminal endWire =>
    exact ⟨remaining, offset, by simp, by simpa using endWire⟩
  | more original rest ih =>
    obtain ⟨unspent, finalOffset, spent, endWire⟩ := ih
    exact ⟨unspent, finalOffset, by simp only [List.length_cons]; omega,
      by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using endWire⟩

theorem readTrace_eos {limits : Formats.Arrow.RecursiveSchema.Batch.Limits}
    {input : KBytes} {trace : Trace} {ordinal offset : Nat}
    (accepted : readTrace limits input = .ok trace) (eos : trace.terminal = .eos ordinal offset) :
    ordinal = trace.batches.length ∧ EnvelopeWire limits.schema.ipc input.toList offset .eos ∧
      offset + 8 = input.len := by
  obtain ⟨_, _, _, terminal⟩ := chain_end (readTrace_wire accepted).chain
  rw [eos] at terminal
  obtain ⟨count, cursor, original, exactEnd⟩ := terminal
  subst offset
  exact ⟨by simpa using count, original, exactEnd⟩

theorem readTrace_failure {limits : Formats.Arrow.RecursiveSchema.Batch.Limits}
    {input : KBytes} {trace : Trace} {ordinal offset : Nat} {cause : Cause}
    (accepted : readTrace limits input = .ok trace)
    (failed : trace.terminal = .failed ordinal offset cause) :
    ordinal = trace.batches.length ∧ ∃ unspent, unspent + ordinal = limits.schema.ipc.batches ∧
      FailureWire limits trace.schema input offset unspent cause := by
  obtain ⟨unspent, _, budget, terminal⟩ := chain_end (readTrace_wire accepted).chain
  rw [failed] at terminal
  obtain ⟨count, cursor, original⟩ := terminal
  subst offset
  exact ⟨by simpa using count, unspent, by omega, original⟩

theorem read_iff {limits : Formats.Arrow.RecursiveSchema.Batch.Limits}
    {input : KBytes} {trace : Trace} :
    read limits input = .ok trace ↔
      readTrace limits input = .ok trace ∧ ∃ ordinal offset, trace.terminal = .eos ordinal offset := by
  unfold Formats.Arrow.RecursiveSchema.Stream.read
  simp only [bind, Except.bind]
  cases opened : readTrace limits input with
  | error cause => simp [Except.mapError]
  | ok observed =>
    cases ended : observed.terminal with
    | eos ordinal offset =>
      simp [Except.mapError, ended, pure, Except.pure]
      exact fun same => same ▸ ⟨ordinal, offset, ended⟩
    | failed ordinal offset cause =>
      simp [Except.mapError, ended]
      rintro rfl index cursor impossible
      rw [ended] at impossible
      contradiction

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream
