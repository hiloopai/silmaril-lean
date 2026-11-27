module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Thms
import Silmaril.Semantics.Relational.Table.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Events

open Silmaril.Relational
open Silmaril.Formats.Arrow.RecursiveSchema (Field)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events

theorem declarations_signature (fields : List Field) :
    declarations (signature fields) = fields.map (fun field => (fieldName field, field)) := by
  apply List.ext_getElem
  · simp [declarations, signature]
  · intro index left right
    simp [declarations, signature]

private theorem erase_cell {field : Field} {raw : Formats.Arrow.RecursiveSchema.Batch.Rows.Cell}
    (fits : Formats.Arrow.RecursiveSchema.Batch.Rows.CellFits field raw) :
    (cell field raw fits).map Subtype.val = raw := by
  cases raw <;> rfl

theorem eraseRow_ofRow {fields : List Field} {row : Formats.Arrow.RecursiveSchema.Batch.Rows.Row}
    (fits : Formats.Arrow.RecursiveSchema.Batch.Rows.RowFits fields row) :
    eraseRow (ofRow fields row fits) = row := by
  apply List.ext_getElem
  · simp [eraseRow, signature, fits.length]
  · intro index left right
    simp only [eraseRow, List.getElem_ofFn, ofRow, List.getElem_toArray]
    exact erase_cell _

theorem eraseBatch_ofBatch (fields : List Field) (batch : Formats.Arrow.RecursiveSchema.Batch.Rows.Observation)
    (fits : ∀ row ∈ batch.rows, Formats.Arrow.RecursiveSchema.Batch.Rows.RowFits fields row)
    (count : batch.rows.length = batch.rowCount) :
    eraseBatch (ofBatch fields batch fits) = batch := by
  have rows :
      (batch.rows.attach.map (fun row => ofRow fields row.val (fits _ row.property))).map eraseRow =
        batch.rows := by
    rw [List.map_map]
    calc
      _ = batch.rows.attach.map Subtype.val := by
        apply List.map_congr_left
        intro row _
        exact eraseRow_ofRow (fits _ row.property)
      _ = _ := List.attach_map_subtype_val _
  unfold eraseBatch ofBatch rowsOfBatch
  rw [AlignedColumns.toRows_ofRows, rows]
  simp only [AlignedColumns.ofRows, List.length_map, List.length_attach, count]

theorem eraseBatches_ofTrace {limits : Formats.Arrow.RecursiveSchema.Batch.Limits}
    {input : KBytes} (trace : Formats.Arrow.RecursiveSchema.Stream.Trace)
    (wire : Formats.Arrow.RecursiveSchema.Stream.TraceWire limits input trace) :
    (ofTrace trace wire).batches.map eraseBatch = trace.batches.map Formats.Arrow.RecursiveSchema.Stream.Completed.observed := by
  simp only [ofTrace, List.map_map]
  rw [← List.attach_map_val (l := trace.batches)]
  apply List.map_congr_left
  intro record _
  have source := (wire.chain.record_of_mem record.property).rows
  exact eraseBatch_ofBatch _ _ source.2 source.1

theorem read_wire {limits : Formats.Arrow.RecursiveSchema.Batch.Limits} {input : KBytes}
    {events : Σ source : Signature, Trace source}
    (accepted : Formats.Arrow.RecursiveSchema.Stream.Events.read limits input = .ok events) : StreamWire limits input events.1 events.2 := by
  unfold Formats.Arrow.RecursiveSchema.Stream.Events.read at accepted
  split at accepted
  · contradiction
  · rename_i original checked
    have wire := Formats.Arrow.RecursiveSchema.Stream.readTrace_wire checked
    have same := Except.ok.inj accepted
    subst events
    exact ⟨original, checked, wire, declarations_signature _, eraseBatches_ofTrace original wire, rfl⟩

theorem read_failure {limits : Formats.Arrow.RecursiveSchema.Batch.Limits} {input : KBytes}
    {events : Σ source : Signature, Trace source} {ordinal offset : Nat}
    {cause : Formats.Arrow.RecursiveSchema.Stream.Cause}
    (accepted : Formats.Arrow.RecursiveSchema.Stream.Events.read limits input = .ok events)
    (failed : events.2.termination = .readError (.failed ordinal offset cause)) :
    ordinal = events.2.batches.length ∧
      ∃ original unspent, Formats.Arrow.RecursiveSchema.Stream.readTrace limits input = .ok original ∧
        original.terminal = .failed ordinal offset cause ∧
        Formats.Arrow.RecursiveSchema.Stream.FailureWire limits original.schema input offset unspent cause := by
  obtain ⟨original, readTrace, _, _, batches, outcome⟩ := (read_wire accepted).trace
  rw [failed] at outcome
  have ended : original.terminal = .failed ordinal offset cause := by
    cases endOfTrace : original.terminal <;> simp [terminal, endOfTrace] at outcome ⊢
    exact ⟨outcome.1.symm, outcome.2.1.symm, outcome.2.2.symm⟩
  obtain ⟨count, unspent, _, wire⟩ := Formats.Arrow.RecursiveSchema.Stream.readTrace_failure readTrace ended
  have prefixLength := congrArg List.length batches
  simp only [List.length_map] at prefixLength
  exact ⟨count.trans prefixLength.symm, original, unspent, readTrace, ended, wire⟩

theorem read_eos {limits : Formats.Arrow.RecursiveSchema.Batch.Limits} {input : KBytes}
    {events : Σ source : Signature, Trace source} (accepted : Formats.Arrow.RecursiveSchema.Stream.Events.read limits input = .ok events)
    (eos : events.2.termination = .eos) :
    ∃ offset, Formats.Arrow.EnvelopeWire limits.schema.ipc input.toList offset .eos ∧
      offset + 8 = input.len := by
  obtain ⟨original, readTrace, _, _, _, outcome⟩ := (read_wire accepted).trace
  rw [eos] at outcome
  cases ended : original.terminal with
  | failed ordinal offset cause => simp [terminal, ended] at outcome
  | eos ordinal offset =>
    exact ⟨offset, (Formats.Arrow.RecursiveSchema.Stream.readTrace_eos readTrace ended).2⟩

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Events
