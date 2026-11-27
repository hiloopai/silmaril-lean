module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.Thms
import Silmaril.Formats.Arrow.TimestampStream.Ordered.Thms
import Silmaril.Formats.Arrow.TimestampStream.Ordered.Writer.Thms
import Init.Data.List.OfFn

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc

open Silmaril.Formats Parquet Timestamp Silmaril.Relational
open Silmaril.Formats.Parquet.Timestamp.Leaf.Projection (Checked)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc
open Silmaril.Numeric.Timestamp (Ticks)

theorem fields_at (schema : Schema) (position : Fin schema.width) :
    (fields schema)[position.val]? = some (Leaf.Events.ToIpc.bindingAt schema position) := by
  have valid : position.val < (fields schema).length := by simp [fields]
  rw [List.getElem?_eq_getElem valid]
  simp [fields]

theorem batchInput_at {schema : Schema} (batch : Scan.Columns schema Leaf.Events.Cell)
    (position : Fin schema.width) :
    (batchInput batch).columns[position.val]? = some ((batch.values position).map (Option.map Ticks.ticks)) := by
  have valid : position.val < (batchInput batch).columns.length := by simp [batchInput]
  rw [List.getElem?_eq_getElem valid]
  simp [batchInput]

theorem batchInput_aligned {schema : Schema} (batch : Scan.Columns schema Leaf.Events.Cell) :
    (batchInput batch).Aligned (fields schema) := by
  refine ⟨by simp [batchInput, fields], ?_⟩
  intro column member
  obtain ⟨position, rfl⟩ := List.mem_ofFn.mp member
  simpa [batchInput] using batch.length_eq position

theorem emitTrace_readback {schema : Schema} {limits : Arrow.ObservationLimits}
    {trace : Arrow.Events.Trace schema Leaf.Events.Cell Leaf.Projection.Error} {wire : KBytes}
    (written : emitTrace limits trace = .ok wire) :
    trace.termination = .eos ∧ Arrow.TimestampStream.Ordered.read limits.ipc wire = .ok (observation trace) := by
  cases ended : trace.termination with
  | closed | readError _ | closeError _ => simp [emitTrace, ended] at written
  | eos =>
    have emitted : Arrow.TimestampStream.Ordered.Writer.emit limits
        (observation trace).fields (observation trace).batches = .ok wire := by
      cases result : Arrow.TimestampStream.Ordered.Writer.emit limits
          (observation trace).fields (observation trace).batches <;>
        simp [emitTrace, ended, result, Except.mapError] at written ⊢
      exact written
    exact ⟨rfl, Arrow.TimestampStream.Ordered.Writer.emit_readback emitted⟩

theorem convert_readback {limits : Leaf.Projection.Limits} {output : Arrow.ObservationLimits}
    {input : Bytes} {ordinals : Array Nat} {wire : KBytes}
    (written : convert limits output input ordinals = .ok wire) :
    ∃ (schema : Schema) (trace : Arrow.Events.Trace schema Leaf.Events.Cell Leaf.Projection.Error),
      Leaf.Projection.readAll limits input ordinals = .ok ⟨schema, trace⟩ ∧ trace.termination = .eos ∧
      Arrow.TimestampStream.Ordered.read output.ipc wire = .ok (observation trace) ∧
      (∀ batch ∈ (observation trace).batches, batch.Aligned (fields schema)) ∧
      ∃ start, Arrow.TimestampStream.Ordered.readSchema output.ipc wire = .ok (fields schema, start) ∧
        Arrow.TimestampStream.Ordered.BatchesWire output.ipc wire (fields schema) output.ipc.batches
          start (observation trace).batches := by
  cases source : Leaf.Projection.readAll limits input ordinals with
  | error cause => simp [convert, source, Except.mapError, Bind.bind, Except.bind] at written
  | ok result =>
    obtain ⟨schema, trace⟩ := result
    have emitted : emitTrace output trace = .ok wire := by
      simpa [convert, source, Except.mapError, Bind.bind, Except.bind] using written
    obtain ⟨ended, decoded⟩ := emitTrace_readback emitted
    obtain ⟨_, start, header, records⟩ := (Arrow.TimestampStream.Ordered.read_iff _ _ _).mp decoded
    exact ⟨schema, trace, rfl, ended, decoded, Arrow.TimestampStream.Ordered.batchesWire_aligned records,
      start, header, records⟩

private theorem traceGroups_footer {checked : Checked} {limits : Leaf.Projection.Limits} (groups : List Nat)
    (eos : (checked.traceGroups limits groups).termination = .eos) :
    List.Forall₂ (fun group batch => ∃ original, checked.snapshot.groupAt group = some original ∧
      batch.rowCount = original.numRows.toNat) groups
      (observation (checked.traceGroups limits groups)).batches := by
  induction groups with
  | nil => exact .nil
  | cons group rest ih =>
    cases read : checked.readGroup limits group with
    | error cause => simp [Leaf.Projection.Checked.traceGroups, read] at eos
    | ok batch =>
      have tail : (checked.traceGroups limits rest).termination = .eos := by
        simpa [Leaf.Projection.Checked.traceGroups, read] using eos
      obtain ⟨original, selected, rows, _⟩ := Leaf.Projection.readGroup_footer read
      simp only [observation, Leaf.Projection.Checked.traceGroups, read, List.map_cons]
      exact .cons ⟨original, selected, rows⟩ (ih tail)

theorem convert_footerBatches {limits : Leaf.Projection.Limits} {output : Arrow.ObservationLimits}
    {input : Bytes} {ordinals : Array Nat} {wire : KBytes}
    (written : convert limits output input ordinals = .ok wire) :
    ∃ checked : Checked, Leaf.Projection.openFile limits input ordinals = .ok checked ∧
      Arrow.TimestampStream.Ordered.read output.ipc wire = .ok (observation (checked.trace limits)) ∧
      List.Forall₂ (fun group batch => ∃ original, checked.snapshot.groupAt group = some original ∧
        batch.rowCount = original.numRows.toNat) checked.indices (observation (checked.trace limits)).batches := by
  cases opened : Leaf.Projection.openFile limits input ordinals with
  | error cause => simp [convert, Leaf.Projection.readAll, opened, Except.map, Except.mapError, Bind.bind, Except.bind] at written
  | ok checked =>
    have emitted : emitTrace output (checked.trace limits) = .ok wire := by
      simpa [convert, Leaf.Projection.readAll_opened opened, Except.mapError, Bind.bind, Except.bind] using written
    obtain ⟨ended, observed⟩ := emitTrace_readback emitted
    exact ⟨checked, rfl, observed, traceGroups_footer checked.indices ended⟩

theorem convert_open_failure {limits : Leaf.Projection.Limits} {output : Arrow.ObservationLimits}
    {input : Bytes} {ordinals : Array Nat} {cause : Leaf.Projection.Error}
    (failed : Leaf.Projection.openFile limits input ordinals = .error cause) :
    convert limits output input ordinals = .error (.source cause) := by
  simp [convert, Leaf.Projection.readAll, failed, Except.map, Except.mapError, Bind.bind, Except.bind]

theorem convert_first_error {limits : Leaf.Projection.Limits} {output : Arrow.ObservationLimits}
    {input : Bytes} {ordinals : Array Nat} {checked : Checked}
    {before after : List Nat} {group : Nat}
    {batches : List (Scan.Columns checked.schema Leaf.Events.Cell)} {cause : Leaf.Projection.Error}
    (opened : Leaf.Projection.openFile limits input ordinals = .ok checked)
    (split : checked.indices = before ++ group :: after)
    (earlier : before.mapM (checked.readGroup limits) = .ok batches)
    (failed : checked.readGroup limits group = .error cause) :
    convert limits output input ordinals = .error (.source cause) := by
  rw [convert, Leaf.Projection.readAll_opened opened, Leaf.Projection.trace_first_error split earlier failed]
  rfl

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc
