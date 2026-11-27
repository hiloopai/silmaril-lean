module

public import Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.FlatProjection.Events.ToIpc.Readback

public section

namespace Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc

open Silmaril.Relational

/-- The schema preserves the original selected descriptors at every position. -/
theorem fields_position (schema : Schema) (position : Fin schema.width) :
    (fields schema)[position.val]'(by simp [fields]) =
      field (schema.kind position).1 (schema.kind position).2 := by
  simp [fields]

/-- A batch preserves the shared count and each typed column, even when width is zero. -/
theorem batchInput_exact {schema : Schema} (batch : Scan.Columns schema Cell) :
    (batchInput batch).rowCount = batch.rowCount ∧
    (batchInput batch).columns.length = schema.width ∧
    ∀ position : Fin schema.width, (batchInput batch).columns[position.val]'(by simp [batchInput]) =
      column (schema.kind position).2 (batch.values position) := by
  simp [batchInput]

/-- A source admission failure is returned ahead of all output checks. -/
theorem convert_open_error {limits : Limits} {output : Arrow.ObservationLimits}
    {input : Bytes} {ordinals : Array Nat} {cause : Events.Error}
    (failed : Events.readAll limits input ordinals = .error cause) :
    convert limits output input ordinals = .error (.source cause) := by
  simp [convert, failed, Except.mapError, Bind.bind, Except.bind]

/-- A late checked source failure also precedes every output check. -/
theorem convert_read_error {limits : Limits} {output : Arrow.ObservationLimits}
    {input : Bytes} {ordinals : Array Nat} {schema : Schema}
    {trace : Arrow.Events.Trace schema Cell Events.Error} {cause : Events.Error}
    (read : Events.readAll limits input ordinals = .ok ⟨schema, trace⟩)
    (failed : trace.termination = .readError cause) :
    convert limits output input ordinals = .error (.source cause) := by
  simp [convert, read, emitTrace, failed, Except.mapError, Bind.bind, Except.bind]

/-- Successful conversion recovers the complete source observation through native exact EOS. -/
theorem convert_readback {limits : Limits} {output : Arrow.ObservationLimits}
    {input : Bytes} {ordinals : Array Nat} {wire : KBytes}
    (written : convert limits output input ordinals = .ok wire) :
    ∃ (schema : Schema) (trace : Arrow.Events.Trace schema Cell Events.Error) (start : Nat),
      Events.readAll limits input ordinals = .ok ⟨schema, trace⟩ ∧
      trace.termination = .eos ∧
      Arrow.MixedFlat.Timestamp.read output wire = .ok (observation trace) ∧
      Arrow.MixedFlat.Timestamp.readSchema output.ipc wire = .ok (fields schema, start) ∧
      Arrow.MixedFlat.Timestamp.BatchesWire output wire (fields schema) output.ipc.batches 0 start
        (trace.batches.map batchInput) :=
  Proofs.Formats.Parquet.FlatProjection.Events.ToIpc.convert_readback written

end Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc
