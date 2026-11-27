module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.Readback

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)
open Leaf.Projection (Checked)

/-- Every emitted field matches its original selected position and Arrow descriptor. -/
theorem fields_at (schema : Schema) (position : Fin schema.width) :
    (fields schema)[position.val]? = some (Leaf.Events.ToIpc.bindingAt schema position) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.fields_at schema position

/-- The native batch input retains each ordered signed nullable tick column. -/
theorem batchInput_at {schema : Schema} (batch : Scan.Columns schema Leaf.Events.Cell)
    (position : Fin schema.width) :
    (batchInput batch).columns[position.val]? = some ((batch.values position).map (Option.map Ticks.ticks)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.batchInput_at batch position

/-- The typed source batch supplies the exact alignment witness. -/
theorem batchInput_aligned {schema : Schema} (batch : Scan.Columns schema Leaf.Events.Cell) :
    (batchInput batch).Aligned (fields schema) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.batchInput_aligned batch

/-- Successful emission requires source EOS and recovers the exact typed observation. -/
theorem emitTrace_readback {schema : Schema} {limits : Arrow.ObservationLimits}
    {trace : Arrow.Events.Trace schema Leaf.Events.Cell Leaf.Projection.Error} {wire : KBytes}
    (written : emitTrace limits trace = .ok wire) :
    trace.termination = .eos ∧ Arrow.TimestampStream.Ordered.read limits.ipc wire = .ok (observation trace) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.emitTrace_readback written

/-- The original typed Events compose with aligned native IPC readback through exact EOS. -/
theorem convert_readback {limits : Leaf.Projection.Limits} {output : Arrow.ObservationLimits}
    {input : Bytes} {ordinals : Array Nat} {wire : KBytes}
    (written : convert limits output input ordinals = .ok wire) :
    ∃ (schema : Schema) (trace : Arrow.Events.Trace schema Leaf.Events.Cell Leaf.Projection.Error),
      Leaf.Projection.readAll limits input ordinals = .ok ⟨schema, trace⟩ ∧ trace.termination = .eos ∧
      Arrow.TimestampStream.Ordered.read output.ipc wire = .ok (observation trace) ∧
      (∀ batch ∈ (observation trace).batches, batch.Aligned (fields schema)) ∧
      ∃ start, Arrow.TimestampStream.Ordered.readSchema output.ipc wire = .ok (fields schema, start) ∧
        Arrow.TimestampStream.Ordered.BatchesWire output.ipc wire (fields schema) output.ipc.batches
          start (observation trace).batches :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.convert_readback written

/-- The decoded IPC contains one ordered batch per original footer group with its exact row count. -/
theorem convert_footerBatches {limits : Leaf.Projection.Limits} {output : Arrow.ObservationLimits}
    {input : Bytes} {ordinals : Array Nat} {wire : KBytes}
    (written : convert limits output input ordinals = .ok wire) :
    ∃ checked : Checked, Leaf.Projection.openFile limits input ordinals = .ok checked ∧
      Arrow.TimestampStream.Ordered.read output.ipc wire = .ok (observation (checked.trace limits)) ∧
      List.Forall₂ (fun group batch => ∃ original, checked.snapshot.groupAt group = some original ∧
        batch.rowCount = original.numRows.toNat) checked.indices (observation (checked.trace limits)).batches :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.convert_footerBatches written

/-- Source-open failure precedes all IPC admission. -/
theorem convert_open_failure {limits : Leaf.Projection.Limits} {output : Arrow.ObservationLimits}
    {input : Bytes} {ordinals : Array Nat} {cause : Leaf.Projection.Error}
    (failed : Leaf.Projection.openFile limits input ordinals = .error cause) :
    convert limits output input ordinals = .error (.source cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.convert_open_failure failed

/-- The first failed original group prevents writer admission, preserving its typed source cause. -/
theorem convert_first_error {limits : Leaf.Projection.Limits} {output : Arrow.ObservationLimits}
    {input : Bytes} {ordinals : Array Nat} {checked : Checked}
    {before after : List Nat} {group : Nat}
    {batches : List (Scan.Columns checked.schema Leaf.Events.Cell)} {cause : Leaf.Projection.Error}
    (opened : Leaf.Projection.openFile limits input ordinals = .ok checked)
    (split : checked.indices = before ++ group :: after)
    (earlier : before.mapM (checked.readGroup limits) = .ok batches)
    (failed : checked.readGroup limits group = .error cause) :
    convert limits output input ordinals = .error (.source cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.convert_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc
