module

public import Silmaril.Formats.Parquet.FlatProjection.ToScan.Defs
import Silmaril.Proofs.Formats.Parquet.FlatProjection.ToScan.Correctness

public section

namespace Silmaril.Formats.Parquet.FlatProjection.ToScan

open Silmaril.Relational
open FlatProjection.Composition
open FlatProjection.Composition.Ipc
open Arrow.MixedFlat

/-- Successful source exhaustion supplies the shape witness for direct
materialization, including explicit row counts at width zero. -/
theorem observeGroups_aligned {parquet : FlatProjection.Limits} {checked : Checked}
    {batches : List OrderedWriter.BatchInput} (read : checked.readAll parquet = .ok batches) :
    Rows.Aligned (observeGroups checked batches) :=
  Proofs.Formats.Parquet.FlatProjection.ToScan.observeGroups_aligned read

/-- Direct group normalization recovers the existing source observation,
including exact nulls and opaque bytes. -/
theorem observeGroups_exact (checked : Checked) (batches : List OrderedWriter.BatchInput) :
    observeSource (observe checked batches) = some (observeGroups checked batches) :=
  Proofs.Formats.Parquet.FlatProjection.ToScan.observeGroups_exact checked batches

/-- Checked IPC emission recovers the direct group observation through EOS. -/
theorem emitted_events {ipc : Arrow.MixedFlat.Limits} {checked : Checked}
    {batches : List OrderedWriter.BatchInput} {wire : KBytes}
    (emitted : OrderedWriter.emit ipc checked.fields batches = .ok wire) :
    readEvents ipc wire = some (observeGroups checked batches) :=
  Proofs.Formats.Parquet.FlatProjection.ToScan.emitted_events emitted

/-- Materializing native IPC after a successful conversion agrees with
materializing the actual checked Parquet batches directly in footer order. -/
theorem convert_rows {parquet : FlatProjection.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes}
    {ordinals : List Nat} {wire : KBytes} (written : convert parquet ipc input ordinals = .ok wire) :
    ∃ (checked : Checked) (batches : List OrderedWriter.BatchInput)
        (read : checked.readAll parquet = .ok batches),
      openFile parquet input ordinals = .ok checked ∧ checked.columns.map Bound.ordinal = ordinals ∧
      List.Forall₂ (fun index batch => checked.readGroup parquet index = .ok batch) checked.indices batches ∧
      readEvents ipc wire = some (observeGroups checked batches) ∧
      Rows.readRows ipc wire = some (Rows.materialize (observeGroups checked batches) (observeGroups_aligned read)) :=
  Proofs.Formats.Parquet.FlatProjection.ToScan.convert_rows written

/-- Under the shared column policy and separately successful conversions,
composed physical ordinals yield the same ordered table as materializing
the original IPC and applying the corresponding typed positional projection.
Successful ordinal composition admits every requested position. -/
theorem convert_compose_rows {wideLimits directLimits : FlatProjection.Limits}
    {wideIpc directIpc : Arrow.MixedFlat.Limits} {input : Bytes}
    {ordinals positions composed : List Nat} {wideWire directWire : KBytes}
    (same : SameColumnPolicy wideLimits directLimits)
    (composedOk : composeOrdinals ordinals positions = some composed)
    (wideWritten : convert wideLimits wideIpc input ordinals = .ok wideWire)
    (directWritten : convert directLimits directIpc input composed = .ok directWire) :
    ∃ (wide : Rows.Table) (projection : Scan.Projection wide.schema),
      Rows.readRows wideIpc wideWire = some wide ∧
      wide.schema.width = ordinals.length ∧ Rows.positions projection = positions ∧
      Rows.readRows directIpc directWire = some ⟨projection.schema, projection.project wide.rows⟩ :=
  Proofs.Formats.Parquet.FlatProjection.ToScan.convert_compose_rows same composedOk wideWritten directWritten

end Silmaril.Formats.Parquet.FlatProjection.ToScan
