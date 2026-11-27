module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.ToIpc.Defs
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.Thms
import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Thms
import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Writer.Thms
import Silmaril.Formats.Arrow.Events.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.ToIpc

open Silmaril.Formats Silmaril.Relational
open Hive.Manifest.Heterogeneous (Entry Schema Trace FileBatches)
open Hive.Manifest.Heterogeneous.ToIpc
open Parquet.FlatProjection.Events (Kind Cell)
open Parquet.FlatProjection.Events.ToIpc (observation fields batchInput)
open Silmaril.Formats.Hive
open Arrow.MixedFlat.Timestamp (readSchema BatchesWire)

theorem emitTrace_readback {schema : Scan.Schema String Kind} {output : Arrow.ObservationLimits}
    {trace : Arrow.Events.Trace schema Cell Hive.Manifest.Heterogeneous.Error} {wire : KBytes}
    (written : emitTrace output trace = .ok wire) :
    trace.termination = .eos ∧ Arrow.MixedFlat.Timestamp.read output wire = .ok (observation trace) := by
  cases termination : trace.termination <;> simp [emitTrace, termination] at written
  case eos =>
    cases emitted : Arrow.MixedFlat.Timestamp.Writer.emit output (observation trace) with
    | error cause => simp [emitted, Except.mapError] at written
    | ok bytes =>
      simp [emitted, Except.mapError] at written
      exact ⟨rfl, Arrow.MixedFlat.Timestamp.Writer.emit_readback (written ▸ emitted)⟩

theorem convert_readback {schema : Schema} {options : PartitionPath.Options}
    {input : Parquet.FlatProjection.Events.Limits} {output : Arrow.ObservationLimits}
    {manifest : List Entry} {wire : KBytes}
    (written : convert schema options input output manifest = .ok wire) :
    ∃ (trace : Trace schema) (start : Nat),
      Hive.Manifest.Heterogeneous.read schema options input manifest = .ok trace ∧
      trace.termination = .eos ∧
      Arrow.MixedFlat.Timestamp.read output wire = .ok (observation trace) ∧
      readSchema output.ipc wire = .ok (fields schema.output, start) ∧
      BatchesWire output wire (fields schema.output) output.ipc.batches 0 start (trace.batches.map batchInput) := by
  cases read : Hive.Manifest.Heterogeneous.read schema options input manifest with
  | error cause => simp [convert, read, Except.mapError, Bind.bind, Except.bind] at written
  | ok trace =>
    have emitted : emitTrace output trace = .ok wire := by
      simpa [convert, read, Except.mapError, Bind.bind, Except.bind] using written
    obtain ⟨eos, checked⟩ := emitTrace_readback emitted
    obtain ⟨start, header, batches⟩ := Arrow.MixedFlat.Timestamp.read_wire checked
    exact ⟨trace, start, rfl, eos, checked, header, batches⟩

theorem convertProjected_readback {schema : Schema} {options : PartitionPath.Options}
    {input : Parquet.FlatProjection.Events.Limits} {output : Arrow.ObservationLimits}
    {manifest : List Entry} {projection : Scan.Projection schema.output} {wire : KBytes}
    (written : convertProjected schema options input output manifest projection = .ok wire) :
    ∃ (trace : Trace schema) (start : Nat),
      Hive.Manifest.Heterogeneous.read schema options input manifest = .ok trace ∧
      trace.termination = .eos ∧
      let projected := trace.scan projection (fun _ => some true)
      Arrow.MixedFlat.Timestamp.read output wire = .ok (observation projected) ∧
      readSchema output.ipc wire = .ok (fields projection.schema, start) ∧
      BatchesWire output wire (fields projection.schema) output.ipc.batches 0 start
        (projected.batches.map batchInput) ∧
      projected.batches.map (·.rowCount) = trace.batches.map (·.rowCount) := by
  unfold convertProjected at written
  rw [Hive.Manifest.Heterogeneous.project_agrees] at written
  cases read : Hive.Manifest.Heterogeneous.read schema options input manifest with
  | error cause => simp [read, Except.map, Except.mapError, Bind.bind, Except.bind] at written
  | ok trace =>
    have emitted : emitTrace output (trace.scan projection (fun _ => some true)) = .ok wire := by
      simpa [read, Except.map, Except.mapError, Bind.bind, Except.bind] using written
    obtain ⟨eos, checked⟩ := emitTrace_readback emitted
    obtain ⟨start, header, batches⟩ := Arrow.MixedFlat.Timestamp.read_wire checked
    exact ⟨trace, start, rfl, by simpa using eos, checked, header, batches,
      Hive.Manifest.Heterogeneous.project_counts projection trace⟩

end Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.ToIpc
