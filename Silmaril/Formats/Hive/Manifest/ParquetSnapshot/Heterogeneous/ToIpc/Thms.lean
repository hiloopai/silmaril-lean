module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.ToIpc.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.ToIpc
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.Thms
import Silmaril.Formats.Arrow.Events.Thms

public section

namespace Silmaril.Formats.Hive.Manifest.Heterogeneous.ToIpc

open Silmaril.Relational
open Parquet.FlatProjection.Events.ToIpc (observation fields batchInput)
open Arrow.MixedFlat.Timestamp (readSchema BatchesWire)

/-- Successful IPC contains the complete positional observation and exact EOS. -/
theorem convert_readback {schema : Schema} {options : PartitionPath.Options}
    {input : Parquet.FlatProjection.Events.Limits} {output : Arrow.ObservationLimits}
    {manifest : List Entry} {wire : KBytes}
    (written : convert schema options input output manifest = .ok wire) :
    ∃ (trace : Trace schema) (start : Nat),
      Heterogeneous.read schema options input manifest = .ok trace ∧
      trace.termination = .eos ∧
      Arrow.MixedFlat.Timestamp.read output wire = .ok (observation trace) ∧
      readSchema output.ipc wire = .ok (fields schema.output, start) ∧
      BatchesWire output wire (fields schema.output) output.ipc.batches 0 start (trace.batches.map batchInput) :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.ToIpc.convert_readback written

/-- Each direct file observation contributes its exact batches in manifest order. -/
theorem convert_file_batches {schema : Schema} {options : PartitionPath.Options}
    {input : Parquet.FlatProjection.Events.Limits} {output : Arrow.ObservationLimits}
    {manifest : List Entry} {wire : KBytes}
    (written : convert schema options input output manifest = .ok wire) :
    ∃ files, List.Forall₂ (FileBatches schema options input) manifest.zipIdx files ∧
      Arrow.MixedFlat.Timestamp.read output wire = .ok ⟨fields schema.output, files.flatten.map batchInput⟩ := by
  obtain ⟨trace, _, read, eos, decoded, _, _⟩ := convert_readback written
  obtain ⟨files, exactFiles, batches⟩ := read_eos read eos
  exact ⟨files, exactFiles, by simpa [observation, batches] using decoded⟩

/-- Projected IPC reads back the logical projection and preserves every batch count, including at width zero. -/
theorem convertProjected_readback {schema : Schema} {options : PartitionPath.Options}
    {input : Parquet.FlatProjection.Events.Limits} {output : Arrow.ObservationLimits}
    {manifest : List Entry} {projection : Scan.Projection schema.output} {wire : KBytes}
    (written : convertProjected schema options input output manifest projection = .ok wire) :
    ∃ (trace : Trace schema) (start : Nat),
      Heterogeneous.read schema options input manifest = .ok trace ∧
      trace.termination = .eos ∧
      let projected := trace.scan projection (fun _ => some true)
      Arrow.MixedFlat.Timestamp.read output wire = .ok (observation projected) ∧
      readSchema output.ipc wire = .ok (fields projection.schema, start) ∧
      BatchesWire output wire (fields projection.schema) output.ipc.batches 0 start
        (projected.batches.map batchInput) ∧
      projected.batches.map (·.rowCount) = trace.batches.map (·.rowCount) :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.ToIpc.convertProjected_readback written

/-- A schema failure precedes all IPC output checks. -/
theorem convert_open_error {schema : Schema} {options : PartitionPath.Options}
    {input : Parquet.FlatProjection.Events.Limits} {output : Arrow.ObservationLimits}
    {manifest : List Entry} {cause : Heterogeneous.Error}
    (failed : Heterogeneous.read schema options input manifest = .error cause) :
    convert schema options input output manifest = .error (.source cause) := by
  simp [convert, failed, Bind.bind, Except.bind, Except.mapError]

/-- Any reached file error takes precedence over IPC admission, and yields no bytes. -/
theorem convert_read_error {schema : Schema} {options : PartitionPath.Options}
    {input : Parquet.FlatProjection.Events.Limits} {output : Arrow.ObservationLimits}
    {manifest : List Entry} {trace : Trace schema} {cause : Heterogeneous.Error}
    (read : Heterogeneous.read schema options input manifest = .ok trace)
    (failed : trace.termination = .readError cause) :
    convert schema options input output manifest = .error (.source cause) := by
  simp [convert, read, emitTrace, failed, Bind.bind, Except.bind, Except.mapError]

/-- The first failing manifest occurrence keeps its original path and cause in IPC conversion. -/
theorem convert_first_error {schema : Schema} {options : PartitionPath.Options}
    {input : Parquet.FlatProjection.Events.Limits} {output : Arrow.ObservationLimits}
    {manifest : List Entry} {before after : List (Entry × Nat)} {current : Entry × Nat}
    {cause : Heterogeneous.Error} (admitted : checkSchema schema = .ok ())
    (split : manifest.zipIdx = before ++ current :: after)
    (earlier : ∀ entry ∈ before, (readFile schema options input entry).termination = .eos)
    (failed : (readFile schema options input current).termination = .readError cause) :
    convert schema options input output manifest = .error (.source cause) :=
  convert_read_error (read_first_error admitted split earlier failed) rfl

/-- Projecting away a failed source field preserves its typed terminal error. -/
theorem convertProjected_read_error {schema : Schema} {options : PartitionPath.Options}
    {input : Parquet.FlatProjection.Events.Limits} {output : Arrow.ObservationLimits}
    {manifest : List Entry} {projection : Scan.Projection schema.output}
    {trace : Trace schema} {cause : Heterogeneous.Error}
    (read : Heterogeneous.read schema options input manifest = .ok trace)
    (failed : trace.termination = .readError cause) :
    convertProjected schema options input output manifest projection = .error (.source cause) := by
  simp [convertProjected, project_agrees, read, emitTrace, failed, Bind.bind, Except.bind, Except.map,
    Except.mapError]

end Silmaril.Formats.Hive.Manifest.Heterogeneous.ToIpc
