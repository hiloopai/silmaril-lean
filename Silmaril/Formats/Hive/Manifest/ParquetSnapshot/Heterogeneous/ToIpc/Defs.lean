module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.Defs
public import Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc.Defs

/-! Checked native mixed Arrow IPC for the supplied heterogeneous Hive manifest. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest.Heterogeneous.ToIpc

open Silmaril.Relational
open Parquet.FlatProjection.Events (Cell)
open Parquet.FlatProjection.Events.ToIpc (observation)

inductive Error where
  | source (cause : Heterogeneous.Error)
  | closed
  | writer (cause : Arrow.MixedFlat.Timestamp.Writer.Error)
  deriving Repr

/-- Finish the source before admission to the IPC writer. The Events trace
remains available to callers that need its completed prefix after a failure. -/
def emitTrace (output : Arrow.ObservationLimits) {schema : Scan.Schema String Parquet.FlatProjection.Events.Kind}
    (trace : Arrow.Events.Trace schema Cell Heterogeneous.Error) : Except Error KBytes :=
  match trace.termination with
  | .readError cause | .closeError cause => .error (.source cause)
  | .closed => .error .closed
  | .eos => (Arrow.MixedFlat.Timestamp.Writer.emit output (observation trace)).mapError .writer

/-- Emit the full declared physical and virtual schema, with one RecordBatch
per group in manifest order. An empty manifest still supplies the schema. -/
def convert (schema : Schema) (options : PartitionPath.Options) (input : Parquet.FlatProjection.Events.Limits)
    (output : Arrow.ObservationLimits) (manifest : List Entry) : Except Error KBytes := do
  let trace ← (Heterogeneous.read schema options input manifest).mapError .source
  emitTrace output trace

/-- Use the existing logical projection, including width zero and repeated
positions. All declared source columns still participate in source validation. -/
def convertProjected (schema : Schema) (options : PartitionPath.Options)
    (input : Parquet.FlatProjection.Events.Limits) (output : Arrow.ObservationLimits)
    (manifest : List Entry) (projection : Scan.Projection schema.output) : Except Error KBytes := do
  let trace ← (Heterogeneous.project schema options input manifest projection).mapError .source
  emitTrace output trace

end Silmaril.Formats.Hive.Manifest.Heterogeneous.ToIpc
