module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.Defs
public import Silmaril.Formats.Arrow.TimestampStream.Ordered.Writer.Defs

/-! Native ordered TIMESTAMP IPC from a fully checked projected source. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

inductive Error where
  | source (cause : Projection.Error)
  | closed
  | writer (cause : Arrow.TimestampStream.Ordered.Writer.Error)
  deriving DecidableEq, Repr

abbrev Schema := Scan.Schema String Events.Kind

def fields (schema : Schema) : List Arrow.TimestampStream.Ordered.Field :=
  List.ofFn (Events.ToIpc.bindingAt schema)

def batchInput {schema : Schema} (batch : Scan.Columns schema Events.Cell) : Arrow.TimestampStream.Ordered.Batch :=
  ⟨batch.rowCount, List.ofFn fun i => (batch.values i).map (Option.map Ticks.ticks)⟩

def observation {schema : Schema} (trace : Arrow.Events.Trace schema Events.Cell Projection.Error) :
    Arrow.TimestampStream.Ordered.Stream :=
  ⟨fields schema, trace.batches.map batchInput⟩

/-- Source termination is checked before inspecting the output limits. -/
def emitTrace (limits : Arrow.ObservationLimits) {schema : Schema}
    (trace : Arrow.Events.Trace schema Events.Cell Projection.Error) : Except Error KBytes :=
  match trace.termination with
  | .readError cause | .closeError cause => .error (.source cause)
  | .closed => .error .closed
  | .eos =>
    let observed := observation trace
    (Arrow.TimestampStream.Ordered.Writer.emit limits observed.fields observed.batches).mapError .writer

def convert (limits : Projection.Limits) (output : Arrow.ObservationLimits) (input : Bytes)
    (ordinals : Array Nat) : Except Error KBytes := do
  let ⟨_, trace⟩ ← (Projection.readAll limits input ordinals).mapError .source
  emitTrace output trace

end Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc
