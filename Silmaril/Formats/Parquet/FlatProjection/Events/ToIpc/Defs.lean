module

public import Silmaril.Formats.Parquet.FlatProjection.Events.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Writer.Defs

/-! Native mixed IPC after a successful ordered heterogeneous Parquet read. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc

open Silmaril.Relational
open Arrow.MixedFlat.Timestamp (Field Batch Stream)

inductive Error where
  | source (cause : Events.Error)
  | closed
  | writer (cause : Arrow.MixedFlat.Timestamp.Writer.Error)
  deriving DecidableEq, Repr

def field (name : String) : Kind → Field
  | .int32 nullable => ⟨name, nullable, .int32⟩
  | .utf8 nullable => ⟨name, nullable, .utf8⟩
  | .timestamp kind => ⟨name, kind.nullable, .timestamp kind.metadata⟩

def column : (kind : Kind) → List (Option (Cell kind)) → Arrow.MixedFlat.Timestamp.Column
  | .int32 _, values => .int32 values
  | .utf8 _, values => .utf8 values
  | .timestamp _, values => .timestamp (values.map (Option.map (·.ticks)))

abbrev Schema := Scan.Schema String Kind

def fields (schema : Schema) : List Field :=
  List.ofFn fun i => field (schema.kind i).1 (schema.kind i).2

def batchInput {schema : Schema} (batch : Scan.Columns schema Cell) : Batch :=
  ⟨batch.rowCount, List.ofFn fun i => column (schema.kind i).2 (batch.values i)⟩

def observation {schema : Schema} {ε : Type*} (trace : Arrow.Events.Trace schema Cell ε) : Stream :=
  ⟨fields schema, trace.batches.map batchInput⟩

/-- Observe the terminal source result before any IPC writer admission. -/
def emitTrace (limits : Arrow.ObservationLimits) {schema : Schema}
    (trace : Arrow.Events.Trace schema Cell Events.Error) : Except Error KBytes :=
  match trace.termination with
  | .readError cause | .closeError cause => .error (.source cause)
  | .closed => .error .closed
  | .eos => (Arrow.MixedFlat.Timestamp.Writer.emit limits (observation trace)).mapError .writer

def convert (limits : Limits) (output : Arrow.ObservationLimits) (input : Bytes)
    (ordinals : Array Nat) : Except Error KBytes := do
  let ⟨_, trace⟩ ← (Events.readAll limits input ordinals).mapError .source
  emitTrace output trace

end Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc
