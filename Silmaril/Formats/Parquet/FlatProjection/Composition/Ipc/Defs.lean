module

public import Silmaril.Formats.Parquet.FlatProjection.Composition.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Defs

/-! Positional observations of complete mixed IPC record events. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

open Arrow.MixedFlat

/-- BinaryView observations record the exact octets, independently of
their inline or variadic buffer representation. -/
inductive Cell where
  | primitive (value : Arrow.Value)
  | binaryView (octets : List UInt8)
  | utf8View (value : String)
  deriving DecidableEq

abbrev BatchObservation := Nat × List (List (Option Cell))

structure EventObservation where
  fields : List Field
  batches : List BatchObservation
  deriving DecidableEq

def observeCell : Arrow.MixedFlat.Events.Cell → Cell
  | .primitive value => .primitive value
  | .binaryView bytes => .binaryView bytes.toList
  | .utf8View value => .utf8View value

def observeBatch {schema : Silmaril.Relational.Scan.Schema Field Unit}
    (batch : Arrow.MixedFlat.Events.Batch schema) : BatchObservation :=
  (batch.rowCount, List.ofFn fun i => (batch.values i).map (Option.map observeCell))

/-- Observe a schema and its original record events only after exact EOS. -/
def complete (events : Stream.Events.EventStream) : Option EventObservation := do
  let .ok ⟨schema, trace⟩ := events | none
  let .eos := trace.termination | none
  return ⟨List.ofFn (fun i => (schema.kind i).1), trace.batches.map observeBatch⟩

def readEvents (limits : Arrow.MixedFlat.Limits) (wire : KBytes) : Option EventObservation :=
  complete (Stream.Events.readAll limits wire)

def projectEventBatch (positions : List Nat) (batch : BatchObservation) : Option BatchObservation :=
  (select positions batch.2).map (Prod.mk batch.1)

/-- Select fields and slots in positional order, preserving repetitions
and all original batch row counts. -/
def projectEvents (positions : List Nat) (events : EventObservation) : Option EventObservation := do
  let fields ← select positions events.fields
  let batches ← events.batches.mapM (projectEventBatch positions)
  return ⟨fields, batches⟩

def observeSlots : Writer.ColumnObservation → List (Option Cell)
  | .int32 values => values.map (Option.map Cell.primitive)
  | .binaryView values => values.map (Option.map Cell.binaryView)
  | .utf8View values => values.map (Option.map Cell.utf8View)

def observeSourceBatch (batch : StreamWriter.BatchObservation) : Option BatchObservation :=
  batch.2.map fun columns => (batch.1, columns.map (observeSlots ∘ Prod.snd))

/-- Compare source batches with native events in the same octet model. -/
def observeSource (source : Observation) : Option EventObservation :=
  (source.batches.mapM observeSourceBatch).map (EventObservation.mk source.fields)

end Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc
