module

public import Silmaril.Formats.Parquet.FlatProjection.Defs

/-! Positional selection of completed checked source observations. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatProjection.Composition

open Arrow.MixedFlat

/-- Select positions in order, preserving repeats. An invalid position
refuses the whole selection. -/
def select {α : Type} (positions : List Nat) (values : List α) : Option (List α) :=
  positions.mapM (fun position => values[position]?)

def composeOrdinals (original positions : List Nat) : Option (List Nat) :=
  select positions original

/-- The snapshot and column decoding policies agree. File bytes, total
rows and projection width have separate admission caps. -/
structure SameColumnPolicy (original direct : FlatProjection.Limits) : Prop where
  snapshot : original.column.snapshot = direct.column.snapshot
  page : original.column.column = direct.column.column
  valueBytes : original.column.maxValueBytes = direct.column.maxValueBytes

structure Observation where
  fields : List Arrow.MixedFlat.Field
  batches : List StreamWriter.BatchObservation
  deriving DecidableEq

def observe (checked : Checked) (batches : List OrderedWriter.BatchInput) : Observation :=
  ⟨checked.fields, batches.map OrderedWriter.BatchInput.observe⟩

def projectBatch (positions : List Nat) (batch : StreamWriter.BatchObservation) :
    Option StreamWriter.BatchObservation := do
  let columns ← batch.2
  let selected ← select positions columns
  return (batch.1, some selected)

/-- Select schema and batch columns without changing any original row
counts. An empty selection retains every batch, including zero-row batches. -/
def project (positions : List Nat) (observation : Observation) : Option Observation := do
  let fields ← select positions observation.fields
  let batches ← observation.batches.mapM (projectBatch positions)
  return ⟨fields, batches⟩

end Silmaril.Formats.Parquet.FlatProjection.Composition
